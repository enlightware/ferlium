// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Executable linkage probes, not a Ferlium emitter. Keep native calls inside the generated module.

use std::{cell::Cell, mem::MaybeUninit, ptr, rc::Rc};

use js_sys::{Array, Function as JsFunction, Object, Reflect, Uint8Array, WebAssembly};
use wasm_bindgen::{JsCast, JsValue};
use wasm_bindgen_test::wasm_bindgen_test;
use wasm_encoder::{
    CodeSection, EntityType, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    Instruction, MemArg, MemoryType, Module as WasmModule, TypeSection, ValType,
};

use crate::{
    CompilerSession, FxHashMap,
    compiler::error::SourceFailureKind,
    hir::{
        native_functions::{
            NativeAddressorMut, NativeDropFn, NativeFailureConvention, NativeFailureState,
            NativeFallibleAddressorMut, NativeFallibleFnN, NativeFallibleOutFnN,
            NativeFallibleOutFnRN, NativeFnMN, NativeFnN, NativeFnNN, NativeFnR, NativeFnRN,
            NativeOptionalFnN, NativeOutFnR,
        },
        value::NativeValueType,
    },
    module::{FunctionId, LocalFunctionId, Module, ModuleId, Path, id::Id},
    std::{
        math::{Float, int_type},
        option::option_type,
    },
    types::effects::{PrimitiveEffect, effect, no_effects},
    ustr,
};

use super::{
    FunctionImport, IMPORT_MODULE, Imports, MEMORY_IMPORT, WasmFunctionId, abi::WasmTypeId,
};

struct ProbeFunction {
    name: String,
    parameters: Vec<ValType>,
    results: Vec<ValType>,
    body: Function,
}

struct Probe {
    imports: Imports,
    functions: Vec<ProbeFunction>,
}

impl Probe {
    fn new() -> Self {
        Self {
            imports: Imports::new().unwrap(),
            functions: Vec::new(),
        }
    }

    fn native(&mut self, module: &Module, name: &str) -> WasmFunctionId {
        let local = module.get_local_function_id(ustr(name)).unwrap();
        let entry = module
            .get_function_by_id(local)
            .unwrap()
            .code
            .native_entry()
            .unwrap();
        let index = self
            .imports
            .add_native(FunctionId::new(module.module_id(), local), entry)
            .unwrap();
        self.forward(name, index);
        index
    }

    fn forward(&mut self, name: &str, index: WasmFunctionId) {
        let import = &self.imports.functions()[index.as_index()];
        let mut body = Function::new([]);
        for parameter in 0..import.parameters.len() as u32 {
            body.instruction(&Instruction::LocalGet(parameter));
        }
        body.instruction(&Instruction::Call(index.as_u32()));
        body.instruction(&Instruction::End);
        self.functions.push(ProbeFunction {
            name: name.into(),
            parameters: import.parameters.clone(),
            results: import.results.clone(),
            body,
        });
    }

    fn instantiate(self) -> Result<WebAssembly::Instance, JsValue> {
        let mut types = TypeSection::new();
        let mut imports = ImportSection::new();
        imports.import(
            IMPORT_MODULE,
            MEMORY_IMPORT,
            MemoryType {
                minimum: 0,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            },
        );
        for function in self.imports.functions() {
            let type_index = WasmTypeId::new(types.len());
            types.ty().function(
                function.parameters.iter().copied(),
                function.results.iter().copied(),
            );
            imports.import(
                IMPORT_MODULE,
                &function.name,
                EntityType::Function(type_index.as_u32()),
            );
        }
        let mut functions = FunctionSection::new();
        let mut exports = ExportSection::new();
        let mut code = CodeSection::new();
        exports.export("memory", ExportKind::Memory, 0);
        let imported_functions = self.imports.functions().len();
        for (index, function) in self.functions.into_iter().enumerate() {
            let type_index = WasmTypeId::new(types.len());
            let function_index = WasmFunctionId::from_index(imported_functions + index);
            functions.function(type_index.as_u32());
            exports.export(&function.name, ExportKind::Func, function_index.as_u32());
            types.ty().function(function.parameters, function.results);
            code.function(&function.body);
        }
        let mut module = WasmModule::new();
        module
            .section(&types)
            .section(&imports)
            .section(&functions)
            .section(&exports)
            .section(&code);
        let bytes = Uint8Array::from(module.finish().as_slice());
        let module = WebAssembly::Module::new(&bytes).unwrap();
        WebAssembly::Instance::new(&module, self.imports.object())
    }
}

fn call(instance: &WebAssembly::Instance, name: &str, args: &[f64]) -> JsValue {
    let function: JsFunction = Reflect::get(&instance.exports(), &name.into())
        .unwrap()
        .dyn_into()
        .unwrap();
    let arguments = args
        .iter()
        .copied()
        .map(JsValue::from_f64)
        .collect::<Array>();
    function.apply(&JsValue::UNDEFINED, &arguments).unwrap()
}

fn number(instance: &WebAssembly::Instance, name: &str, args: &[f64]) -> f64 {
    call(instance, name, args).as_f64().unwrap()
}

#[derive(Debug, Clone)]
struct Owned {
    text: String,
    counter: isize,
    drops: Rc<Cell<usize>>,
}
impl NativeValueType for Owned {}
impl Drop for Owned {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

unsafe extern "C" fn member(receiver: *mut Owned) -> *mut isize {
    // SAFETY: the entry receives an exclusively borrowed, live receiver; its integer field
    // remains live and permits arbitrary integer replacement for the duration of that borrow.
    unsafe { ptr::addr_of_mut!((*receiver).counter) }
}

unsafe extern "C" fn fallible_member(
    failure: &mut NativeFailureState,
    receiver: *mut Owned,
    output: &mut MaybeUninit<*mut isize>,
) -> u32 {
    // SAFETY: the registered entry receives a live receiver for the whole call.
    unsafe {
        let receiver = &mut *receiver;
        if receiver.text.is_empty() {
            failure.fail(SourceFailureKind::InvalidArgument("empty receiver".into()))
        } else {
            output.write(member(receiver));
            0
        }
    }
}

fn fixtures() -> Module {
    let mut module = Module::new(ModuleId::new(1), Path::single_str("linkage"));
    module.add_function(
        ustr("add"),
        NativeFnNN::from_rust(|a: isize, b: isize| a.wrapping_add(b)).description(
            ["a", "b"],
            "",
            no_effects(),
        ),
    );
    module.add_function(
        ustr("float"),
        NativeFnN::from_rust(|x: Float| Float::new_saturating(x.into_inner() + 0.5)).description(
            ["x"],
            "",
            no_effects(),
        ),
    );
    module.add_function(
        ustr("boolean"),
        NativeFnN::from_rust(|x: bool| !x).description(["x"], "", no_effects()),
    );
    module.add_function(
        ustr("length"),
        NativeFnR::from_rust(|x: &Owned| x.text.len() as isize).description(
            ["x"],
            "",
            no_effects(),
        ),
    );
    module.add_function(
        ustr("clone"),
        NativeOutFnR::from_rust(Owned::clone).description(["x"], "", no_effects()),
    );
    module.add_function(
        ustr("mutate"),
        NativeFnMN::from_rust(|x: &mut Owned, n: isize| {
            x.counter = n;
            x.text.push('!');
        })
        .description(["x", "n"], "", no_effects()),
    );
    unsafe extern "C" fn destroy(x: *mut Owned) {
        // SAFETY: the consuming entry receives a live, uniquely owned value and destroys it once.
        unsafe { ptr::drop_in_place(x) };
    }
    // SAFETY: destroy consumes exactly one value without freeing its outer storage.
    module.add_function(
        ustr("drop"),
        unsafe { NativeDropFn::new(destroy) }.description(["x"], "", no_effects()),
    );
    module.add_function(
        ustr("fallible_clone"),
        NativeFallibleOutFnRN::from_rust(|x: &Owned, ok: bool| {
            if ok {
                Ok(x.clone())
            } else {
                Err(SourceFailureKind::Aborted(None))
            }
        })
        .description(["x", "ok"], "", effect(PrimitiveEffect::Fallible)),
    );
    module.add_function(
        ustr("unit"),
        NativeFnRN::from_rust(|x: &(), n: isize| {
            let () = x;
            n
        })
        .description(["x", "n"], "", no_effects()),
    );
    module.add_function(
        ustr("fallible"),
        NativeFallibleOutFnN::from_rust(|n: isize| {
            if n == 0 {
                Err(SourceFailureKind::DivisionByZero)
            } else {
                Ok(100 / n)
            }
        })
        .description(["n"], "", effect(PrimitiveEffect::Fallible)),
    );
    module.add_function(
        ustr("fallible_unit"),
        NativeFallibleFnN::from_rust(|ok: bool| {
            if ok {
                Ok(())
            } else {
                Err(SourceFailureKind::Aborted(None))
            }
        })
        .description(["ok"], "", effect(PrimitiveEffect::Fallible)),
    );
    module.add_function(
        ustr("never"),
        NativeFallibleFnN::from_rust_never(|_: isize| Err(SourceFailureKind::Aborted(None)))
            .description(["x"], "", effect(PrimitiveEffect::Fallible)),
    );
    module.add_function(
        ustr("optional"),
        NativeOptionalFnN::from_rust(|n: isize| (n >= 0).then_some(n), option_type(int_type()))
            .description(["n"], "", no_effects()),
    );
    // SAFETY: both entries return a stable native member rooted in the exclusively borrowed owner.
    module.add_function(
        ustr("member"),
        unsafe { NativeAddressorMut::new(member) }.description(["x"], "", no_effects()),
    );
    module.add_function(
        ustr("fallible_member"),
        unsafe { NativeFallibleAddressorMut::new(fallible_member) }.description(
            ["x"],
            "",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    for function in module.iter_functions() {
        function
            .code
            .native_entry()
            .unwrap()
            .signature()
            .validate(&function.definition)
            .unwrap();
    }
    module
}

#[wasm_bindgen_test]
fn wasm_linkage_all_std_native_signatures() {
    let session = CompilerSession::new();
    let module = session.std_module();
    let mut probe = Probe::new();
    let mut count = 0;
    for (index, function) in module.iter_functions().enumerate() {
        if let Some(entry) = function.code.native_entry() {
            entry.signature().validate(&function.definition).unwrap();
            let id = FunctionId::new(module.module_id(), LocalFunctionId::from_index(index));
            let imported = probe.imports.add_native(id, entry).unwrap();
            let import_count = probe.imports.functions().len();
            assert_eq!(probe.imports.add_native(id, entry).unwrap(), imported);
            assert_eq!(probe.imports.functions().len(), import_count);
            count += 1;
        }
    }
    assert!(
        count > 100,
        "the std native catalog must actually be exercised"
    );
    probe.instantiate().unwrap(); // The engine checks every C-entry type, including uncalled imports.
}

#[wasm_bindgen_test]
fn wasm_linkage_rejects_mismatched_native_import() {
    let module = fixtures();
    for name in ["add", "fallible"] {
        let mut probe = Probe::new();
        let index = probe.native(&module, name);
        let signature = &mut probe.imports.functions[index.as_index()];
        if name == "add" {
            signature.results = vec![ValType::F64];
        } else {
            signature.parameters.pop(); // Missing fallible result out-pointer.
        }
        probe.functions.clear();
        let error = probe.instantiate().unwrap_err();
        assert!(error.is_instance_of::<WebAssembly::LinkError>());
    }
    // A JavaScript forwarding wrapper would accept either signature. This proves we imported
    // the typed Wasm function itself, so mismatches fail before any guest code can run.
}

#[wasm_bindgen_test]
fn wasm_linkage_rejects_invalid_result_transport() {
    let module = fixtures();
    for name in ["add", "optional", "never"] {
        let local = module.get_local_function_id(ustr(name)).unwrap();
        let mut signature = module
            .get_function_by_id(local)
            .unwrap()
            .code
            .native_entry()
            .unwrap()
            .signature()
            .clone();
        signature.failure = if name == "never" {
            NativeFailureConvention::Infallible
        } else {
            NativeFailureConvention::StatusWithState
        };
        let error = FunctionImport::native(name.into(), &signature)
            .err()
            .unwrap();
        assert!(
            error
                .as_string()
                .unwrap()
                .contains("invalid native result transport")
        );
    }
}

#[wasm_bindgen_test]
fn wasm_linkage_native_execution() {
    let module = fixtures();
    let mut probe = Probe::new();
    let mut entries = FxHashMap::default();
    for name in [
        "add",
        "float",
        "boolean",
        "length",
        "clone",
        "mutate",
        "drop",
        "fallible_clone",
        "unit",
        "fallible",
        "fallible_unit",
        "never",
        "optional",
        "member",
        "fallible_member",
    ] {
        entries.insert(name, probe.native(&module, name));
    }
    // Exercise allocation, managed output, borrowing and destruction in a single generated call.
    let mut body = Function::new([(2, ValType::I32)]);
    body.instruction(&Instruction::I32Const(size_of::<Owned>() as i32))
        .instruction(&Instruction::I32Const(align_of::<Owned>() as i32))
        .instruction(&Instruction::Call(
            probe.imports.function_index("alloc").as_u32(),
        ))
        .instruction(&Instruction::LocalSet(1))
        .instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::LocalGet(1))
        .instruction(&Instruction::Call(entries["clone"].as_u32()))
        .instruction(&Instruction::LocalGet(1))
        .instruction(&Instruction::Call(entries["length"].as_u32()))
        .instruction(&Instruction::LocalSet(2))
        .instruction(&Instruction::LocalGet(1))
        .instruction(&Instruction::Call(entries["drop"].as_u32()))
        .instruction(&Instruction::LocalGet(1))
        .instruction(&Instruction::Call(
            probe.imports.function_index("dealloc").as_u32(),
        ))
        .instruction(&Instruction::LocalGet(2))
        .instruction(&Instruction::End);
    probe.functions.push(ProbeFunction {
        name: "clone_and_measure".into(),
        parameters: vec![ValType::I32],
        results: vec![ValType::I32],
        body,
    });
    let instance = probe.instantiate().unwrap();
    assert_eq!(
        number(&instance, "add", &[isize::MAX as f64, 1.0]),
        isize::MIN as f64
    );
    assert_eq!(number(&instance, "float", &[2.0]), 2.5);
    assert_eq!(number(&instance, "boolean", &[0.0]), 1.0);
    assert_eq!(number(&instance, "boolean", &[1.0]), 0.0);
    assert_eq!(
        number(&instance, "unit", &[&() as *const () as u32 as f64, 42.0]),
        42.0
    );

    let drops = Rc::new(Cell::new(0));
    let mut owner = Owned {
        text: "native storage".into(),
        counter: 0,
        drops: drops.clone(),
    };
    let owner_ptr = &mut owner as *mut Owned as u32 as f64;
    assert_eq!(
        number(&instance, "length", &[owner_ptr]),
        owner.text.len() as f64
    );
    let mut output = MaybeUninit::<Owned>::uninit();
    call(
        &instance,
        "clone",
        &[owner_ptr, output.as_mut_ptr() as u32 as f64],
    );
    // SAFETY: the infallible registered clone initialized the output exactly once.
    let cloned = unsafe { output.assume_init() };
    assert_eq!(cloned.text, owner.text);
    assert_ne!(cloned.text.as_ptr(), owner.text.as_ptr());
    drop(cloned);
    assert_eq!(drops.get(), 1);
    call(&instance, "mutate", &[owner_ptr, 42.0]);
    assert_eq!(owner.counter, 42);
    assert_eq!(owner.text, "native storage!");
    assert_eq!(
        number(&instance, "member", &[owner_ptr]) as u32,
        ptr::addr_of_mut!(owner.counter) as u32
    );

    let mut failure = NativeFailureState::default();
    let failure_ptr = &mut failure as *mut NativeFailureState as u32 as f64;
    let mut scalar = MaybeUninit::new(123_isize);
    let scalar_ptr = scalar.as_mut_ptr() as u32 as f64;
    assert_ne!(
        number(&instance, "fallible", &[failure_ptr, 0.0, scalar_ptr]),
        0.0
    );
    // SAFETY: failure leaves the preinitialized sentinel unchanged.
    assert_eq!(unsafe { scalar.assume_init() }, 123);
    assert_eq!(failure.take(), Some(SourceFailureKind::DivisionByZero));
    assert_eq!(
        number(&instance, "fallible", &[failure_ptr, 4.0, scalar_ptr]),
        0.0
    );
    // SAFETY: success initializes the scalar result.
    assert_eq!(unsafe { scalar.assume_init() }, 25);
    assert!(failure.is_empty());
    assert_eq!(number(&instance, "optional", &[-1.0, scalar_ptr]), 0.0);
    // SAFETY: absence preserves the prior scalar bits.
    assert_eq!(unsafe { scalar.assume_init() }, 25);
    assert_eq!(number(&instance, "optional", &[19.0, scalar_ptr]), 1.0);
    // SAFETY: presence initializes the scalar result.
    assert_eq!(unsafe { scalar.assume_init() }, 19);
    assert_ne!(number(&instance, "fallible_unit", &[failure_ptr, 0.0]), 0.0);
    assert_eq!(failure.take(), Some(SourceFailureKind::Aborted(None)));
    assert_eq!(number(&instance, "fallible_unit", &[failure_ptr, 1.0]), 0.0);
    assert_ne!(number(&instance, "never", &[failure_ptr, 42.0]), 0.0);
    assert_eq!(failure.take(), Some(SourceFailureKind::Aborted(None)));

    let mut managed = MaybeUninit::<Owned>::uninit();
    let managed_ptr = managed.as_mut_ptr() as u32 as f64;
    assert_ne!(
        number(
            &instance,
            "fallible_clone",
            &[failure_ptr, owner_ptr, 0.0, managed_ptr]
        ),
        0.0
    );
    assert_eq!(failure.take(), Some(SourceFailureKind::Aborted(None)));
    assert_eq!(drops.get(), 1);
    assert_eq!(
        number(
            &instance,
            "fallible_clone",
            &[failure_ptr, owner_ptr, 1.0, managed_ptr]
        ),
        0.0
    );
    // SAFETY: success initialized managed; it remains alive until the consuming call below.
    assert_eq!(unsafe { &managed.assume_init_ref().text }, &owner.text);
    call(&instance, "drop", &[managed_ptr]);
    assert_eq!(drops.get(), 2);

    assert_eq!(
        number(&instance, "clone_and_measure", &[owner_ptr]),
        owner.text.len() as f64
    );
    assert_eq!(drops.get(), 3);
    assert_eq!(Rc::strong_count(&drops), 2);

    let mut address = MaybeUninit::<*mut isize>::uninit();
    let address_ptr = address.as_mut_ptr() as u32 as f64;
    assert_eq!(
        number(
            &instance,
            "fallible_member",
            &[failure_ptr, owner_ptr, address_ptr]
        ),
        0.0
    );
    // SAFETY: success wrote the rooted member pointer, whose receiver is still alive.
    assert_eq!(
        unsafe { address.assume_init() },
        ptr::addr_of_mut!(owner.counter)
    );
    owner.text.clear();
    address.write(ptr::null_mut());
    assert_ne!(
        number(
            &instance,
            "fallible_member",
            &[failure_ptr, owner_ptr, address_ptr]
        ),
        0.0
    );
    // SAFETY: failure leaves the null sentinel unchanged.
    assert!(unsafe { address.assume_init() }.is_null());
    assert!(matches!(
        failure.take(),
        Some(SourceFailureKind::InvalidArgument(_))
    ));
    drop(owner);
    assert_eq!(drops.get(), 4);
}

#[wasm_bindgen_test]
fn wasm_linkage_allocation_and_memory_growth() {
    let mut probe = Probe::new();
    for name in ["alloc", "realloc", "dealloc"] {
        probe.forward(name, probe.imports.function_index(name));
    }
    let memarg = MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    };
    let mut body = Function::new([]);
    body.instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::LocalGet(1))
        .instruction(&Instruction::I32Store(memarg))
        .instruction(&Instruction::LocalGet(0))
        .instruction(&Instruction::I32Load(memarg))
        .instruction(&Instruction::End);
    probe.functions.push(ProbeFunction {
        name: "write_read".into(),
        parameters: vec![ValType::I32; 2],
        results: vec![ValType::I32],
        body,
    });
    let instance = probe.instantiate().unwrap();
    let memory: WebAssembly::Memory = Reflect::get(&instance.exports(), &"memory".into())
        .unwrap()
        .dyn_into()
        .unwrap();
    assert!(Object::is(memory.as_ref(), &wasm_bindgen::memory()));
    let allocation = number(&instance, "alloc", &[4.0, 64.0]);
    assert_eq!(allocation as usize % 64, 0);
    assert_eq!(
        number(&instance, "write_read", &[allocation, 1234.0]),
        1234.0
    );
    // SAFETY: the generated module just initialized a live, aligned allocation in our memory.
    assert_eq!(unsafe { (allocation as usize as *const i32).read() }, 1234);
    let allocation = number(&instance, "realloc", &[allocation, 128.0, 256.0]);
    assert_eq!(allocation as usize % 256, 0);
    // SAFETY: realloc preserves the first four bytes and their ownership.
    assert_eq!(unsafe { (allocation as usize as *const i32).read() }, 1234);
    let before = Uint8Array::new(&memory.buffer()).length();
    let large = number(&instance, "alloc", &[before as f64 + 65536.0, 16.0]);
    assert!(Uint8Array::new(&memory.buffer()).length() > before);
    assert_eq!(number(&instance, "write_read", &[large, 5678.0]), 5678.0);
    assert_eq!(number(&instance, "write_read", &[allocation, 42.0]), 42.0);
    call(&instance, "dealloc", &[large]);
    call(&instance, "dealloc", &[allocation]);
    let a = number(&instance, "alloc", &[0.0, 128.0]);
    let b = number(&instance, "alloc", &[0.0, 128.0]);
    assert_ne!(a, b);
    assert_eq!(a as usize % 128, 0);
    call(&instance, "dealloc", &[a]);
    call(&instance, "dealloc", &[b]);
}
