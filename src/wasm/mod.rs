// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Wasm32 linkage to the matching Rust runtime instance. Table lookup happens during linking;
//! generated code imports the C entries themselves, not JavaScript or interpreter adapters.
//! Hosts must link with `--growable-table` to bind generated entries into Rust's function table.
//! This backend is wasm32-specific: pointers and Ferlium's target-sized `int` use i32. Wasm64
//! needs coordinated changes to transport, addressing, memory declarations and invocation state.

mod abi;
mod boxed;
mod callable_environment;
mod emit;
mod evidence;
mod execution;
mod failure;
mod runtime;
#[cfg(feature = "wasm-text")]
pub(crate) mod text;

pub use abi::WasmFunctionId;
pub use execution::{
    BoundFunction, CompiledProgram, Instance, WasmArguments, WasmLimits, WasmValue, run_boxed_entry,
};

use js_sys::{Object, Reflect, WebAssembly::Table};
use wasm_bindgen::{JsCast, JsValue};
use wasm_encoder::ValType;

use self::abi::{CallAbi, HostTableSlotId};

use crate::{
    FxHashMap,
    hir::native_functions::{NativeEntry, NativeSignature},
    module::{FunctionId, id::Id},
};

pub const IMPORT_MODULE: &str = "ferlium";
pub const MEMORY_IMPORT: &str = "memory";

/// One core-Wasm function import; its position in `Imports::functions` is its function index.
pub struct FunctionImport {
    pub name: String,
    pub parameters: Vec<ValType>,
    pub results: Vec<ValType>,
}

impl FunctionImport {
    // Keep this mapping consistent with the rustc ABI probes in tests/native_abi/check_wasm.py.
    fn native(name: String, signature: &NativeSignature) -> Result<Self, JsValue> {
        let abi = CallAbi::native(signature)
            .map_err(|reason| JsValue::from_str(&format!("{reason} for Wasm import {name}")))?;
        Ok(Self {
            name,
            parameters: abi.params(),
            results: abi.results().into_iter().collect(),
        })
    }
}

/// Import contracts and their instance-local JS bindings. Never persist Rust table indexes;
/// native names retain the program's existing module-qualified function identities instead.
pub struct Imports {
    table: Table,
    namespace: Object,
    object: Object,
    functions: Vec<FunctionImport>,
    natives: FxHashMap<FunctionId, WasmFunctionId>,
}

impl Imports {
    /// Bind the current Rust instance's memory and raw allocation services.
    pub fn new() -> Result<Self, JsValue> {
        let namespace = Object::new();
        Reflect::set(&namespace, &MEMORY_IMPORT.into(), &wasm_bindgen::memory())?;
        let object = Object::new();
        Reflect::set(&object, &IMPORT_MODULE.into(), &namespace)?;
        let mut imports = Self {
            table: wasm_bindgen::function_table().dyn_into()?,
            namespace,
            object,
            functions: Vec::new(),
            natives: FxHashMap::default(),
        };
        for (name, address, parameters, results) in [
            (
                "alloc",
                runtime::allocate as *const (),
                vec![ValType::I32; 2],
                vec![ValType::I32],
            ),
            (
                "realloc",
                runtime::reallocate as *const (),
                vec![ValType::I32; 3],
                vec![ValType::I32],
            ),
            (
                "dealloc",
                runtime::release as *const (),
                vec![ValType::I32],
                vec![],
            ),
            (
                "string_matches",
                runtime::string_matches as *const (),
                vec![ValType::I32; 2],
                vec![ValType::I32],
            ),
            (
                "capture_failure",
                failure::capture as *const (),
                vec![ValType::I32; 2],
                vec![ValType::I32],
            ),
            (
                "propagate_failure",
                failure::propagate as *const (),
                vec![ValType::I32; 2],
                vec![ValType::I32],
            ),
            (
                "retain_evidence",
                evidence::retain as *const (),
                vec![ValType::I32],
                vec![],
            ),
            (
                "release_evidence",
                evidence::release as *const (),
                vec![ValType::I32; 2],
                vec![],
            ),
            (
                "build_evidence",
                evidence::build as *const (),
                vec![ValType::I32; 4],
                vec![],
            ),
            (
                "allocate_callable_environment",
                callable_environment::allocate as *const (),
                vec![ValType::I32; 4],
                vec![ValType::I32],
            ),
            (
                "copy_callable_environment",
                callable_environment::copy_shell as *const (),
                vec![ValType::I32],
                vec![ValType::I32],
            ),
            (
                "materialize_subscript_environment",
                callable_environment::materialize_subscript as *const (),
                vec![ValType::I32; 2],
                vec![ValType::I32],
            ),
            (
                "release_callable_environment",
                callable_environment::release as *const (),
                vec![ValType::I32; 2],
                vec![],
            ),
        ] {
            imports.insert(
                FunctionImport {
                    name: name.into(),
                    parameters,
                    results,
                },
                address,
            )?;
        }
        Ok(imports)
    }

    /// Bind a registered C entry, reusing its imported function index on subsequent references.
    pub fn add_native(
        &mut self,
        id: FunctionId,
        entry: &NativeEntry,
    ) -> Result<WasmFunctionId, JsValue> {
        if let Some(&index) = self.natives.get(&id) {
            return Ok(index);
        }
        let name = format!("m{}_f{}", id.module.as_u32(), id.function.as_u32());
        let index = self.insert(
            FunctionImport::native(name, entry.signature())?,
            entry.address(),
        )?;
        self.natives.insert(id, index);
        Ok(index)
    }

    pub(super) fn function_index(&self, name: &str) -> WasmFunctionId {
        WasmFunctionId::from_index(
            self.functions
                .iter()
                .position(|function| function.name == name)
                .expect("runtime import"),
        )
    }

    pub fn functions(&self) -> &[FunctionImport] {
        &self.functions
    }

    pub fn object(&self) -> &Object {
        &self.object
    }

    fn insert(
        &mut self,
        import: FunctionImport,
        address: *const (),
    ) -> Result<WasmFunctionId, JsValue> {
        let name = JsValue::from_str(&import.name);
        if Reflect::has(&self.namespace, &name)? {
            return Err(JsValue::from_str(&format!(
                "duplicate Wasm function import {}",
                import.name
            )));
        }
        // Rust wasm32 function pointers are indexes in this instance's indirect function table.
        // The value returned by get is the Wasm function itself; do not wrap it in a JS closure.
        let slot = HostTableSlotId::from_index(address as usize);
        let function = self.table.get(slot.as_u32())?;
        if !function.is_function() {
            return Err(JsValue::from_str(&format!(
                "missing Wasm C entry {}",
                import.name
            )));
        }
        Reflect::set(&self.namespace, &name, &function)?;
        let index = WasmFunctionId::from_index(self.functions.len());
        self.functions.push(import);
        Ok(index)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod codegen_tests;
