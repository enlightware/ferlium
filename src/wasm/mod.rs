// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Wasm32 linkage to the matching Rust runtime instance. Table lookup happens during linking;
//! generated code imports the C entries themselves, not JavaScript or interpreter adapters.

mod runtime;

use js_sys::{Object, Reflect, WebAssembly::Table};
use wasm_bindgen::{JsCast, JsValue};
use wasm_encoder::ValType;

use crate::{
    FxHashMap,
    hir::native_functions::{
        NativeEntry, NativeFailureConvention, NativeParameter, NativeResult, NativeScalar,
        NativeSignature,
    },
    module::FunctionId,
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
        let fallible = signature.failure == NativeFailureConvention::StatusWithState;
        if (fallible
            && matches!(
                signature.result,
                NativeResult::Scalar(..) | NativeResult::Optional { .. }
            ))
            || (!fallible && signature.result == NativeResult::Never)
        {
            return Err(JsValue::from_str(&format!(
                "invalid native result transport for Wasm import {name}"
            )));
        }
        let mut parameters = Vec::new();
        if fallible {
            parameters.push(ValType::I32);
        }
        parameters.extend(
            signature
                .parameters
                .iter()
                .map(|parameter| match parameter {
                    NativeParameter::Scalar(_, scalar) => scalar_type(*scalar),
                    NativeParameter::Shared(_)
                    | NativeParameter::Mutable(_)
                    | NativeParameter::Consuming(_) => ValType::I32,
                }),
        );
        let result = match signature.result {
            NativeResult::Unit | NativeResult::Never => None,
            NativeResult::Scalar(_, scalar) => Some(scalar_type(scalar)),
            NativeResult::Addressor { .. } if !fallible => Some(ValType::I32),
            NativeResult::Output(_) | NativeResult::Addressor { .. } => {
                parameters.push(ValType::I32);
                None
            }
            NativeResult::Optional { .. } => {
                parameters.push(ValType::I32);
                Some(ValType::I32)
            }
        };
        Ok(Self {
            name,
            parameters,
            results: if fallible { Some(ValType::I32) } else { result }
                .into_iter()
                .collect(),
        })
    }
}

fn scalar_type(scalar: NativeScalar) -> ValType {
    match scalar {
        NativeScalar::Bool | NativeScalar::Int => ValType::I32,
        NativeScalar::Float => ValType::F64,
    }
}

/// Import contracts and their instance-local JS bindings. Never persist Rust table indexes;
/// native names retain the program's existing module-qualified function identities instead.
pub struct Imports {
    table: Table,
    namespace: Object,
    object: Object,
    functions: Vec<FunctionImport>,
    natives: FxHashMap<FunctionId, u32>,
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
    pub fn add_native(&mut self, id: FunctionId, entry: &NativeEntry) -> Result<u32, JsValue> {
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

    pub fn functions(&self) -> &[FunctionImport] {
        &self.functions
    }

    pub fn object(&self) -> &Object {
        &self.object
    }

    fn insert(&mut self, import: FunctionImport, address: *const ()) -> Result<u32, JsValue> {
        let name = JsValue::from_str(&import.name);
        if Reflect::has(&self.namespace, &name)? {
            return Err(JsValue::from_str(&format!(
                "duplicate Wasm function import {}",
                import.name
            )));
        }
        // Rust wasm32 function pointers are indexes in this instance's indirect function table.
        // The value returned by get is the Wasm function itself; do not wrap it in a JS closure.
        let function = self.table.get(address as u32)?;
        if !function.is_function() {
            return Err(JsValue::from_str(&format!(
                "missing Wasm C entry {}",
                import.name
            )));
        }
        Reflect::set(&self.namespace, &name, &function)?;
        let index = self.functions.len() as u32;
        self.functions.push(import);
        Ok(index)
    }
}

#[cfg(test)]
mod tests;
