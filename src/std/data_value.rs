// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    module::{Module, TypeDefId},
    std::{STD_MODULE_ID, string::string_type},
    types::r#type::Type,
};
use std::sync::OnceLock;
use ustr::ustr;

static DATA_VALUE_TYPE_DEF: OnceLock<TypeDefId> = OnceLock::new();

pub fn set_data_value_type_def(type_def: TypeDefId) {
    assert_eq!(type_def.module, STD_MODULE_ID);
    if let Err(existing) = DATA_VALUE_TYPE_DEF.set(type_def) {
        assert_eq!(existing, type_def);
    }
}

pub fn find_data_value_type_def(module: &Module) -> TypeDefId {
    module
        .get_type_def_id(ustr("DataValue"))
        .expect("std module must define DataValue before registering serialization")
}

pub fn data_value_type_def() -> TypeDefId {
    *DATA_VALUE_TYPE_DEF
        .get()
        .expect("std DataValue type must be registered before use")
}

pub fn data_value_type() -> Type {
    Type::named(data_value_type_def(), [])
}

pub fn data_value_record_entry_type() -> Type {
    Type::tuple([string_type(), data_value_type()])
}

pub fn data_value_map_entry_type() -> Type {
    Type::tuple([data_value_type(), data_value_type()])
}
