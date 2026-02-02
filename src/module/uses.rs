// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Use directives

use derive_new::new;
use enum_as_inner::EnumAsInner;
use ustr::Ustr;

use crate::module::path::Path;

#[derive(Debug, Clone, new)]
pub struct UseSome {
    pub module: Path,
    pub symbols: Vec<Ustr>,
}

/// A use directive
#[derive(Debug, Clone, EnumAsInner)]
pub enum Use {
    /// Use all symbols from a module
    All(Path),
    /// Use only some symbols from a module
    Some(UseSome),
}

pub type Uses = Vec<Use>;
