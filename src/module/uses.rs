// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Use directives

use std::collections::HashMap;

use derive_new::new;
use ustr::Ustr;

use crate::{Location, module::path::Path};

#[derive(Debug, Clone, new)]
pub struct UseData {
    pub module: Path,
    pub span: Location,
}

/// Use directives of a module, separated into explicit and wildcard uses
#[derive(Debug, Clone, new)]
pub struct Uses {
    pub explicits: HashMap<Ustr, UseData>,
    pub wildcards: Vec<UseData>,
}
impl Default for Uses {
    fn default() -> Self {
        Self::new(HashMap::new(), vec![])
    }
}
