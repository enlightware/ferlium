// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::rc::Rc;

use crate::module::Module;
use crate::module::id::NamedIndexed;
use crate::module::path::Path;

use super::ModuleId;

/// Arc-wrapped module bundle for sharing between threads
pub type ModuleRc = Rc<Module>;

/// A set of modules indexed both by name (Path) and by numeric ID (ModuleId).
/// This is the canonical way to hold a collection of modules in a compilation session.
pub type Modules = NamedIndexed<Path, ModuleId, ModuleRc>;
