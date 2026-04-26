// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

pub mod effects;
pub mod mutability;
pub mod r#trait;
pub mod trait_solver;
pub mod r#type;
pub mod type_scheme;
pub mod typing_env;

pub(crate) mod coherence;
pub(crate) mod never;
pub(crate) mod type_constraints;
pub(crate) mod type_inference;
pub(crate) mod type_like;
pub(crate) mod type_mapper;
pub(crate) mod type_substitution;
pub(crate) mod type_visitor;
