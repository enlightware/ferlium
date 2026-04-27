// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
use enum_as_inner::EnumAsInner;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

use super::diagnostics::ErrorData;

/// The content of an execution error in the IDE
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
#[derive(Debug, Clone, new)]
pub struct ExecutionErrorData {
    pub summary: String,
    pub complete: String,
    pub data: Option<ErrorData>,
}

#[derive(Debug, Clone, EnumAsInner)]
pub enum ExecutionResultInner {
    Success(String),
    Error(ExecutionErrorData),
}

/// The result of executing an expression in the IDE
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct ExecutionResult(ExecutionResultInner);

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl ExecutionResult {
    pub fn html_message(&self) -> String {
        use ExecutionResultInner::*;
        match &self.0 {
            Success(output) => html_escape::encode_text(&output).to_string(),
            Error(data) => {
                format!(
                    "<span class=\"error\">{}</span>",
                    html_escape::encode_text(&data.complete)
                )
            }
        }
    }

    pub fn error_content(&self) -> Option<ExecutionErrorData> {
        self.0.as_error().cloned()
    }

    pub fn error_data(&self) -> Option<ErrorData> {
        self.0.as_error().and_then(|data| data.data.clone())
    }
}

impl ExecutionResult {
    pub fn success(output: String) -> Self {
        Self(ExecutionResultInner::Success(output))
    }

    pub fn error(data: ExecutionErrorData) -> Self {
        Self(ExecutionResultInner::Error(data))
    }
}
