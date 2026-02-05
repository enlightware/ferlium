// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

// Exactly one Ferlium ABI feature must be enabled: ferlium_abi_32 or ferlium_abi_64.

// Both enabled → error.
#[cfg(all(feature = "ferlium_abi_32", feature = "ferlium_abi_64"))]
compile_error!(
    "Multiple Ferlium ABI features enabled; pick exactly one of: ferlium_abi_32 or ferlium_abi_64."
);

// Neither enabled → error.
#[cfg(not(any(feature = "ferlium_abi_32", feature = "ferlium_abi_64")))]
compile_error!("You must enable exactly one of: ferlium_abi_32 or ferlium_abi_64 for Ferlium ABI.");

// Pointer alignment / size *according to Ferlium ABI*, not Rust host.
#[cfg(feature = "ferlium_abi_32")]
pub const FERLIUM_PTR_SIZE: u8 = 4;

#[cfg(feature = "ferlium_abi_64")]
pub const FERLIUM_PTR_SIZE: u8 = 8;
