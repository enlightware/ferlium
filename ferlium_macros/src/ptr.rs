// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

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
