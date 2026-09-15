// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Use directives

use crate::FxHashMap;

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
    pub explicits: FxHashMap<Ustr, UseData>,
    pub wildcards: Vec<UseData>,
}

impl Uses {
    pub fn new_with_std() -> Self {
        Self::new(
            FxHashMap::default(),
            vec![UseData::new(
                Path::single_str("std"),
                Location::new_synthesized(),
            )],
        )
    }
}

impl Default for Uses {
    fn default() -> Self {
        Self::new(FxHashMap::default(), vec![])
    }
}
