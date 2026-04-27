// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::ops::Deref;

use crate::types::effects::EffType;

use super::{CompilationError, CompilationErrorImpl, MutabilityMustBeWhat};

impl CompilationError {
    pub fn expect_name_defined_multiple_times(&self, name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            NameDefinedMultipleTimes { name: n, .. } => {
                if *n == name {
                    return;
                }
                panic!(
                    "expect_name_defined_multiple_times failed: expected \"{}\", got \"{}\"",
                    name, n
                );
            }
            _ => panic!(
                "expect_name_defined_multiple_times called on non-NameDefinedMultipleTimes error {self:?}"
            ),
        }
    }

    pub fn expect_wrong_number_of_arguments(&self, expected: usize, got: usize) {
        use CompilationErrorImpl::*;
        match self.deref() {
            WrongNumberOfArguments {
                expected: exp,
                got: g,
                ..
            } => {
                if exp == &expected && g == &got {
                    return;
                }
                panic!(
                    "expect_wrong_number_of_arguments failed: expected {} != {}, got {} != {}",
                    exp, g, expected, got
                );
            }
            _ => panic!(
                "expect_wrong_number_of_arguments called on non-WrongNumberOfArguments error {self:?}"
            ),
        }
    }

    pub fn expect_mutability_must_be(&self, should_be: MutabilityMustBeWhat) {
        let is_what = self
            .as_mutability_must_be()
            .unwrap_or_else(|| {
                panic!("expect_mutability_must_be called on non-MutabilityMustBe error {self:?}")
            })
            .2;
        if *is_what != should_be {
            panic!(
                "expect_mutability_must_be failed: expected {:?}, got {:?}",
                should_be, is_what
            );
        }
    }

    pub fn expect_type_mismatch(&self, cur_ty: &str, exp_ty: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            TypeMismatch {
                current_ty,
                expected_ty,
                ..
            } => {
                if current_ty == cur_ty && expected_ty == exp_ty {
                    return;
                }
                let expected = alpha_normalize_type_strings([cur_ty, exp_ty]);
                let actual =
                    alpha_normalize_type_strings([current_ty.as_str(), expected_ty.as_str()]);
                if actual == expected {
                    return;
                }
                panic!(
                    "expect_type_mismatch failed: expected \"{}\" ≰ \"{}\", got \"{}\" ≰ \"{}\"",
                    cur_ty, exp_ty, current_ty, expected_ty
                );
            }
            _ => panic!("expect_type_mismatch called on non-TypeMismatch error {self:?}"),
        }
    }

    pub fn expect_unbound_ty_var(&self) {
        use CompilationErrorImpl::*;
        // TODO: once ty_var normalization is implemented, pass the ty_var as parameter
        match self.deref() {
            UnboundTypeVar { .. } => (),
            _ => panic!("expect_unbound_ty_val called on non-UnboundTypeVar error {self:?}"),
        }
    }

    pub fn expect_duplicate_record_field(&self, src: &str, exp_name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            DuplicatedField {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                let name = src[first_occurrence_span.as_range()].to_string();
                if name == exp_name {
                } else {
                    panic!(
                        "expect_duplicate_record_field failed: expected \"{}\", got \"{}\"",
                        exp_name, name
                    );
                }
            }
            _ => panic!(
                "expect_duplicate_record_field called on non-DuplicatedRecordField error {self:?}"
            ),
        }
    }

    pub fn expect_inconsistent_adt(&self) {
        use CompilationErrorImpl::*;
        match self.deref() {
            InconsistentADT { .. } => (),
            _ => panic!("expect_inconsistent_adt called on non-InconsistentADT error {self:?}"),
        }
    }

    pub fn expect_duplicated_variant(&self, src: &str, exp_name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            DuplicatedVariant {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                let name = &src[first_occurrence_span.as_range()];
                if name == exp_name {
                } else {
                    panic!(
                        "expect_duplicated_variant failed: expected \"{}\", got \"{}\"",
                        exp_name, name
                    );
                }
            }
            _ => panic!("expect_duplicated_variant called on non-DuplicatedVariant error {self:?}"),
        }
    }

    pub fn expect_mutable_paths_overlap(&self) {
        use CompilationErrorImpl::*;
        match self.deref() {
            MutablePathsOverlap { .. } => (),
            _ => panic!(
                "expect_mutable_paths_overlap called on non-MutablePathsOverlap error {self:?}"
            ),
        }
    }

    pub fn expect_undefined_var_in_string_formatting(&self, src: &str, exp_name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            UndefinedVarInStringFormatting { var_span, .. } => {
                let var_name = &src[var_span.as_range()];
                if var_name == exp_name {
                } else {
                    panic!(
                        "expect_undefined_var_in_string_formatting failed: expected \"{}\", got \"{}\"",
                        exp_name, var_name
                    );
                }
            }
            _ => panic!(
                "expect_undefined_var_in_string_formatting called on non-UndefinedVarInStringFormatting error {self:?}"
            ),
        }
    }

    pub fn expect_invalid_effect_dependency(&self, cur_eff: EffType, target_eff: EffType) {
        use CompilationErrorImpl::*;
        match self.deref() {
            InvalidEffectDependency { source, target, .. } => {
                if source == &cur_eff && target == &target_eff {
                    return;
                }
                panic!(
                    "expect_invalid_effect_dependency failed: expected {} ≰ {}, got {} ≰ {}",
                    cur_eff, target_eff, source, target
                );
            }
            _ => panic!(
                "expect_invalid_effect_dependency called on non-InvalidEffectDependency error {self:?}"
            ),
        }
    }

    pub fn expect_trait_impl_not_found(&self, trait_name: &str, tys: &[&str]) {
        use CompilationErrorImpl::*;
        match self.deref() {
            TraitImplNotFound {
                trait_ref: name,
                input_tys,
                ..
            } => {
                if name == trait_name
                    && input_tys
                        .iter()
                        .map(|ty| ty.as_str())
                        .eq(tys.iter().copied())
                {
                    return;
                }
                panic!(
                    "expect_trait_impl_not_found failed: expected {} over {:?}, got {} over {:?}",
                    trait_name, tys, name, input_tys
                );
            }
            _ => {
                panic!("expect_trait_impl_not_found called on non-TraitImplNotFound error {self:?}")
            }
        }
    }

    pub fn expect_trait_method_effect_mismatch(
        &self,
        expected_trait: &str,
        method: &str,
        expected_effects: &EffType,
        got_effects: &EffType,
    ) {
        use CompilationErrorImpl::*;
        match self.deref() {
            TraitMethodEffectMismatch {
                trait_ref,
                method_name,
                expected,
                got,
                ..
            } => {
                if trait_ref == expected_trait
                    && method_name.as_str() == method
                    && expected == expected_effects
                    && got == got_effects
                {
                    return;
                }
                panic!(
                    "expect_trait_method_effect_mismatch failed: expected trait {} method {} with effects {} but got {}, actual was trait {} method {} with effects {} but got {}",
                    expected_trait,
                    method,
                    expected_effects,
                    got_effects,
                    trait_ref,
                    method_name,
                    expected,
                    got
                );
            }
            _ => {
                panic!(
                    "expect_trait_method_effect_mismatch called on non-TraitMethodEffectMismatch error {self:?}"
                )
            }
        }
    }

    pub fn expect_return_outside_function(&self) {
        use CompilationErrorImpl::*;
        match self.deref() {
            ReturnOutsideFunction { .. } => (),
            _ => panic!(
                "expect_return_outside_function called on non-ReturnOutsideFunction error {self:?}"
            ),
        }
    }
}

/// Canonicalize rendered type/error fragments modulo fresh variable renaming.
///
/// This is only used in test helpers for comparing diagnostic strings whose
/// fresh type/effect variable names may differ while the mismatch shape stays
/// the same.
fn alpha_normalize_type_strings<const N: usize>(parts: [&str; N]) -> [String; N] {
    use std::collections::HashMap;

    fn is_boundary(ch: Option<char>) -> bool {
        ch.is_none_or(|c| !c.is_ascii_alphanumeric() && c != '_')
    }

    fn is_subscript_digit(ch: char) -> bool {
        matches!(
            ch,
            '₀' | '₁' | '₂' | '₃' | '₄' | '₅' | '₆' | '₇' | '₈' | '₉'
        )
    }

    let mut ty_vars = HashMap::<String, usize>::new();
    let mut eff_vars = HashMap::<String, usize>::new();
    parts.map(|part| {
        let chars = part.chars().collect::<Vec<_>>();
        let mut out = String::new();
        let mut i = 0;
        while i < chars.len() {
            let ch = chars[i];
            let prev = if i > 0 { Some(chars[i - 1]) } else { None };
            let next = if i + 1 < chars.len() {
                Some(chars[i + 1])
            } else {
                None
            };
            if ch.is_ascii_uppercase() && is_boundary(prev) && is_boundary(next) {
                let key = ch.to_string();
                let next_index = ty_vars.len();
                let index = *ty_vars.entry(key).or_insert(next_index);
                out.push('T');
                out.push_str(&index.to_string());
                i += 1;
            } else if ch == 'e' && is_boundary(prev) {
                let mut j = i + 1;
                while j < chars.len() && is_subscript_digit(chars[j]) {
                    j += 1;
                }
                if j > i + 1 && is_boundary(chars.get(j).copied()) {
                    let key = chars[i..j].iter().collect::<String>();
                    let next_index = eff_vars.len();
                    let index = *eff_vars.entry(key).or_insert(next_index);
                    out.push('e');
                    out.push_str(&index.to_string());
                    i = j;
                } else {
                    out.push(ch);
                    i += 1;
                }
            } else {
                out.push(ch);
                i += 1;
            }
        }
        out
    })
}
