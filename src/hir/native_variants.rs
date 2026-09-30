// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Payload-free Rust enum results. The C entry returns the Rust discriminant as an `int`; a
//! generated Ferlium body maps it to symbolic cases, so the optimizer sees through the mapping.
use std::{iter, marker::PhantomData};

use ustr::{Ustr, ustr};

use super::native_functions::*;
use crate::{
    Location,
    containers::b,
    hir::{
        self, CallArgument, Node, NodeKind, VariantPayloadStorageSource,
        function::{CallableDefinition, ScriptFunction},
        hir_syn::{alloc_synth, immediate, load_local, static_apply},
        value::{LiteralValue, VariantPayloadStorage},
    },
    module::{
        FunctionId, LocalDecl, LocalDeclId, LocalFunctionId, Module, ModuleFunction, Visibility,
        id::Id,
    },
    std::math::int_type,
    types::{
        effects::EffType,
        r#type::{Type, variant_type},
        type_scheme::TypeScheme,
    },
};

#[doc(hidden)]
pub mod native_variant_private {
    /// Implemented only by `native_variant_result!`, which checks the enum against its cases.
    pub trait Sealed {}
}

/// A fieldless Rust enum usable as a native result; implement it with [`native_variant_result!`].
///
/// `CASES` pairs each Ferlium tag with its Rust discriminant. A native returning any other
/// discriminant violates its contract; the generated body then yields the last case.
///
/// [`native_variant_result!`]: crate::native_variant_result
pub trait NativeVariantResult: native_variant_private::Sealed + 'static {
    const CASES: &'static [(&'static str, i32)];
    fn discriminant(self) -> isize;
}

/// Implement [`NativeVariantResult`] for a fieldless enum, listing every case exactly once.
///
/// Rust rejects missing, repeated, or data-carrying cases, and discriminants outside `i32`:
/// ```
/// enum Signal { Stop, Go = 7 }
/// ferlium::native_variant_result!(Signal { Stop, Go });
/// ```
/// ```compile_fail
/// enum Signal { Stop, Go }
/// ferlium::native_variant_result!(Signal { Stop });
/// ```
/// ```compile_fail
/// enum Signal { Stop, Go }
/// ferlium::native_variant_result!(Signal { Stop, Go, Stop });
/// ```
/// ```compile_fail
/// enum Signal { Stop, Go(u8) }
/// ferlium::native_variant_result!(Signal { Stop, Go });
/// ```
/// ```compile_fail
/// #[repr(i64)]
/// enum Signal { Stop, Go = 1 << 40 }
/// ferlium::native_variant_result!(Signal { Stop, Go });
/// ```
#[macro_export]
macro_rules! native_variant_result {
    ($ty:ty { $($case:ident),+ $(,)? }) => {
        const _: () = {
            // Exhaustiveness rejects missing cases; unit patterns reject cases with fields.
            #[allow(dead_code)]
            fn exhaustive(value: $ty) {
                match value { $(<$ty>::$case => {})+ }
            }
            // Distinct variants have distinct discriminants, so equal ones mean a repeated case.
            // Lints such as `unreachable_patterns` are silenced in other crates' macro expansions.
            let discriminants: &[i128] = &[$(<$ty>::$case as i128),+];
            let mut i = 0;
            while i < discriminants.len() {
                assert!(
                    discriminants[i] >= i32::MIN as i128 && discriminants[i] <= i32::MAX as i128,
                    "native variant discriminant does not fit the i32 transport",
                );
                let mut j = i + 1;
                while j < discriminants.len() {
                    assert!(discriminants[i] != discriminants[j], "repeated native variant case");
                    j += 1;
                }
                i += 1;
            }
        };
        impl $crate::hir::native_functions::native_variant_private::Sealed for $ty {}
        impl $crate::hir::native_functions::NativeVariantResult for $ty {
            const CASES: &'static [(&'static str, i32)] =
                &[$((stringify!($case), <$ty>::$case as i32)),+];
            fn discriminant(self) -> isize {
                self as isize
            }
        }
    };
}

crate::native_variant_result!(std::cmp::Ordering {
    Less,
    Equal,
    Greater
});

/// A native entry returning a discriminant, with the cases its Ferlium body decodes.
pub struct NativeVariantCallable<E: EntryFunction> {
    raw: NativeCallable<E>,
    cases: &'static [(&'static str, i32)],
}

impl<E: EntryFunction> NativeVariantCallable<E> {
    pub fn description(
        self,
        arg_names: impl IntoIterator<Item = &'static str>,
        doc: &'static str,
        effects: EffType,
    ) -> NativeVariantDescription {
        NativeVariantDescription {
            raw: self.raw.description(arg_names, doc, effects),
            cases: self.cases,
            inline_never: false,
        }
    }
}

/// The two functions a native variant registers: the hidden `int` entry and its decoding body.
pub struct NativeVariantDescription {
    raw: ModuleFunction,
    cases: &'static [(&'static str, i32)],
    inline_never: bool,
}

impl NativeVariantDescription {
    /// Keep calls to the decoding body, for std entries whose identity a backend lowers directly.
    pub(crate) fn inline_never(mut self) -> Self {
        self.inline_never = true;
        self
    }

    /// Register the discriminant entry as `name$discriminant` and the decoding body as `name`.
    pub fn add_to(
        self,
        module: &mut Module,
        name: Ustr,
        visibility: Visibility,
    ) -> LocalFunctionId {
        let raw_ty = self.raw.definition.ty_scheme.ty.clone();
        let arg_names = self.raw.definition.arg_names.clone();
        let doc = self.raw.definition.doc.clone();
        let passing = self.raw.parameter_passing.clone();
        let raw = FunctionId::new(
            module.module_id(),
            module.add_function_with_visibility(
                ustr(&format!("{name}$discriminant")),
                self.raw,
                Visibility::Module,
            ),
        );
        let variant_ty = variant_type(self.cases.iter().map(|(tag, _)| (*tag, Type::unit())));
        let mut ty = raw_ty.clone();
        ty.ret = variant_ty;
        let mut definition = CallableDefinition::new(TypeScheme::new_just_type(ty), arg_names, doc);
        if self.inline_never {
            definition = definition.with_inline_never();
        }
        let span = Location::new_synthesized();
        let locals = definition.gen_locals_no_bounds(iter::repeat(span), span);
        let arena = &mut module.hir_arena;
        let args = raw_ty
            .args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                alloc_synth(arena, load_local(LocalDeclId::from_index(index)), arg.ty)
            })
            .collect();
        let call = static_apply(
            raw,
            raw_ty.clone(),
            CallArgument::from_values_and_passing(args, passing.clone()),
            span,
        );
        let discriminant = arena.alloc(Node::new(call, int_type(), raw_ty.effects.clone(), span));
        let mut variant = |tag: &str| {
            let payload = alloc_synth(arena, immediate(LiteralValue::new_native(())), Type::unit());
            alloc_synth(
                arena,
                NodeKind::Variant(hir::Variant {
                    tag: ustr(tag),
                    payload,
                    payload_storage: Some(VariantPayloadStorageSource::Static(
                        VariantPayloadStorage::Inline,
                    )),
                }),
                variant_ty,
            )
        };
        // Total without a failure path: an out-of-contract discriminant selects the last case.
        let ((last, _), rest) = self.cases.split_last().expect("inhabited native variant");
        let alternatives = rest
            .iter()
            .map(|(tag, discriminant)| {
                (
                    LiteralValue::new_native(*discriminant as isize),
                    variant(tag),
                )
            })
            .collect();
        let default = variant(last);
        let root = arena.alloc(Node::new(
            NodeKind::Case(b(hir::Case {
                value: discriminant,
                alternatives,
                default,
            })),
            variant_ty,
            raw_ty.effects.clone(),
            span,
        ));
        let function = ModuleFunction::new_elaborated(
            definition,
            b(ScriptFunction::new(root, passing.len())),
            passing,
            None,
            locals.into_iter().map(LocalDecl::into_elaborated).collect(),
        );
        module.add_function_with_visibility(name, function, visibility)
    }
}

macro_rules! variant_entries {
    ($variant:ident, $direct:ident $(, $arg:ident : $value:ident)*) => {
        /// Adapts a Rust function returning a [`NativeVariantResult`] to a discriminant entry.
        pub struct $variant<$($arg: NativeArgument,)* R: NativeVariantResult>(PhantomData<fn($($arg,)*) -> R>);
        impl<$($arg: NativeArgument,)* R: NativeVariantResult> $variant<$($arg,)* R> {
            pub fn from_rust<F>(function: F) -> NativeVariantCallable<$direct<$($arg,)* isize>>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> R + Copy + 'static {
                NativeVariantCallable {
                    raw: $direct::from_rust(move |$($value: $arg::Borrowed<'_>),*| {
                        function($($value),*).discriminant()
                    }),
                    cases: R::CASES,
                }
            }
        }
    };
}

variant_entries!(NativeVariantFn0, NativeFn0);
variant_entries!(NativeVariantFn1, NativeFn1, A: a);
variant_entries!(NativeVariantFn2, NativeFn2, A: a, B: b);
variant_entries!(NativeVariantFn3, NativeFn3, A: a, B: b, C: c);
