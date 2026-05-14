// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    FxHashMap,
    containers::b,
    types::effects::EffType,
    types::mutability::MutType,
    types::r#type::{FnArgType, FnType, NamedType, NativeType, Type, TypeKind, store_types},
    types::type_like::TypeLike,
};

/// Leaf-rewrite policy for recursive substitution of interned `Type` graphs.
///
/// Implementors only provide the direct rewrite for one `Type`, `MutType`, or
/// `EffType`. The free functions in this module own the recursive traversal,
/// cycle handling, shared `seen` map, batched `store_types`, and remapping of
/// local type ids back to interned world types.
///
/// `substitute_type` should not recursively substitute inner types itself; if it
/// returns a composite type, the driver will recurse into it.
pub trait TypeSubstituer {
    fn substitute_type(&mut self, ty: Type) -> Type;
    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType;
    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType;

    /// Returns `false` when the substitution driver can return this `Type` unchanged without recursively rebuilding and re-interning it.
    fn affects_type(&mut self, ty: Type) -> bool {
        !ty.is_constant()
    }
}

/// Recursively substitute all inner types in a type, using the given substituer.
pub fn substitute_type(ty: Type, substituer: &mut impl TypeSubstituer) -> Type {
    let mut kinds = Vec::new();
    let mut seen = FxHashMap::default();
    let result = substitute_type_rec(ty, substituer, &mut kinds, &mut seen);
    // The recursive call may short-circuit and return the input `Type` directly
    // when it is fully concrete (no free variables to resolve); in that case
    // there is nothing to re-intern.
    if result.world().is_some() {
        result
    } else {
        store_types(&kinds)[result.index() as usize]
    }
}

/// Recursively substitute all inner types in a list of types, using the given substituer.
pub fn substitute_types(tys: &[Type], substituer: &mut impl TypeSubstituer) -> Vec<Type> {
    let mut tys = tys.to_vec();
    substitute_types_in_place(&mut tys, substituer);
    tys
}

/// Recursively substitute all inner types in a list of types in place.
pub fn substitute_types_in_place(tys: &mut [Type], substituer: &mut impl TypeSubstituer) {
    let mut kinds = Vec::new();
    let mut seen = FxHashMap::default();
    for ty in tys.iter_mut() {
        *ty = substitute_type_rec(*ty, substituer, &mut kinds, &mut seen);
    }
    if kinds.is_empty() {
        return;
    }
    let new_tys = store_types(&kinds);
    for ty in tys {
        *ty = remap_local_type(*ty, &new_tys);
    }
}

/// Recursively substitute type fields in place, sharing one substitution batch.
pub fn substitute_type_fields_in_place<T>(
    items: &mut [T],
    mut get_type: impl for<'a> FnMut(&'a mut T) -> &'a mut Type,
    substituer: &mut impl TypeSubstituer,
) {
    let mut kinds = Vec::new();
    let mut seen = FxHashMap::default();
    for item in items.iter_mut() {
        let ty = get_type(item);
        *ty = substitute_type_rec(*ty, substituer, &mut kinds, &mut seen);
    }
    if kinds.is_empty() {
        return;
    }
    let new_tys = store_types(&kinds);
    for item in items {
        let ty = get_type(item);
        *ty = remap_local_type(*ty, &new_tys);
    }
}

/// Recursively substitute all inner types in a function type, using the given substituer.
pub fn substitute_fn_type(fn_ty: &FnType, substituer: &mut impl TypeSubstituer) -> FnType {
    let mut fn_ty = fn_ty.clone();
    substitute_fn_type_in_place(&mut fn_ty, substituer);
    fn_ty
}

/// Recursively substitute all inner types in a function type in place.
pub fn substitute_fn_type_in_place(fn_ty: &mut FnType, substituer: &mut impl TypeSubstituer) {
    let mut kinds = Vec::new();
    let mut seen = FxHashMap::default();
    for arg in &mut fn_ty.args {
        arg.ty = substitute_type_rec(arg.ty, substituer, &mut kinds, &mut seen);
        arg.mut_ty = substituer.substitute_mut_type(arg.mut_ty);
    }
    fn_ty.ret = substitute_type_rec(fn_ty.ret, substituer, &mut kinds, &mut seen);
    fn_ty.effects = substituer.substitute_effect_type(&fn_ty.effects);
    if kinds.is_empty() {
        return;
    }
    let new_tys = store_types(&kinds);
    for arg in &mut fn_ty.args {
        arg.ty = remap_local_type(arg.ty, &new_tys);
    }
    fn_ty.ret = remap_local_type(fn_ty.ret, &new_tys);
}

fn remap_local_type(ty: Type, new_tys: &[Type]) -> Type {
    ty.world()
        .map_or_else(|| new_tys[ty.index() as usize], |_| ty)
}

fn substitute_type_rec(
    ty: Type,
    substituer: &mut impl TypeSubstituer,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> Type {
    // Fast path: ask the substituer whether it can affect this type at all.
    if !substituer.affects_type(ty) {
        return ty;
    }

    // Do substitution for this specific type
    let ty = substituer.substitute_type(ty);

    // Has this type already been substituted?
    if let Some(index) = seen.get(&ty) {
        // Yes, return the index in output
        return Type::new_local(*index);
    }

    // No, add it to the list of seen types
    let this_ty_index = output.len() as u32;
    seen.insert(ty, this_ty_index);

    // And put a placeholder for now in the output list
    output.push(TypeKind::Never);

    // Recurse into the type kind
    let type_data: TypeKind = { ty.data().clone() };
    use TypeKind::*;
    let kind = match type_data {
        Variable(var) => Variable(var),
        Native(ty) => Native(b(NativeType::new(
            ty.bare_ty.clone(),
            substitute_types_rec(&ty.arguments, substituer, output, seen),
        ))),
        Variant(tys) => Variant(
            tys.into_iter()
                .map(|(name, ty)| (name, substitute_type_rec(ty, substituer, output, seen)))
                .collect(),
        ),
        Tuple(tys) => Tuple(substitute_types_rec(&tys, substituer, output, seen)),
        Record(fields) => Record(
            fields
                .into_iter()
                .map(|(name, ty)| (name, substitute_type_rec(ty, substituer, output, seen)))
                .collect(),
        ),
        Function(fn_ty) => Function(b(substitute_fn_type_rec(&fn_ty, substituer, output, seen))),
        Named(NamedType {
            def: decl,
            params: args,
        }) => Named(NamedType {
            def: decl,
            params: substitute_types_rec(&args, substituer, output, seen),
        }),
        Never => Never,
    };

    // Write back the actual kind into the output list
    output[this_ty_index as usize] = kind;
    Type::new_local(this_ty_index)
}

fn substitute_types_rec(
    tys: &[Type],
    substituer: &mut impl TypeSubstituer,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> Vec<Type> {
    tys.iter()
        .map(|ty| substitute_type_rec(*ty, substituer, output, seen))
        .collect()
}

fn substitute_fn_type_rec(
    fn_ty: &FnType,
    substituer: &mut impl TypeSubstituer,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> FnType {
    let args = fn_ty
        .args
        .iter()
        .map(|arg| {
            FnArgType::new(
                substitute_type_rec(arg.ty, substituer, output, seen),
                substituer.substitute_mut_type(arg.mut_ty),
            )
        })
        .collect();
    let ret = substitute_type_rec(fn_ty.ret, substituer, output, seen);
    let effects = substituer.substitute_effect_type(&fn_ty.effects);
    FnType::new(args, ret, effects)
}
