// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::collections::HashMap;

use crate::{
    containers::b,
    effects::EffType,
    mutability::MutType,
    r#type::{store_types, FnArgType, FnType, NamedType, NativeType, Type, TypeKind},
};

/// A struct that can substitute types, possibly mutating itself in the process.
/// The substitution is non-recursive and should not look into inner types.
pub trait TypeSubstituer {
    fn substitute_type(&mut self, ty: Type) -> Type;
    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType;
    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType;
}

/// Recursively substitute all inner types in a type, using the given substituer.
pub fn substitute_type(ty: Type, substituer: &mut impl TypeSubstituer) -> Type {
    let mut kinds = Vec::new();
    let mut seen = HashMap::new();
    substitute_type_rec(ty, substituer, &mut kinds, &mut seen);
    store_types(&kinds)[0]
}

/// Recursively substitute all inner types in a list of types, using the given substituer.
pub fn substitute_types(tys: &[Type], substituer: &mut impl TypeSubstituer) -> Vec<Type> {
    let mut kinds = Vec::new();
    let mut seen = HashMap::new();
    let tys = substitute_types_rec(tys, substituer, &mut kinds, &mut seen);
    let new_tys = store_types(&kinds);
    // Map all local types to their new world types in the list of types
    tys.into_iter()
        .map(|ty| {
            ty.world()
                .map_or_else(|| new_tys[ty.index() as usize], |_| ty)
        })
        .collect()
}

/// Recursively substitute all inner types in a function type, using the given substituer.
pub fn substitute_fn_type(fn_ty: &FnType, substituer: &mut impl TypeSubstituer) -> FnType {
    let mut kinds = Vec::new();
    let mut seen = HashMap::new();
    let mut fn_ty = substitute_fn_type_rec(fn_ty, substituer, &mut kinds, &mut seen);
    let new_tys = store_types(&kinds);
    // Map all local types to their new world types in the function type
    let map_ty = |ty: Type| {
        ty.world()
            .map_or_else(|| new_tys[ty.index() as usize], |_| ty)
    };
    fn_ty.args = fn_ty
        .args
        .into_iter()
        .map(|arg| FnArgType::new(map_ty(arg.ty), arg.mut_ty))
        .collect();
    fn_ty.ret = map_ty(fn_ty.ret);
    fn_ty
}

fn substitute_type_rec(
    ty: Type,
    substituer: &mut impl TypeSubstituer,
    output: &mut Vec<TypeKind>,
    seen: &mut HashMap<Type, u32>,
) -> Type {
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
    seen: &mut HashMap<Type, u32>,
) -> Vec<Type> {
    tys.iter()
        .map(|ty| substitute_type_rec(*ty, substituer, output, seen))
        .collect()
}

fn substitute_fn_type_rec(
    fn_ty: &FnType,
    substituer: &mut impl TypeSubstituer,
    output: &mut Vec<TypeKind>,
    seen: &mut HashMap<Type, u32>,
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
