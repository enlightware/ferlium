// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    FxHashMap,
    containers::b,
    types::effects::EffType,
    types::mutability::MutType,
    types::r#type::{
        FnArgType, FnType, NamedType, NativeType, SubscriptMemberType, SubscriptType,
        TYPE_HEIGHT_LIMIT, Type, TypeKind, TypeLimitExceeded, store_types,
    },
    types::type_like::TypeLike,
    types::type_mapper::{SimpleInstantiationMapper, TypeMapper},
};

use super::type_inference::substitution::InstSubst;

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

/// A graph of local type nodes under construction by a substitution. The traversal descends
/// recursively, and the graph is interned only once it returns, so the traversal counts its own
/// depth: it refuses to descend past `TYPE_HEIGHT_LIMIT`, which bounds its stack. The height and
/// size of the results are checked once interned, where they are exact: a local node may become
/// a member of a recursive world, whose metrics count its internal edges once, so the metrics of
/// the local graph would overcount them.
struct SubstitutionGraph<'o> {
    output: &'o mut Vec<TypeKind>,
    seen: FxHashMap<Type, u32>,
    depth: u32,
}

impl<'o> SubstitutionGraph<'o> {
    fn new(output: &'o mut Vec<TypeKind>) -> Self {
        Self {
            output,
            seen: FxHashMap::default(),
            depth: 0,
        }
    }

    /// Start a node for `ty`, as the traversal descends into it.
    fn begin(&mut self, ty: Type) -> Result<u32, TypeLimitExceeded> {
        if self.depth >= TYPE_HEIGHT_LIMIT {
            return Err(TypeLimitExceeded::Height(TYPE_HEIGHT_LIMIT + 1));
        }
        self.depth += 1;
        let index = self.output.len() as u32;
        self.seen.insert(ty, index);
        // A placeholder, until the node's children are built.
        self.output.push(TypeKind::Never);
        Ok(index)
    }

    /// Complete the node at `index`, as the traversal returns from it.
    fn end(&mut self, index: u32, kind: TypeKind) -> Type {
        self.depth -= 1;
        self.output[index as usize] = kind;
        Type::new_local(index)
    }

    /// Intern the graph and replace `roots`, which the substitution staged, by their interned
    /// types, checked against the limits.
    fn finish(self, roots: &mut [Type]) -> Result<(), TypeLimitExceeded> {
        if !self.output.is_empty() {
            let new_tys = store_types(self.output);
            for root in roots.iter_mut() {
                *root = remap_local_type(*root, &new_tys);
            }
        }
        roots.iter().try_for_each(|root| root.check_limits())
    }
}

/// Recursively substitute all inner types in a type, using the given substituer.
pub fn substitute_type(
    ty: Type,
    substituer: &mut impl TypeSubstituer,
) -> Result<Type, TypeLimitExceeded> {
    let mut tys = [ty];
    substitute_types_in_place(&mut tys, substituer)?;
    Ok(tys[0])
}

/// Recursively instantiate type/effect variables, preserving recursive type graphs.
pub(crate) fn instantiate_type(ty: Type, subst: &InstSubst) -> Type {
    map_type_recursive(ty, &mut SimpleInstantiationMapper::new(subst))
}

/// Instantiate into an existing, unfinished graph without interning it. Replacements
/// may refer to local nodes in `output`; they stay opaque to the instantiation traversal.
pub(crate) fn instantiate_type_in_graph(
    ty: Type,
    subst: &InstSubst,
    output: &mut Vec<TypeKind>,
) -> Type {
    map_type_rec(
        ty,
        &mut SimpleInstantiationMapper::new(subst),
        output,
        &mut FxHashMap::default(),
    )
}

/// Recursively map a type while preserving recursive type graphs.
///
/// Variable replacements are treated as opaque, matching `TypeMapper`'s
/// existing instantiation semantics: the mapper rewrites the original graph,
/// not the types it returns as replacements.
pub(crate) fn map_type_recursive(ty: Type, mapper: &mut impl TypeMapper) -> Type {
    let mut kinds = Vec::new();
    let mut seen = FxHashMap::default();
    let result = map_type_rec(ty, mapper, &mut kinds, &mut seen);
    if result.world().is_some() {
        result
    } else {
        store_types(&kinds)[result.index() as usize]
    }
}

/// Recursively substitute all inner types in a list of types, using the given substituer.
pub fn substitute_types(
    tys: &[Type],
    substituer: &mut impl TypeSubstituer,
) -> Result<Vec<Type>, TypeLimitExceeded> {
    let mut tys = tys.to_vec();
    substitute_types_in_place(&mut tys, substituer)?;
    Ok(tys)
}

/// Recursively substitute all inner types in a list of types in place. On error, `tys` is
/// unchanged.
pub fn substitute_types_in_place(
    tys: &mut [Type],
    substituer: &mut impl TypeSubstituer,
) -> Result<(), TypeLimitExceeded> {
    let mut kinds = Vec::new();
    let mut graph = SubstitutionGraph::new(&mut kinds);
    let mut roots = tys
        .iter()
        .map(|ty| substitute_type_rec(*ty, substituer, &mut graph))
        .collect::<Result<Vec<_>, _>>()?;
    graph.finish(&mut roots)?;
    tys.copy_from_slice(&roots);
    Ok(())
}

/// Recursively substitute type fields in place, sharing one substitution batch.
pub fn substitute_type_fields_in_place<T>(
    items: &mut [T],
    mut get_type: impl for<'a> FnMut(&'a mut T) -> &'a mut Type,
    substituer: &mut impl TypeSubstituer,
) -> Result<(), TypeLimitExceeded> {
    let mut tys: Vec<_> = items.iter_mut().map(|item| *get_type(item)).collect();
    substitute_types_in_place(&mut tys, substituer)?;
    for (item, ty) in items.iter_mut().zip(tys) {
        *get_type(item) = ty;
    }
    Ok(())
}

/// Recursively substitute all inner types in a function type, using the given substituer.
pub fn substitute_fn_type(
    fn_ty: &FnType,
    substituer: &mut impl TypeSubstituer,
) -> Result<FnType, TypeLimitExceeded> {
    let mut fn_ty = fn_ty.clone();
    substitute_fn_type_in_place(&mut fn_ty, substituer)?;
    Ok(fn_ty)
}

/// Recursively substitute all inner types in a function type in place. On error, `fn_ty` is
/// unchanged.
pub fn substitute_fn_type_in_place(
    fn_ty: &mut FnType,
    substituer: &mut impl TypeSubstituer,
) -> Result<(), TypeLimitExceeded> {
    let mut kinds = Vec::new();
    let mut graph = SubstitutionGraph::new(&mut kinds);
    let mut substituted = substitute_fn_type_rec(fn_ty, substituer, &mut graph)?;
    let mut tys: Vec<_> = substituted.args.iter().map(|arg| arg.ty).collect();
    tys.push(substituted.ret);
    graph.finish(&mut tys)?;
    substituted.ret = tys.pop().unwrap();
    for (arg, ty) in substituted.args.iter_mut().zip(tys) {
        arg.ty = ty;
    }
    substituted.check_limits()?;
    *fn_ty = substituted;
    Ok(())
}

/// Recursively substitute all inner types in a subscript type in place. On error,
/// `subscript_ty` is unchanged.
pub fn substitute_subscript_type_in_place(
    subscript_ty: &mut SubscriptType,
    substituer: &mut impl TypeSubstituer,
) -> Result<(), TypeLimitExceeded> {
    let mut kinds = Vec::new();
    let mut graph = SubstitutionGraph::new(&mut kinds);
    let mut substituted = substitute_subscript_type_rec(subscript_ty, substituer, &mut graph)?;
    let mut tys: Vec<_> = substituted.args.iter().map(|arg| arg.ty).collect();
    tys.push(substituted.ret);
    graph.finish(&mut tys)?;
    substituted.ret = tys.pop().unwrap();
    for (arg, ty) in substituted.args.iter_mut().zip(tys) {
        arg.ty = ty;
    }
    substituted.check_limits()?;
    *subscript_ty = substituted;
    Ok(())
}

fn remap_local_type(ty: Type, new_tys: &[Type]) -> Type {
    ty.world()
        .map_or_else(|| new_tys[ty.index() as usize], |_| ty)
}

fn substitute_type_rec(
    ty: Type,
    substituer: &mut impl TypeSubstituer,
    graph: &mut SubstitutionGraph,
) -> Result<Type, TypeLimitExceeded> {
    // Fast path: ask the substituer whether it can affect this type at all.
    if !substituer.affects_type(ty) {
        return Ok(ty);
    }

    // Do substitution for this specific type
    let ty = substituer.substitute_type(ty);

    // Has this type already been substituted?
    if let Some(index) = graph.seen.get(&ty) {
        // Yes, return the index in output
        return Ok(Type::new_local(*index));
    }

    // No, start a node for it
    let this_ty_index = graph.begin(ty)?;

    // Recurse into the type kind
    let type_data: TypeKind = { ty.data().clone() };
    use TypeKind::*;
    let kind = match type_data {
        Variable(var) => Variable(var),
        Native(ty) => Native(b(NativeType::new(
            ty.bare_ty.clone(),
            substitute_types_rec(&ty.arguments, substituer, graph)?,
        ))),
        Variant(tys) => Variant(
            tys.into_iter()
                .map(|(name, ty)| Ok((name, substitute_type_rec(ty, substituer, graph)?)))
                .collect::<Result<_, _>>()?,
        ),
        Tuple(tys) => Tuple(substitute_types_rec(&tys, substituer, graph)?),
        Record(fields) => Record(
            fields
                .into_iter()
                .map(|(name, ty)| Ok((name, substitute_type_rec(ty, substituer, graph)?)))
                .collect::<Result<_, _>>()?,
        ),
        Function(fn_ty) => Function(b(substitute_fn_type_rec(&fn_ty, substituer, graph)?)),
        Subscript(subscript) => Subscript(b(substitute_subscript_type_rec(
            &subscript, substituer, graph,
        )?)),
        Named(NamedType {
            def: decl,
            params: args,
            effect_params,
        }) => Named(NamedType {
            def: decl,
            params: substitute_types_rec(&args, substituer, graph)?,
            effect_params: effect_params
                .iter()
                .map(|eff| substituer.substitute_effect_type(eff))
                .collect(),
        }),
        Never => Never,
    };

    // Write back the actual kind into the output list
    Ok(graph.end(this_ty_index, kind))
}

fn map_type_rec(
    ty: Type,
    mapper: &mut impl TypeMapper,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> Type {
    if !mapper.affects_type(ty) {
        return ty;
    }

    let type_data: TypeKind = { ty.data().clone() };
    if let TypeKind::Variable(var) = type_data {
        return mapper.map_type(Type::variable(var));
    }

    if let Some(index) = seen.get(&ty) {
        return Type::new_local(*index);
    }

    let this_ty_index = output.len() as u32;
    seen.insert(ty, this_ty_index);
    output.push(TypeKind::Never);

    use TypeKind::*;
    let kind = match type_data {
        Variable(_) => unreachable!(),
        Native(ty) => Native(b(NativeType::new(
            ty.bare_ty.clone(),
            map_types_rec(&ty.arguments, mapper, output, seen),
        ))),
        Variant(tys) => Variant(
            tys.into_iter()
                .map(|(name, ty)| (name, map_type_rec(ty, mapper, output, seen)))
                .collect(),
        ),
        Tuple(tys) => Tuple(map_types_rec(&tys, mapper, output, seen)),
        Record(fields) => Record(
            fields
                .into_iter()
                .map(|(name, ty)| (name, map_type_rec(ty, mapper, output, seen)))
                .collect(),
        ),
        Function(fn_ty) => Function(b(map_fn_type_rec(&fn_ty, mapper, output, seen))),
        Subscript(subscript) => {
            Subscript(b(map_subscript_type_rec(&subscript, mapper, output, seen)))
        }
        Named(NamedType {
            def,
            params,
            effect_params,
        }) => Named(NamedType {
            def,
            params: map_types_rec(&params, mapper, output, seen),
            effect_params: effect_params
                .iter()
                .map(|eff| mapper.map_effect_type(eff))
                .collect(),
        }),
        Never => Never,
    };

    output[this_ty_index as usize] = kind;
    Type::new_local(this_ty_index)
}

fn map_types_rec(
    tys: &[Type],
    mapper: &mut impl TypeMapper,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> Vec<Type> {
    tys.iter()
        .map(|ty| map_type_rec(*ty, mapper, output, seen))
        .collect()
}

fn map_fn_type_rec(
    fn_ty: &FnType,
    mapper: &mut impl TypeMapper,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> FnType {
    let args = map_fn_arg_types_rec(&fn_ty.args, mapper, output, seen);
    let ret = map_type_rec(fn_ty.ret, mapper, output, seen);
    let effects = mapper.map_effect_type(&fn_ty.effects);
    FnType::new(args, ret, effects)
}

fn map_fn_arg_types_rec(
    args: &[FnArgType],
    mapper: &mut impl TypeMapper,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> Vec<FnArgType> {
    args.iter()
        .map(|arg| {
            FnArgType::new(
                map_type_rec(arg.ty, mapper, output, seen),
                mapper.map_mut_type(arg.mut_ty),
            )
        })
        .collect()
}

fn map_subscript_type_rec(
    subscript: &SubscriptType,
    mapper: &mut impl TypeMapper,
    output: &mut Vec<TypeKind>,
    seen: &mut FxHashMap<Type, u32>,
) -> SubscriptType {
    let args = map_fn_arg_types_rec(&subscript.args, mapper, output, seen);
    let ret = map_type_rec(subscript.ret, mapper, output, seen);
    SubscriptType::new(
        args,
        ret,
        map_subscript_member_type(subscript.ref_member.as_ref(), mapper),
        map_subscript_member_type(subscript.mut_member.as_ref(), mapper),
    )
}

fn map_subscript_member_type(
    member: Option<&SubscriptMemberType>,
    mapper: &mut impl TypeMapper,
) -> Option<SubscriptMemberType> {
    member.map(|member| {
        SubscriptMemberType::new(
            mapper.map_effect_type(&member.effects),
            member.result_convention,
        )
    })
}

fn substitute_types_rec(
    tys: &[Type],
    substituer: &mut impl TypeSubstituer,
    graph: &mut SubstitutionGraph,
) -> Result<Vec<Type>, TypeLimitExceeded> {
    tys.iter()
        .map(|ty| substitute_type_rec(*ty, substituer, graph))
        .collect()
}

fn substitute_fn_type_rec(
    fn_ty: &FnType,
    substituer: &mut impl TypeSubstituer,
    graph: &mut SubstitutionGraph,
) -> Result<FnType, TypeLimitExceeded> {
    let args = substitute_fn_arg_types_rec(&fn_ty.args, substituer, graph)?;
    let ret = substitute_type_rec(fn_ty.ret, substituer, graph)?;
    let effects = substituer.substitute_effect_type(&fn_ty.effects);
    Ok(FnType::new(args, ret, effects))
}

fn substitute_fn_arg_types_rec(
    args: &[FnArgType],
    substituer: &mut impl TypeSubstituer,
    graph: &mut SubstitutionGraph,
) -> Result<Vec<FnArgType>, TypeLimitExceeded> {
    args.iter()
        .map(|arg| {
            Ok(FnArgType::new(
                substitute_type_rec(arg.ty, substituer, graph)?,
                substituer.substitute_mut_type(arg.mut_ty),
            ))
        })
        .collect()
}

fn substitute_subscript_type_rec(
    subscript: &SubscriptType,
    substituer: &mut impl TypeSubstituer,
    graph: &mut SubstitutionGraph,
) -> Result<SubscriptType, TypeLimitExceeded> {
    let args = substitute_fn_arg_types_rec(&subscript.args, substituer, graph)?;
    let ret = substitute_type_rec(subscript.ret, substituer, graph)?;
    Ok(SubscriptType::new(
        args,
        ret,
        substitute_subscript_member_type(subscript.ref_member.as_ref(), substituer),
        substitute_subscript_member_type(subscript.mut_member.as_ref(), substituer),
    ))
}

fn substitute_subscript_member_type(
    member: Option<&SubscriptMemberType>,
    substituer: &mut impl TypeSubstituer,
) -> Option<SubscriptMemberType> {
    member.map(|member| {
        SubscriptMemberType::new(
            substituer.substitute_effect_type(&member.effects),
            member.result_convention,
        )
    })
}
