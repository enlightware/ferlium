// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Structural properties of a concrete type, asked by more than one stage.
//!
//! Type inference and HIR elaboration ask through the trait solver; the MIR optimizer asks through a
//! `ModuleEnv`, having no solver. The query is the same, so it lives here as a free function over
//! the small environment it needs.
//!
//! `type_has_static_layout` in `std::value` is this module's sibling and belongs here too; it is
//! left where it is until something needs it moved.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    Modules,
    desugar::DepGraphNode,
    graph::find_strongly_connected_components,
    module::{ConcreteTraitImplKey, Module, ModuleEnv, TraitId, TypeDefId, id::Id},
    types::{
        effects::EffType,
        r#type::{
            NamedType, REPRESENTATION_HEIGHT_LIMIT, REPRESENTATION_SIZE_LIMIT, RepresentationParam,
            RepresentationSummary, Type, TypeDef, TypeKind, TypeVar,
        },
        type_like::TypeLike,
        type_matching::erase_type_effects,
    },
};

/// The type definitions that the representations of types depend on.
pub(crate) trait TypeDefEnv {
    fn type_def(&self, id: TypeDefId) -> &TypeDef;
}

/// What [`concrete_type_is_trivial_copy`] needs from whoever asks it.
pub(crate) trait TypePropertyEnv: TypeDefEnv {
    /// Whether `ty` opts into `TrivialCopy` through an impl in the trait's own module.
    ///
    /// Probed in the module that owns the trait rather than in the current visibility scope, so a
    /// native-only marker property does not change when an unrelated module is added or removed.
    fn has_trivial_copy_impl(&self, ty: Type) -> bool;
}

/// The key a `TrivialCopy` opt-in for `ty` is registered under, and the trait it belongs to.
pub(crate) fn trivial_copy_impl_key(trait_id: TraitId, ty: Type) -> ConcreteTraitImplKey {
    ConcreteTraitImplKey::new(trait_id, vec![ty])
}

/// Whether representation-copying this concrete type is semantically valid.
///
/// Native types opt in through concrete `TrivialCopy` impls. Inline product types derive the
/// property structurally, while named types do so only when they have no explicit custom `Value`
/// impl overriding ownership behaviour.
///
/// A non-recursive sum qualifies when every possible inline payload qualifies. A recursive
/// occurrence is indirect and owns its allocation, so the recursion check below rejects it.
pub(crate) fn concrete_type_is_trivial_copy(ty: Type, env: &impl TypePropertyEnv) -> bool {
    if !ty.is_constant() {
        return false;
    }
    TrivialCopyWalk::default().is_trivial_copy(ty, env)
}

/// One query of [`concrete_type_is_trivial_copy`], which decides each type it meets once.
///
/// A decision does not depend on the types being walked when it is made: a type whose walk meets
/// one of them lies on a cycle, so it is not copyable from wherever it is asked.
#[derive(Default)]
struct TrivialCopyWalk {
    active: FxHashSet<Type>,
    decided: FxHashMap<Type, bool>,
}

impl TrivialCopyWalk {
    fn is_trivial_copy(&mut self, ty: Type, env: &impl TypePropertyEnv) -> bool {
        if env.has_trivial_copy_impl(ty) {
            return true;
        }
        if let Some(&decided) = self.decided.get(&ty) {
            return decided;
        }
        // A recursive occurrence is represented indirectly, so it owns storage and cannot be
        // copied by representation.
        if !self.active.insert(ty) {
            return false;
        }
        // The types being walked are as many as the walk is deep. A type whose representation was
        // checked never reaches the limit; one first built when specializing can, and is then
        // taken as not copyable, which is always sound.
        if self.active.len() > REPRESENTATION_HEIGHT_LIMIT as usize {
            self.active.remove(&ty);
            return false;
        }

        let kind = ty.data().clone();
        let result = match kind {
            TypeKind::Tuple(member_tys) => member_tys
                .into_iter()
                .all(|member_ty| self.is_trivial_copy(member_ty, env)),
            TypeKind::Record(fields) => fields
                .into_iter()
                .all(|(_, field_ty)| self.is_trivial_copy(field_ty, env)),
            TypeKind::Named(named) => {
                let type_def = env.type_def(named.def);
                !type_def.has_custom_value_impl && {
                    let shape_ty = type_def
                        .instantiated_shape_with_effects(&named.params, &named.effect_params);
                    self.is_trivial_copy(shape_ty, env)
                }
            }
            // Non-recursive variant payloads are stored inline. The tag and union are
            // representation-copyable exactly when every possible payload is
            // representation-copyable.
            TypeKind::Variant(cases) => cases
                .into_iter()
                .all(|(_, payload_ty)| self.is_trivial_copy(payload_ty, env)),
            TypeKind::Native(_)
            | TypeKind::Function(_)
            | TypeKind::Subscript(_)
            | TypeKind::Never
            | TypeKind::Variable(_) => false,
        };
        self.active.remove(&ty);
        // The query's own type is not met again once it returns.
        if !self.active.is_empty() {
            self.decided.insert(ty, result);
        }
        result
    }
}

/// The metrics of the representation of a type: the type with each named type in it replaced by its
/// definition's shape, down to the leaves whose layout does not depend on what they hold, natives,
/// callables and variables. They follow from the type itself and the summaries of the definitions
/// it names (`RepresentationSummary`): computing them expands a named type only where its summary
/// cannot give them, as below.
///
/// The height bounds the stack of a walk that expands named types and does not revisit a type it is
/// walking; the size, counting a repeated part at each occurrence, bounds the work of one that does
/// not share repeated parts. Within a group of mutually recursive types, such a walk goes through
/// each type at most once, so a group counts as the sum of its types, as a recursive world does
/// (see `TypeSummary::height`). Tarjan's algorithm finds the groups.
///
/// A named type counts as its shape given its arguments. Its definition's summary gives that,
/// each argument counting at each occurrence of its parameter, unless an argument is on a cycle of
/// a recursive structural type: the shape could then hold types of that cycle, which a walk goes
/// through once. So the walk measures such a shape itself, without effects, which never change a
/// representation and would otherwise tell apart instances of a recursive definition. An argument
/// thus counts the same whether a definition holds it or a parameter substituted with it. The parts
/// of a shape count as written, also when an argument off any cycle makes them the unfolding of a
/// recursive type, as `End | Next(T, X)` at `int` with `type X = End | Next(int, X)`: they then
/// count more than that type.
pub(crate) struct RepresentationMetrics<'a, E> {
    env: &'a E,
    /// The index of each parameter of the definition being summarized, which count as no part.
    params: FxHashMap<TypeVar, usize>,
    /// The group of mutually recursive definitions being summarized: a reference to one of them is
    /// one part, as walks stop where they meet again a type they are walking.
    group: Option<&'a FxHashSet<TypeDefId>>,
    /// The metrics of each type whose group is complete.
    done: FxHashMap<Type, Metrics>,
    /// The types of the incomplete groups, in the order the walk met them, each with how it is
    /// measured: Tarjan's stack.
    stack: Vec<Visit>,
    /// For each type of `stack`, the smallest index in it that its walk reached.
    low: FxHashMap<Type, usize>,
}

/// A type that the walk met, with how it measures it, decided then, and the children it walks.
struct Visit {
    ty: Type,
    measure: Measure,
    children: Vec<Type>,
}

/// How the walk measures a type.
enum Measure {
    /// A parameter of the definition being summarized, of this index, which counts as no part.
    Param(usize),
    /// One part: a leaf, or a reference to a definition of the group being summarized.
    Part,
    /// One part above its children: the members of a product or a variant, or the shape of a
    /// named type that the walk measures itself.
    Above,
    /// A named type, by its definition's summary given its arguments: its children are those at
    /// the parameters that occur.
    Summary(NamedType),
}

/// The metrics of a representation, and of the occurrences in it of the parameters being
/// summarized.
#[derive(Debug, Clone, Default)]
struct Metrics {
    height: u32,
    size: u32,
    /// The occurrences of the parameters that occur, by index in increasing order: sparse, so
    /// that a definition with many parameters, each occurring in a small part of it, is summarized
    /// in time and memory linear in its size.
    occurrences: Vec<(usize, Occurrence)>,
}

/// The occurrences of a parameter in a representation.
#[derive(Debug, Clone, Copy)]
struct Occurrence {
    /// The depth of its deepest occurrence.
    depth: u32,
    /// Its number of occurrences.
    count: u32,
}

impl Occurrence {
    fn below(self, depth: u32, count: u32) -> Self {
        Self {
            depth: self.depth.saturating_add(depth),
            count: self.count.saturating_mul(count),
        }
    }
}

impl Metrics {
    /// A part with no children: a leaf, or a type of the same recursive group counted elsewhere.
    fn part() -> Self {
        Self {
            height: 1,
            size: 1,
            occurrences: Vec::new(),
        }
    }

    /// An occurrence of the parameter of `index`, which counts as no part.
    fn param(index: usize) -> Self {
        Self {
            height: 0,
            size: 0,
            occurrences: vec![(index, Occurrence { depth: 0, count: 1 })],
        }
    }

    /// A representation found higher than the limit, of which nothing more is known: it is at least
    /// one more than the limit high, and as many parts.
    fn beyond_height() -> Self {
        let height = REPRESENTATION_HEIGHT_LIMIT + 1;
        Self {
            height,
            size: height,
            occurrences: Vec::new(),
        }
    }

    /// One part above `children`.
    fn above<'m>(children: impl IntoIterator<Item = &'m Metrics>) -> Self {
        let mut metrics = Self::part();
        let mut occurrences = Vec::new();
        for child in children {
            metrics.height = metrics.height.max(child.height.saturating_add(1));
            metrics.size = metrics.size.saturating_add(child.size);
            occurrences.extend(
                child
                    .occurrences
                    .iter()
                    .map(|&(index, occurrence)| (index, occurrence.below(1, 1))),
            );
        }
        metrics.occurrences = merge_occurrences(occurrences);
        metrics
    }

    /// A named type of `summary`, whose parameters stand for `args`.
    fn named(summary: &RepresentationSummary, args: &[&Metrics]) -> Self {
        let mut shape = Self {
            height: summary.height,
            size: summary.size,
            occurrences: Vec::new(),
        };
        for (&RepresentationParam { depth, count }, arg) in summary.params.iter().zip(args) {
            shape.size = shape.size.saturating_add(count.saturating_mul(arg.size));
            if let Some(depth) = depth {
                shape.height = shape.height.max(depth.saturating_add(arg.height));
                shape.occurrences.extend(
                    arg.occurrences
                        .iter()
                        .map(|&(index, occurrence)| (index, occurrence.below(depth, count))),
                );
            }
        }
        shape.occurrences = merge_occurrences(shape.occurrences);
        Self::above([&shape])
    }

    /// A group of mutually recursive types, of which `members` are the metrics of each with the
    /// others counting as nothing: a walk goes through each at most once.
    fn group(members: &[Metrics]) -> Self {
        let height = members
            .iter()
            .fold(0u32, |height, member| height.saturating_add(member.height));
        let size = members
            .iter()
            .fold(0u32, |size, member| size.saturating_add(member.size));
        let occurrences = members
            .iter()
            .flat_map(|member| &member.occurrences)
            .map(|&(index, Occurrence { count, .. })| {
                (
                    index,
                    Occurrence {
                        depth: height,
                        count,
                    },
                )
            })
            .collect();
        Self {
            height,
            size,
            occurrences: merge_occurrences(occurrences),
        }
    }

    /// The summary of a definition of `params` parameters.
    fn into_summary(self, params: usize) -> RepresentationSummary {
        let mut summary = RepresentationSummary {
            height: self.height,
            size: self.size,
            params: vec![RepresentationParam::default(); params].into(),
        };
        for (index, Occurrence { depth, count }) in self.occurrences {
            summary.params[index] = RepresentationParam {
                depth: Some(depth),
                count,
            };
        }
        summary
    }
}

/// A walk went deeper than a representation within the height limit can be high.
struct BeyondHeight;

/// Sort `occurrences` by parameter and merge those of a same parameter.
fn merge_occurrences(mut occurrences: Vec<(usize, Occurrence)>) -> Vec<(usize, Occurrence)> {
    occurrences.sort_unstable_by_key(|&(index, _)| index);
    occurrences.dedup_by(|(index, occurrence), (kept_index, kept)| {
        *index == *kept_index && {
            kept.depth = kept.depth.max(occurrence.depth);
            kept.count = kept.count.saturating_add(occurrence.count);
            true
        }
    });
    occurrences
}

impl<'a, E: TypeDefEnv> RepresentationMetrics<'a, E> {
    pub(crate) fn new(env: &'a E) -> Self {
        Self::summarizing(env, &[], None)
    }

    fn summarizing(
        env: &'a E,
        params: &'a [TypeVar],
        group: Option<&'a FxHashSet<TypeDefId>>,
    ) -> Self {
        Self {
            env,
            params: params
                .iter()
                .enumerate()
                .map(|(index, &param)| (param, index))
                .collect(),
            group,
            done: FxHashMap::default(),
            stack: Vec::new(),
            low: FxHashMap::default(),
        }
    }

    /// The height and the size of the representation of `ty`, the size counting a repeated part
    /// at each occurrence.
    pub(crate) fn height_and_size(&mut self, ty: Type) -> (u32, u32) {
        if self.params.is_empty() && is_representation_leaf(ty) {
            return (1, 1);
        }
        let metrics = self.metrics(ty);
        (metrics.height, metrics.size)
    }

    fn metrics(&mut self, ty: Type) -> Metrics {
        let ty = erase_type_effects(ty);
        if !self.done.contains_key(&ty) && self.walk(ty, 1).is_err() {
            // The groups it left incomplete are not measured; those it completed are.
            self.stack.clear();
            self.low.clear();
            return Metrics::beyond_height();
        }
        self.done[&ty].clone()
    }

    /// Whether the walk measures the shape of the named type `named`: if an argument at a parameter
    /// that occurs is on a cycle. A definition beyond the limits is reported at its definition, and
    /// counts as its summary until then.
    fn expands(&self, named: &NamedType) -> bool {
        let summary = &self.env.type_def(named.def).representation;
        !self.group.is_some_and(|group| group.contains(&named.def))
            && summary.height <= REPRESENTATION_HEIGHT_LIMIT
            && summary.size <= REPRESENTATION_SIZE_LIMIT
            && named
                .params
                .iter()
                .zip(&summary.params)
                .any(|(arg, param)| param.depth.is_some() && arg.is_global_recursive())
    }

    /// How the walk measures `ty`, and its children: for a named type that [`Self::expands`], its
    /// shape given its arguments.
    fn visit(&self, ty: Type) -> Visit {
        let kind = ty.data().clone();
        let (measure, children) = match kind {
            TypeKind::Variable(var) => match self.params.get(&var) {
                Some(&index) => (Measure::Param(index), Vec::new()),
                None => (Measure::Part, Vec::new()),
            },
            TypeKind::Named(named)
                if self.group.is_some_and(|group| group.contains(&named.def)) =>
            {
                (Measure::Part, Vec::new())
            }
            TypeKind::Named(named) if self.expands(&named) => {
                let type_def = self.env.type_def(named.def);
                let effects = vec![EffType::empty(); type_def.effect_param_count()];
                let shape = type_def.instantiated_shape_with_effects(&named.params, &effects);
                (Measure::Above, vec![erase_type_effects(shape)])
            }
            TypeKind::Named(named) => {
                let children = occurring_args(&named, self.env);
                (Measure::Summary(named), children)
            }
            TypeKind::Tuple(members) => (Measure::Above, members),
            TypeKind::Record(fields) | TypeKind::Variant(fields) => (
                Measure::Above,
                fields.into_iter().map(|(_, ty)| ty).collect(),
            ),
            TypeKind::Native(_)
            | TypeKind::Function(_)
            | TypeKind::Subscript(_)
            | TypeKind::Never => (Measure::Part, Vec::new()),
        };
        Visit {
            ty,
            measure,
            children,
        }
    }

    /// Walk the type graph of `ty`, `depth` types deep.
    ///
    /// Each type on the path of the walk is at least one level of the representation above the
    /// next, but a parameter, which counts as none and has no children. So a walk deeper than one
    /// more than the height limit measures a representation beyond the limit: it stops there,
    /// before shapes composed through aliases make it as deep as they are high.
    fn walk(&mut self, ty: Type, depth: u32) -> Result<(), BeyondHeight> {
        if depth > REPRESENTATION_HEIGHT_LIMIT + 1 {
            return Err(BeyondHeight);
        }
        let index = self.stack.len();
        let mut visit = self.visit(ty);
        let children = std::mem::take(&mut visit.children);
        self.stack.push(visit);
        self.low.insert(ty, index);
        for &child in &children {
            if self.done.contains_key(&child) {
                continue;
            }
            if !self.low.contains_key(&child) {
                self.walk(child, depth + 1)?;
            }
            // A child still on the stack is in the group of this type.
            if let Some(&child_low) = self.low.get(&child) {
                let low = self.low.get_mut(&ty).expect("a type on the stack");
                *low = (*low).min(child_low);
            }
        }
        self.stack[index].children = children;
        if self.low[&ty] != index {
            return Ok(());
        }
        let group = self.stack.split_off(index);
        for member in &group {
            self.low.remove(&member.ty);
        }
        let metrics = if let [visit] = &group[..]
            && !visit.children.contains(&ty)
        {
            self.node_metrics(visit)
        } else {
            // The other types of the group count as nothing in each: the group counts each once.
            let members = group
                .iter()
                .map(|member| self.node_metrics(member))
                .collect::<Vec<_>>();
            Metrics::group(&members)
        };
        for member in group {
            self.done.insert(member.ty, metrics.clone());
        }
        Ok(())
    }

    /// The metrics of a visited type from those of its children, of which those not done are in
    /// its group, and count as nothing.
    fn node_metrics(&self, visit: &Visit) -> Metrics {
        let none = Metrics::default();
        let child = |child: &Type| self.done.get(child).unwrap_or(&none);
        match &visit.measure {
            Measure::Param(index) => Metrics::param(*index),
            Measure::Part => Metrics::part(),
            Measure::Above => Metrics::above(visit.children.iter().map(child)),
            // An argument at a parameter that does not occur is not walked, and counts as nothing.
            Measure::Summary(named) => {
                let args = named.params.iter().map(child).collect::<Vec<_>>();
                let type_def = self.env.type_def(named.def);
                Metrics::named(&type_def.representation, &args)
            }
        }
    }
}

/// Whether `ty` is a leaf of representations, whose layout does not depend on what it holds.
fn is_representation_leaf(ty: Type) -> bool {
    matches!(
        &*ty.data(),
        TypeKind::Variable(_)
            | TypeKind::Native(_)
            | TypeKind::Function(_)
            | TypeKind::Subscript(_)
            | TypeKind::Never
    )
}

/// The children of `ty` in its representation: the members of a product or a variant, the arguments
/// of a named type at the parameters that occur in its definition's representation, and none for a
/// leaf.
fn representation_children(ty: Type, env: &impl TypeDefEnv) -> Vec<Type> {
    match &*ty.data() {
        TypeKind::Tuple(members) => members.clone(),
        TypeKind::Record(fields) | TypeKind::Variant(fields) => {
            fields.iter().map(|(_, ty)| *ty).collect()
        }
        TypeKind::Named(named) => occurring_args(named, env),
        TypeKind::Variable(_)
        | TypeKind::Native(_)
        | TypeKind::Function(_)
        | TypeKind::Subscript(_)
        | TypeKind::Never => Vec::new(),
    }
}

/// The arguments of `named` at the parameters that occur in its definition's representation.
fn occurring_args(named: &NamedType, env: &impl TypeDefEnv) -> Vec<Type> {
    let params = &env.type_def(named.def).representation.params;
    named
        .params
        .iter()
        .zip(params)
        .filter(|(_, param)| param.depth.is_some())
        .map(|(&arg, _)| arg)
        .collect()
}

/// Summarize the representations of the type definitions of `module`, each after those it names:
/// those of other modules are summarized already.
pub(crate) fn summarize_module_type_defs(module: &mut Module, others: &Modules) {
    let ids = module.type_def_ids().collect::<Vec<_>>();
    let graph = representation_graph(module, others, &ids);
    for group in find_strongly_connected_components(&graph) {
        let recursive = group.len() > 1 || graph[group[0]].0.contains(&group[0]);
        let defs = group.iter().map(|&index| ids[index]).collect::<Vec<_>>();
        let summaries = summarize_type_defs(&defs, recursive, &ModuleEnv::new(module, others));
        for (def, summary) in defs.into_iter().zip(summaries) {
            module.type_def_mut(def).representation = summary;
        }
    }
}

/// For each definition `ids` of `module`, in order, the indices of those of `module` that its
/// representation reaches.
///
/// An argument of a named type is part of the representation where its parameter occurs in that of
/// the definition, which is not summarized yet for one of `module`. So the walks of all the shapes
/// run together, and enter such an argument once its parameter is found to occur: they go through
/// each part of each shape once.
fn representation_graph(module: &Module, others: &Modules, ids: &[TypeDefId]) -> Vec<DepGraphNode> {
    let env = ModuleEnv::new(module, others);
    let params = ids
        .iter()
        .enumerate()
        .flat_map(|(def, &id)| {
            let params = &module.type_def(id).shape.ty_quantifiers;
            params
                .iter()
                .enumerate()
                .map(move |(index, &param)| ((def, param), index))
        })
        .collect::<FxHashMap<_, _>>();
    let mut occurring = FxHashSet::default();
    // The arguments at parameters not known to occur yet, with the definition of their shape.
    let mut waiting = FxHashMap::<(usize, usize), Vec<(usize, Type)>>::default();
    let mut walked = FxHashSet::default();
    let mut reached = vec![Vec::new(); ids.len()];
    let mut pending = ids
        .iter()
        .enumerate()
        .map(|(def, &id)| (def, module.type_def(id).shape_ty()))
        .collect::<Vec<_>>();
    while let Some((def, ty)) = pending.pop() {
        if !walked.insert((def, ty)) {
            continue;
        }
        let kind = ty.data().clone();
        match kind {
            TypeKind::Variable(var) => {
                if let Some(&index) = params.get(&(def, var))
                    && occurring.insert((def, index))
                {
                    pending.extend(waiting.remove(&(def, index)).into_iter().flatten());
                }
            }
            TypeKind::Named(named) if named.def.module == module.module_id() => {
                let other = named.def.index.as_index();
                reached[def].push(other);
                for (index, arg) in named.params.into_iter().enumerate() {
                    if occurring.contains(&(other, index)) {
                        pending.push((def, arg));
                    } else {
                        waiting.entry((other, index)).or_default().push((def, arg));
                    }
                }
            }
            _ => pending.extend(
                representation_children(ty, &env)
                    .into_iter()
                    .map(|child| (def, child)),
            ),
        }
    }
    reached.into_iter().map(DepGraphNode).collect()
}

/// The summaries of the representations of the definitions `defs`, a group of mutually recursive
/// ones if `recursive`, from the summaries of the definitions they name.
fn summarize_type_defs(
    defs: &[TypeDefId],
    recursive: bool,
    env: &impl TypeDefEnv,
) -> Vec<RepresentationSummary> {
    let members = recursive.then(|| defs.iter().copied().collect::<FxHashSet<_>>());
    let locals = defs
        .iter()
        .map(|&def| {
            let type_def = env.type_def(def);
            let params = &type_def.shape.ty_quantifiers;
            RepresentationMetrics::summarizing(env, params, members.as_ref())
                .metrics(type_def.shape_ty())
        })
        .collect::<Vec<_>>();
    let arity = |def: TypeDefId| env.type_def(def).shape.ty_quantifiers.len();
    let Some(members) = members else {
        return defs
            .iter()
            .zip(locals)
            .map(|(&def, local)| local.into_summary(arity(def)))
            .collect();
    };
    // A walk goes through each definition of the group at most once, carrying its parameters
    // along: each member has the group's height and size. When the group is regular, as source
    // groups are, each member passes its parameters unchanged to the others, so a parameter occurs
    // as often as all members' parameters at its position, as deep as the group.
    let group = Metrics::group(&locals);
    if is_regular_group(defs, &members, env) {
        return defs
            .iter()
            .map(|&def| group.clone().into_summary(arity(def)))
            .collect();
    }
    // Otherwise each parameter stands for any of them.
    let count = group
        .occurrences
        .iter()
        .fold(0u32, |total, (_, occurrence)| {
            total.saturating_add(occurrence.count)
        });
    let param = RepresentationParam {
        depth: (!group.occurrences.is_empty()).then_some(group.height),
        count,
    };
    defs.iter()
        .map(|&def| RepresentationSummary {
            height: group.height,
            size: group.size,
            params: vec![param; arity(def)].into(),
        })
        .collect()
}

/// Whether, in the shapes of the group of mutually recursive definitions `defs`, every reference
/// to one of them, a member of `group`, passes the referring definition's parameters unchanged.
fn is_regular_group(
    defs: &[TypeDefId],
    group: &FxHashSet<TypeDefId>,
    env: &impl TypeDefEnv,
) -> bool {
    defs.iter().all(|&def| {
        let type_def = env.type_def(def);
        let params = &type_def.shape.ty_quantifiers;
        let mut pending = vec![type_def.shape_ty()];
        let mut seen = FxHashSet::default();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if let TypeKind::Named(named) = &*ty.data()
                && group.contains(&named.def)
                && (named.params.len() != params.len()
                    || !named.params.iter().zip(params).all(|(arg, &param)| {
                        matches!(&*arg.data(), TypeKind::Variable(var) if *var == param)
                    }))
            {
                return false;
            }
            pending.extend(representation_children(ty, env));
        }
        true
    })
}

/// The height and the size of the representation of a definition, its parameters being leaves: the
/// largest of those of its named type and of the parts of its shape. The shape is the named type's
/// representation, not the type of values of its own; a part of the shape of a recursive one, such
/// as a payload, is, and can be higher.
pub(crate) fn type_def_representation_metrics(
    type_def: &TypeDef,
    env: &impl TypeDefEnv,
) -> (u32, u32) {
    let summary = &type_def.representation;
    let named_height = summary
        .params
        .iter()
        .filter_map(|param| param.depth)
        .fold(summary.height, |height, depth| {
            height.max(depth.saturating_add(1))
        })
        .saturating_add(1);
    let named_size = summary
        .params
        .iter()
        .fold(summary.size, |size, param| size.saturating_add(param.count))
        .saturating_add(1);
    let mut parts = RepresentationMetrics::new(env);
    representation_children(type_def.shape_ty(), env)
        .into_iter()
        .map(|part| parts.metrics(part))
        .fold((named_height, named_size), |(height, size), part| {
            (height.max(part.height), size.max(part.size))
        })
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::*;
    use crate::{
        CompilerSession,
        std::{math::int_type, ordering::ordering_type, string::string_type},
    };

    /// The two environments must agree, or a type would be copyable during elaboration and not
    /// during optimization — the property they share is the whole point of the abstraction.
    #[test]
    fn the_module_env_agrees_with_the_trait_solver() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let ordering = ordering_type();
        for (ty, expected) in [
            (int_type(), true),
            (Type::unit(), true),
            (ordering, true),
            (string_type(), false),
            (Type::tuple([int_type(), int_type()]), true),
            (Type::tuple([int_type(), string_type()]), false),
            (Type::variant([(ustr("Some"), int_type())]), true),
            (Type::variant([(ustr("Some"), string_type())]), false),
        ] {
            assert_eq!(concrete_type_is_trivial_copy(ty, &env), expected, "{ty:?}");
        }
    }
}
