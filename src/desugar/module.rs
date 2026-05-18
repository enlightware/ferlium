use crate::compiler::error::InvalidRecursiveTypeKind;
use crate::desugar::types::{
    RecursiveAliasRef, RecursiveTypeBuilder, desugar_type_constraints, extend_generic_ty_params,
};
use crate::hir::function::FunctionDefinition;
use crate::types::r#trait::{Trait, TraitMethodSpans, TraitRef, TraitSpans, TraitValidationError};

use super::expr::desugar;
use super::*;

/// A reference to name of a type, either an alias or a definition, in parsed AST.
enum NamedTypeData {
    Alias(UstrSpan, Vec<UstrSpan>, PTypeSpan),
    Def(PTypeDef),
}
impl NamedTypeData {
    fn name(&self) -> Ustr {
        use NamedTypeData::*;
        match self {
            Alias(name, _, _) => name.0,
            Def(def) => def.name.0,
        }
    }
    fn name_span(&self) -> Location {
        use NamedTypeData::*;
        match self {
            Alias(name, _, _) => name.1,
            Def(def) => def.name.1,
        }
    }
    fn generic_params(&self) -> &[UstrSpan] {
        use NamedTypeData::*;
        match self {
            Alias(_, generic_params, _) => generic_params,
            Def(def) => &def.generic_params,
        }
    }

    /// Summarizes the local named-type references made by this alias or type definition.
    fn cycle_info(&self, ty_names: &FxHashMap<Ustr, usize>) -> TypeCycleInfo {
        let mut info = TypeCycleInfo::default();
        match self {
            NamedTypeData::Alias(_, _, alias) => {
                info.collect_from_type(&alias.0, ty_names, false);
            }
            NamedTypeData::Def(def) => {
                // Type definitions depend on both their shape and their where-clause
                // types. Bounds can mention local named types too, so they must take
                // part in the same dependency graph.
                info.collect_from_type(&def.shape, ty_names, false);
                for constraint in &def.where_clause {
                    for input in &constraint.input_types {
                        info.collect_from_type(&input.ty.0, ty_names, false);
                    }
                    for output in &constraint.output_types {
                        info.collect_from_type(&output.ty.0, ty_names, false);
                    }
                }
            }
        }
        info
    }

    /// Rejects non-regular generic references to declarations in the same recursive SCC.
    fn validate_regular_recursive_generic_refs(
        &self,
        scc_set: &FxHashSet<usize>,
        ty_names: &FxHashMap<Ustr, usize>,
        ty_refs: &[NamedTypeData],
    ) -> Result<(), InternalCompilationError> {
        match self {
            NamedTypeData::Alias(_, generic_params, alias) => {
                validate_regular_generic_refs_in_type(
                    &alias.0,
                    alias.1,
                    generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )
            }
            NamedTypeData::Def(def) => {
                validate_regular_generic_refs_in_type(
                    &def.shape,
                    def.span,
                    &def.generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )?;
                for constraint in &def.where_clause {
                    for input in &constraint.input_types {
                        validate_regular_generic_refs_in_type(
                            &input.ty.0,
                            input.ty.1,
                            &def.generic_params,
                            scc_set,
                            ty_names,
                            ty_refs,
                        )?;
                    }
                    for output in &constraint.output_types {
                        validate_regular_generic_refs_in_type(
                            &output.ty.0,
                            output.ty.1,
                            &def.generic_params,
                            scc_set,
                            ty_names,
                            ty_refs,
                        )?;
                    }
                }
                Ok(())
            }
        }
    }

    /// Lowers this non-recursive named type after its local dependencies have been inserted.
    fn desugar_acyclic(
        &self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<DesugaredNamedType, InternalCompilationError> {
        // Acyclic declarations can be lowered directly because topological ordering
        // guarantees that every local dependency has already been inserted into the
        // output module.
        Ok(match self {
            NamedTypeData::Alias(name, generic_params, alias) => {
                let generic_ty_params = extend_generic_ty_params(
                    &GenericTyParams::default(),
                    generic_params,
                    GenericParamsOwner::TypeAlias { name: name.0 },
                )?;
                let ty_var_count = generic_params.len() as u32;
                let param_names: Vec<_> = generic_params.iter().map(|(name, _)| *name).collect();
                let ty = alias.0.desugar_with_ty_params(
                    alias.1,
                    false,
                    env,
                    &generic_ty_params,
                    modules_used,
                )?;
                DesugaredNamedType::Alias(*name, param_names, ty_var_count, ty)
            }
            NamedTypeData::Def(def) => {
                DesugaredNamedType::Def(def.name.0, def.desugar(env, modules_used)?)
            }
        })
    }
}

/// Returns whether `args` is exactly `<T, U, ...>` for the current declaration's parameters.
fn is_regular_recursive_generic_application(
    current_generic_params: &[UstrSpan],
    target_generic_params: &[UstrSpan],
    args: &[ast::TypeSpan<Parsed>],
) -> bool {
    target_generic_params.len() == current_generic_params.len()
        && args.len() == current_generic_params.len()
        && args
            .iter()
            .zip(current_generic_params)
            .all(|((arg, _), (expected_name, _))| match arg {
                ast::PType::Path(path) => {
                    matches!(&path.segments[..], [(name, _)] if name == expected_name)
                }
                _ => false,
            })
}

/// Walks a parsed type and checks same-SCC generic applications for regular recursive shape.
fn validate_regular_generic_refs_in_type(
    ty: &ast::PType,
    span: Location,
    current_generic_params: &[UstrSpan],
    scc_set: &FxHashSet<usize>,
    ty_names: &FxHashMap<Ustr, usize>,
    ty_refs: &[NamedTypeData],
) -> Result<(), InternalCompilationError> {
    use ast::PType::*;
    match ty {
        AppliedPath { path, args } => {
            // For now, recursive generic SCCs must be regular: every recursive
            // application of a generic declaration in the SCC must pass the
            // current declaration's type parameters through unchanged. This
            // rejects shapes such as `Tree<T> = Leaf | Node(Tree<(T, T)>)`,
            // which would otherwise require recursive type-level computation.
            if let [(name, _)] = &path.segments[..]
                && let Some(target_index) = ty_names.get(name)
                && scc_set.contains(target_index)
            {
                let target_generic_params = ty_refs[*target_index].generic_params();
                if !target_generic_params.is_empty()
                    && !is_regular_recursive_generic_application(
                        current_generic_params,
                        target_generic_params,
                        args,
                    )
                {
                    return Err(internal_compilation_error!(InvalidRecursiveType {
                        kind: InvalidRecursiveTypeKind::NonRegularGenericShape { name: *name },
                        span,
                    }));
                }
            }
            for (arg, arg_span) in args {
                validate_regular_generic_refs_in_type(
                    arg,
                    *arg_span,
                    current_generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )?;
            }
        }
        Variant(variants) => {
            for (_, (payload, payload_span)) in variants {
                validate_regular_generic_refs_in_type(
                    payload,
                    *payload_span,
                    current_generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )?;
            }
        }
        Tuple(elements) => {
            for (element, element_span) in elements {
                validate_regular_generic_refs_in_type(
                    element,
                    *element_span,
                    current_generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )?;
            }
        }
        Record(fields) => {
            for (_, (field, field_span)) in fields {
                validate_regular_generic_refs_in_type(
                    field,
                    *field_span,
                    current_generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )?;
            }
        }
        Array(inner) => validate_regular_generic_refs_in_type(
            &inner.0,
            inner.1,
            current_generic_params,
            scc_set,
            ty_names,
            ty_refs,
        )?,
        Function(fn_type) => {
            for arg in &fn_type.args {
                validate_regular_generic_refs_in_type(
                    &arg.ty.0,
                    arg.ty.1,
                    current_generic_params,
                    scc_set,
                    ty_names,
                    ty_refs,
                )?;
            }
            validate_regular_generic_refs_in_type(
                &fn_type.ret.0,
                fn_type.ret.1,
                current_generic_params,
                scc_set,
                ty_names,
                ty_refs,
            )?;
        }
        Never | Unit | Resolved(_) | Infer | Path(_) => {}
    }
    Ok(())
}

/// Per-declaration summary used to classify recursive type SCCs.
///
/// References are split by whether they are guarded by a sum type. Variant payload
/// reference sets are kept separately so termination can be checked relative to
/// the current SCC.
#[derive(Default)]
struct TypeCycleInfo {
    guarded_refs: FxHashSet<usize>,
    unguarded_refs: FxHashSet<usize>,
    variant_payload_refs: Vec<FxHashSet<usize>>,
}

impl TypeCycleInfo {
    /// Collects local named-type references from one parsed type, noting whether they cross a sum boundary.
    fn collect_from_type(
        &mut self,
        ty: &ast::PType,
        ty_names: &FxHashMap<Ustr, usize>,
        guarded: bool,
    ) {
        use ast::PType::*;
        match ty {
            Path(path) => {
                if let [(name, _)] = &path.segments[..]
                    && let Some(index) = ty_names.get(name)
                {
                    if guarded {
                        self.guarded_refs.insert(*index);
                    } else {
                        self.unguarded_refs.insert(*index);
                    }
                }
            }
            AppliedPath { path, args } => {
                // A generic use such as `List<T>` contributes the same dependency as
                // `List`; its arguments may contribute additional local dependencies.
                if let [(name, _)] = &path.segments[..]
                    && let Some(index) = ty_names.get(name)
                {
                    if guarded {
                        self.guarded_refs.insert(*index);
                    } else {
                        self.unguarded_refs.insert(*index);
                    }
                }
                for (arg, _) in args {
                    self.collect_from_type(arg, ty_names, guarded);
                }
            }
            Variant(variants) => {
                for (_, (payload, _)) in variants {
                    // Entering a variant payload crosses a sum boundary. A recursive
                    // reference below this point is guarded by the sum type, and each
                    // payload is tracked independently so we can later prove that at
                    // least one branch terminates outside the current SCC.
                    let mut payload_info = TypeCycleInfo::default();
                    payload_info.collect_from_type(payload, ty_names, true);
                    let payload_refs = payload_info.refs();
                    self.guarded_refs.extend(payload_info.guarded_refs);
                    self.unguarded_refs.extend(payload_info.unguarded_refs);
                    self.variant_payload_refs.push(payload_refs);
                }
            }
            Tuple(elements) => {
                for (element, _) in elements {
                    self.collect_from_type(element, ty_names, guarded);
                }
            }
            Record(fields) => {
                for (_, (field, _)) in fields {
                    self.collect_from_type(field, ty_names, guarded);
                }
            }
            Array(inner) => self.collect_from_type(&inner.0, ty_names, guarded),
            Function(fn_type) => {
                for arg in &fn_type.args {
                    self.collect_from_type(&arg.ty.0, ty_names, guarded);
                }
                self.collect_from_type(&fn_type.ret.0, ty_names, guarded);
            }
            Never | Unit | Resolved(_) | Infer => {}
        }
    }

    /// Returns all same-module named-type references found in this declaration.
    fn refs(&self) -> FxHashSet<usize> {
        self.guarded_refs
            .union(&self.unguarded_refs)
            .copied()
            .collect()
    }
}

/// Returns whether a one-node SCC is recursive through a self-edge.
fn is_recursive_singleton(index: usize, deps: &[DepGraphNode]) -> bool {
    deps[index].0.contains(&index)
}

/// Rejects recursive SCCs that are product-only or have no terminating sum branch.
fn validate_type_cycle(
    scc: &[usize],
    ty_refs: &[NamedTypeData],
    cycle_infos: &[TypeCycleInfo],
    ty_names: &FxHashMap<Ustr, usize>,
) -> Result<(), InternalCompilationError> {
    // We accept recursive types only when recursion is guarded by at least one
    // sum type. To check that, restrict the dependency graph to unguarded edges
    // inside this SCC. Any cycle that remains is a product-only infinite type:
    // examples are `type A = A`, mutually recursive structs, or recursion through
    // tuples/records/functions without crossing a variant.
    let scc_set = scc.iter().copied().collect::<FxHashSet<_>>();
    let scc_pos = scc
        .iter()
        .copied()
        .enumerate()
        .map(|(pos, index)| (index, pos))
        .collect::<FxHashMap<_, _>>();
    let unguarded_graph = scc
        .iter()
        .map(|index| {
            DepGraphNode(
                cycle_infos[*index]
                    .unguarded_refs
                    .iter()
                    .copied()
                    .filter(|dep| scc_set.contains(dep))
                    .map(|dep| scc_pos[&dep])
                    .collect(),
            )
        })
        .collect::<Vec<_>>();
    let unguarded_sccs = find_strongly_connected_components(&unguarded_graph);
    for unguarded_scc in unguarded_sccs {
        if unguarded_scc.len() > 1
            || (unguarded_scc.len() == 1
                && unguarded_graph[unguarded_scc[0]]
                    .0
                    .contains(&unguarded_scc[0]))
        {
            let ty_ref = &ty_refs[scc[unguarded_scc[0]]];
            return Err(internal_compilation_error!(InfiniteType {
                kind: InfiniteTypeKind::ProductCycleWithoutSum {
                    name: ty_ref.name()
                },
                span: ty_ref.name_span(),
            }));
        }
    }

    // Guarded recursion is still not enough: the sum must have a terminating
    // branch. We accept the SCC when any variant payload in the cycle has no
    // reference back into the SCC, e.g. `Nil` in `Nil | Cons(T, List<T>)`.
    let has_terminating_variant = scc.iter().any(|index| {
        cycle_infos[*index]
            .variant_payload_refs
            .iter()
            .any(|refs| refs.is_disjoint(&scc_set))
    });
    if !has_terminating_variant {
        let ty_ref = &ty_refs[scc[0]];
        return Err(internal_compilation_error!(InfiniteType {
            kind: InfiniteTypeKind::SumCycleWithoutTerminatingVariant {
                name: ty_ref.name()
            },
            span: ty_ref.name_span(),
        }));
    }

    for index in scc {
        ty_refs[*index].validate_regular_recursive_generic_refs(&scc_set, ty_names, ty_refs)?;
    }

    Ok(())
}

/// Local named-type dependency graph for aliases and type definitions in one module.
///
/// `ty_refs` owns the declarations, `ty_dep_graph` stores their local dependency
/// edges by index, and `sccs` is the SCC partition used for dependency-ordered
/// desugaring and recursive-cycle handling.
struct NamedTypeGraph {
    ty_refs: Vec<NamedTypeData>,
    ty_dep_graph: Vec<DepGraphNode>,
    sccs: Vec<Vec<usize>>,
}

impl NamedTypeGraph {
    /// Lowers all named types in dependency order, using SCC-specific handling for recursive groups.
    fn desugar(
        self,
        output: &mut Module,
        others: &Modules,
    ) -> Result<FxHashSet<ModuleId>, InternalCompilationError> {
        let NamedTypeGraph {
            ty_refs,
            ty_dep_graph,
            sccs,
        } = self;

        // Process SCCs in dependency order. The graph edge direction points from a
        // declaration to the declarations it mentions, so we reverse the topological
        // SCC order before inserting declarations into the output module.
        let sorted_sccs = topological_sort_sccs(&ty_dep_graph, &sccs);
        let mut modules_used = FxHashSet::<ModuleId>::default();
        for scc in sorted_sccs.into_iter().rev() {
            let is_recursive = scc.len() > 1 || is_recursive_singleton(scc[0], &ty_dep_graph);

            if is_recursive {
                desugar_recursive_named_type_scc(
                    &scc,
                    &ty_refs,
                    output,
                    others,
                    &mut modules_used,
                )?;
                continue;
            }

            assert_eq!(scc.len(), 1);
            let desugared = {
                // Keep the immutable environment borrow short so the output module can
                // be updated after each acyclic declaration.
                let env = ModuleEnv::new(output, others);
                ty_refs[scc[0]].desugar_acyclic(&env, &mut modules_used)?
            };
            match desugared {
                DesugaredNamedType::Alias(name, param_names, ty_var_count, ty) => {
                    output.add_type_alias(name.0, param_names, ty_var_count, ty);
                }
                DesugaredNamedType::Def(name, type_def) => {
                    output.add_type_def(name, type_def);
                }
            }
        }
        Ok(modules_used)
    }
}

fn build_named_type_graph(
    type_aliases: Vec<ast::TypeAlias>,
    type_defs: Vec<PTypeDef>,
) -> Result<NamedTypeGraph, InternalCompilationError> {
    // First gather all local aliases and type definitions into a single indexed
    // list. `ty_names` maps source names back to those indices so dependency
    // collection can recognize same-module references without consulting the
    // partially built output module.
    let (ty_names, ty_refs): (FxHashMap<_, _>, Vec<_>) = type_aliases
        .into_iter()
        .map(|alias| {
            (
                alias.name.0,
                NamedTypeData::Alias(alias.name, alias.generic_params, alias.ty),
            )
        })
        .chain(
            type_defs
                .into_iter()
                .map(|def| (def.name.0, NamedTypeData::Def(def))),
        )
        .enumerate()
        .map(|(index, (name, ty_data))| ((name, index), ty_data))
        .unzip();

    // Build one dependency graph over all named types in the module. The graph
    // is used both to order acyclic declarations and to identify recursive SCCs
    // that need validation and special lowering.
    let cycle_infos = ty_refs
        .iter()
        .map(|ty_ref| ty_ref.cycle_info(&ty_names))
        .collect::<Vec<_>>();
    let ty_dep_graph = cycle_infos
        .iter()
        .map(|info| DepGraphNode(info.refs().into_iter().collect()))
        .collect::<Vec<_>>();
    let sccs = find_strongly_connected_components(&ty_dep_graph);

    // Validate every recursive SCC before lowering. This keeps semantic cycle
    // errors independent from the representation strategy used later for aliases
    // and nominal type definitions.
    for scc in &sccs {
        if scc.len() > 1 || is_recursive_singleton(scc[0], &ty_dep_graph) {
            validate_type_cycle(scc, &ty_refs, &cycle_infos, &ty_names)?;
        }
    }

    Ok(NamedTypeGraph {
        ty_refs,
        ty_dep_graph,
        sccs,
    })
}

/// Builds structural placeholder metadata for all aliases in one recursive SCC.
fn build_recursive_alias_refs(
    scc: &[usize],
    ty_refs: &[NamedTypeData],
) -> FxHashMap<Ustr, RecursiveAliasRef> {
    scc.iter()
        .filter_map(|&index| match &ty_refs[index] {
            NamedTypeData::Alias(name, generic_params, _) => Some((*name, generic_params)),
            NamedTypeData::Def(_) => None,
        })
        .enumerate()
        .map(|(local_index, (name, generic_params))| {
            (
                name.0,
                RecursiveAliasRef {
                    name: name.0,
                    index: local_index as u32,
                    param_names: generic_params.iter().map(|(name, _)| *name).collect(),
                    ty_var_count: generic_params.len() as u32,
                    span: name.1,
                },
            )
        })
        .collect()
}

/// Inserts unfilled nominal type-definition handles for all type definitions in one recursive SCC.
fn predeclare_recursive_type_defs(
    scc: &[usize],
    ty_refs: &[NamedTypeData],
    output: &mut Module,
) -> FxHashMap<Ustr, TypeDefId> {
    scc.iter()
        .filter_map(|&index| match &ty_refs[index] {
            NamedTypeData::Alias(..) => None,
            NamedTypeData::Def(def) => {
                let param_names = def.generic_params.iter().map(|(name, _)| *name).collect();
                let type_def = output.reserve_type_def(def.name.0, param_names, def.span);
                Some((def.name.0, type_def))
            }
        })
        .collect()
}

/// Lowers all aliases in a recursive SCC using structural alias slots and reserved type definitions.
fn desugar_recursive_aliases_in_scc(
    scc: &[usize],
    ty_refs: &[NamedTypeData],
    env: &ModuleEnv<'_>,
    modules_used: &mut FxHashSet<ModuleId>,
    alias_refs: &FxHashMap<Ustr, RecursiveAliasRef>,
    type_defs: &FxHashMap<Ustr, TypeDefId>,
) -> Result<Vec<(UstrSpan, Vec<UstrSpan>, Type)>, InternalCompilationError> {
    let mut root_tys = Vec::with_capacity(alias_refs.len());
    let mut root_entries = Vec::with_capacity(alias_refs.len());
    let mut builder =
        RecursiveTypeBuilder::new(alias_refs.len(), env, modules_used, alias_refs, type_defs);
    for &index in scc {
        let NamedTypeData::Alias(name, generic_params, alias) = &ty_refs[index] else {
            continue;
        };
        let alias_ref = &alias_refs[&name.0];
        // Each alias root gets its own generic parameter environment. Recursive
        // generic references are accepted only when they use that alias's own
        // parameters unchanged; non-regular recursive generic shapes are rejected
        // by `RecursiveTypeBuilder`.
        let generic_ty_params = extend_generic_ty_params(
            &GenericTyParams::default(),
            generic_params,
            GenericParamsOwner::TypeAlias { name: name.0 },
        )?;
        builder.set_generic_ty_params(generic_ty_params);
        let ty = builder.desugar_root(alias_ref.index, &alias.0, alias.1)?;
        root_tys.push(ty);
        root_entries.push((*name, generic_params.clone()));
    }
    let root_tys = builder.finish(&root_tys);
    Ok(root_entries
        .into_iter()
        .zip(root_tys)
        .map(|((name, generic_params), ty)| (name, generic_params, ty))
        .collect())
}

/// Fills all predeclared nominal type definitions in a recursive SCC.
fn fill_recursive_type_defs_in_scc(
    scc: &[usize],
    ty_refs: &[NamedTypeData],
    output: &mut Module,
    others: &Modules,
    modules_used: &mut FxHashSet<ModuleId>,
    type_defs: &FxHashMap<Ustr, TypeDefId>,
) -> Result<(), InternalCompilationError> {
    for &index in scc {
        let NamedTypeData::Def(def) = &ty_refs[index] else {
            continue;
        };
        let type_def = type_defs[&def.name.0];
        let desugared = {
            let env = ModuleEnv::new(output, others);
            def.desugar_data(&env, modules_used)?
        };
        output.fill_type_def(type_def, desugared);
    }
    Ok(())
}

/// Lowers one recursive named-type SCC by reserving aliases and type definitions before finalization.
fn desugar_recursive_named_type_scc(
    scc: &[usize],
    ty_refs: &[NamedTypeData],
    output: &mut Module,
    others: &Modules,
    modules_used: &mut FxHashSet<ModuleId>,
) -> Result<(), InternalCompilationError> {
    // Recursive SCC lowering has one common shape:
    //
    // 1. Reserve every name whose final value may be mentioned while the SCC is
    //    still being lowered.
    // 2. Lower structural aliases against those reservations.
    // 3. Publish the resolved aliases in the output module.
    // 4. Lower and fill nominal type definitions against the now-complete SCC.
    //
    // Pure alias SCCs are the degenerate case with no nominal reservations. Pure
    // type-def SCCs are the degenerate case with no structural alias slots. Mixed
    // SCCs use both mechanisms in the same pass.
    let alias_refs = build_recursive_alias_refs(scc, ty_refs);
    let type_defs = predeclare_recursive_type_defs(scc, ty_refs, output);

    if !alias_refs.is_empty() {
        // Recursive aliases are structural types, so recursive alias references
        // are represented as local placeholders while each alias root is
        // desugared. Type definitions in the same SCC have already been reserved
        // in the module, and are also passed directly to the builder so aliases
        // can refer to those nominal handles before their bodies are filled.
        let entries = {
            let env = ModuleEnv::new(output, others);
            desugar_recursive_aliases_in_scc(
                scc,
                ty_refs,
                &env,
                modules_used,
                &alias_refs,
                &type_defs,
            )?
        };
        for (name, generic_params, ty) in entries {
            output.add_type_alias(
                name.0,
                generic_params.iter().map(|(name, _)| *name).collect(),
                generic_params.len() as u32,
                ty,
            );
        }
    }

    if !type_defs.is_empty() {
        // Once aliases have been published, type definition bodies can resolve
        // aliases and nominal definitions from the same SCC through the normal
        // module environment.
        fill_recursive_type_defs_in_scc(scc, ty_refs, output, others, modules_used, &type_defs)?;
    }

    Ok(())
}

enum DesugaredNamedType {
    Alias(UstrSpan, Vec<Ustr>, u32, Type),
    Def(Ustr, HirTypeDef),
}

impl PModule {
    /// Desugars a parsed module and resolve its types and write them into output.
    /// Returns a desugared AST, the desugared expression arena, and a list of
    /// strongly connected components of its function dependency graph, sorted topologically.
    pub fn desugar(
        self,
        output: &mut Module,
        others: &Modules,
        parsed_arena: &PExprArena,
    ) -> Result<(DModule, DExprArena, FnSccs), InternalCompilationError> {
        // Flatten uses from self and check for conflicts with local definitions.
        let local_names = self.own_symbols().collect();
        let PModule {
            traits,
            functions,
            impls,
            type_aliases,
            type_defs,
            uses,
        } = self;

        let resolver = ModulesResolver::new(others);
        resolve_imports(&uses, &local_names, &resolver, &mut output.uses)?;

        let type_graph = build_named_type_graph(type_aliases, type_defs)?;
        let mut modules_used = type_graph.desugar(output, others)?;
        let mut env = ModuleEnv::new(output, others);

        for trait_def in traits {
            output.add_trait(trait_def.desugar(&env, &mut modules_used)?);
            env = ModuleEnv::new(output, others);
        }

        // Desugar functions
        let fn_map = functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<FxHashMap<_, _>>();
        let mut desugared_arena = new_desugared_arena_sized_from_parsed_arena(parsed_arena);
        let (functions, fn_dep_graph): (_, Vec<_>) = process_results(
            functions.into_iter().map(|f| {
                f.desugar(
                    &fn_map,
                    &env,
                    parsed_arena,
                    &mut desugared_arena,
                    &mut modules_used,
                )
            }),
            |iter| iter.unzip(),
        )?;
        let sccs = find_strongly_connected_components(&fn_dep_graph);
        let sorted_sccs = topological_sort_sccs(&fn_dep_graph, &sccs);

        // Desugar trait implementations
        let impls = impls
            .into_iter()
            .map(|i| i.desugar(&env, parsed_arena, &mut desugared_arena, &mut modules_used))
            .collect::<Result<_, _>>()?;

        // Build result
        output.type_deps.extend(modules_used);
        let module = DModule {
            traits: vec![],
            functions,
            impls,
            type_aliases: vec![],
            type_defs: vec![],
            uses,
        };
        Ok((module, desugared_arena, sorted_sccs))
    }
}

impl ast::TraitDefinition {
    pub fn desugar(
        self,
        env: &ModuleEnv<'_>,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<TraitRef, InternalCompilationError> {
        let generic_params = self
            .input_type_names
            .iter()
            .chain(self.output_type_names.iter())
            .copied()
            .collect::<Vec<_>>();
        let generic_ty_params = extend_generic_ty_params(
            &GenericTyParams::default(),
            &generic_params,
            GenericParamsOwner::Trait { name: self.name.0 },
        )?;
        let constraints =
            desugar_type_constraints(&self.where_clause, &generic_ty_params, env, modules_used)?;
        let method_spans = self
            .methods
            .iter()
            .map(|function| function.spans())
            .collect();
        let spans = self.spans(method_spans);
        let input_type_names = self.iter_input_type_names().collect();
        let output_type_names = self.iter_output_type_names().collect();
        let methods = self
            .methods
            .into_iter()
            .map(|function| function.desugar(env, &generic_ty_params, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        let trait_span = self.span;
        TraitRef::from_trait_data(Trait {
            module_id: None,
            name: self.name.0,
            doc: self.doc,
            input_type_names,
            output_type_names,
            constraints,
            methods,
            associated_consts: vec![],
            derivers: vec![],
            impl_policy: crate::types::r#trait::TraitImplPolicy::UserImplementable,
            spans: Some(spans),
        })
        .map_err(|error| match error {
            TraitValidationError::Invalid { trait_name, kind } => {
                internal_compilation_error!(InvalidTraitDefinition {
                    trait_name,
                    kind,
                    span: trait_span,
                })
            }
            TraitValidationError::Unsupported { trait_name, kind } => {
                internal_compilation_error!(UnsupportedTraitDefinition {
                    trait_name,
                    kind,
                    span: trait_span,
                })
            }
        })
    }
}

impl ast::TraitMethod {
    fn spans(&self) -> TraitMethodSpans {
        TraitMethodSpans {
            name: self.name.1,
            args: self
                .args
                .iter()
                .map(|arg| (arg.name.1, arg.ty.span))
                .collect(),
            ret_ty: self.ret_ty.as_ref().map(|(_, span)| *span),
            span: self.span,
        }
    }

    fn desugar(
        self,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<(Ustr, FunctionDefinition), InternalCompilationError> {
        let args = self
            .args
            .iter()
            .map(|arg| {
                arg.ty
                    .desugar_with_ty_params(env, generic_ty_params, modules_used)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.ret_ty.map_or_else(
            || Ok(Type::unit()),
            |(ret_ty, span)| {
                ret_ty.desugar_with_ty_params(span, false, env, generic_ty_params, modules_used)
            },
        )?;
        use ast::PFnEffects::*;
        let effects = match self.effects {
            ImplicitPure => EffType::empty(),
            ImplicitGeneric => EffType::single_variable_id(0),
            Explicit(effects) => EffType::multiple_primitive(&effects),
        };
        let fn_ty = FnType::new(args, ret, effects);
        Ok((
            self.name.0,
            FunctionDefinition::new(
                TypeScheme::new_infer_quantifiers(fn_ty),
                self.args.into_iter().map(|arg| arg.name.0).collect(),
                self.doc,
            ),
        ))
    }
}

impl ast::TraitDefinition {
    fn spans(&self, methods: Vec<TraitMethodSpans>) -> TraitSpans {
        TraitSpans {
            name: self.name.1,
            input_type_names: self
                .input_type_names
                .iter()
                .map(|(_, span)| *span)
                .collect(),
            output_type_names: self
                .output_type_names
                .iter()
                .map(|(_, span)| *span)
                .collect(),
            constraints: self
                .where_clause
                .iter()
                .map(|constraint| constraint.span)
                .collect(),
            methods,
            span: self.span,
        }
    }
}

impl PModuleFunction {
    pub fn desugar(
        self,
        fn_map: &FnMap,
        env: &ModuleEnv<'_>,
        parsed_arena: &PExprArena,
        desugared_arena: &mut DExprArena,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<(DModuleFunction, DepGraphNode), InternalCompilationError> {
        let generic_ty_params = GenericTyParams::default();
        self.desugar_with_ty_params(
            fn_map,
            env,
            &generic_ty_params,
            parsed_arena,
            desugared_arena,
            modules_used,
        )
    }

    pub(crate) fn desugar_with_ty_params(
        self,
        fn_map: &FnMap,
        env: &ModuleEnv<'_>,
        generic_ty_params: &GenericTyParams,
        parsed_arena: &PExprArena,
        desugared_arena: &mut DExprArena,
        modules_used: &mut FxHashSet<ModuleId>,
    ) -> Result<(DModuleFunction, DepGraphNode), InternalCompilationError> {
        let generic_ty_params = extend_generic_ty_params(
            generic_ty_params,
            &self.generic_params,
            GenericParamsOwner::Function { name: self.name.0 },
        )?;
        // Collect mut-binding arg info before args are consumed.
        let mut_binding_args: Vec<UstrSpan> = self
            .args
            .iter()
            .filter(|arg| arg.mut_binding)
            .map(|arg| arg.name)
            .collect();
        let locals = self.args.iter().map(|arg| arg.name.0).collect();
        let mut ctx = DesugarCtx::new_with_locals(fn_map, locals, env, &generic_ty_params);
        let body = desugar(
            self.body,
            &mut ctx,
            parsed_arena,
            desugared_arena,
            modules_used,
        )?;
        // Desugar `mut x` parameters by prepending `let mut x = x;` to the body.
        // This rebinds each such parameter as a mutable local, shadowing the immutable arg,
        // without changing the function's external signature.
        let body = if mut_binding_args.is_empty() {
            body
        } else {
            let body_span = desugared_arena[body].span;
            let mut stmts: Vec<DExprId> = Vec::with_capacity(mut_binding_args.len() + 1);
            for name in &mut_binding_args {
                let span = name.1;
                let arg_ref = desugared_arena.alloc(DExpr::new(
                    ExprKind::identifier(Path::single(name.0, span)),
                    span,
                ));
                let let_mut = desugared_arena.alloc(DExpr::new(
                    ExprKind::let_(
                        DLetPattern::binding(*name, MutVal::mutable()),
                        arg_ref,
                        None,
                    ),
                    span,
                ));
                stmts.push(let_mut);
            }
            stmts.push(body);
            desugared_arena.alloc(DExpr::new(ExprKind::block(stmts), body_span))
        };
        let args = self
            .args
            .into_iter()
            .map(|arg| arg.desugar_with_ty_params(env, &generic_ty_params, modules_used))
            .collect::<Result<Vec<_>, _>>()?;
        // Collect function dependencies
        let ret_ty = self
            .ret_ty
            .map(|(ty, span)| {
                Ok((
                    ty.desugar_with_ty_params(span, false, env, &generic_ty_params, modules_used)?,
                    span,
                ))
            })
            .transpose()?;
        let where_clause =
            desugar_type_constraints(&self.where_clause, &generic_ty_params, env, modules_used)?;
        let function = ModuleFunction {
            name: self.name,
            generic_params: self.generic_params,
            args,
            args_span: self.args_span,
            ret_ty,
            where_clause,
            body,
            span: self.span,
            doc: self.doc,
        };
        let deps = DepGraphNode(ctx.fn_deps.into_iter().collect());
        Ok((function, deps))
    }
}
