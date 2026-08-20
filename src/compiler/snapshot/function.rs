use crate::{
    Location,
    hir::function::ArgConvention,
    module::{
        DebugLocationRange, ELocalDecl, FunctionDebugInfo, LocalAssignmentMode, LocalDebugInfo,
        LocalDebugOrigin, LocalFrameSlot, LocalStorage, ModuleFunction, ModuleFunctionSpans,
        ResolvedLocalClone, ResolvedLocalDrop,
    },
    types::{mutability::MutType, r#type::Type},
};

use super::{
    NativeCallableCatalog, SnapshotCallableDefinition, SnapshotError, SnapshotFunctionBody,
    SnapshotTypeGraphBuilder, SnapshotTypeId,
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotFunctionSpans {
    name: Location,
    args: Vec<(Location, Option<(Location, bool)>)>,
    args_span: Location,
    ret_ty: Option<(Location, bool)>,
    span: Location,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum SnapshotLocalStorage {
    NonOwning,
    Owned { drop: ResolvedLocalDrop },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotLocalDecl {
    name: (String, Location),
    mut_ty: MutType,
    ty: SnapshotTypeId,
    ty_span: Option<(Location, bool)>,
    scope: Location,
    storage: SnapshotLocalStorage,
    slot: LocalFrameSlot,
    assignment_mode: LocalAssignmentMode,
    clone: Option<ResolvedLocalClone>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotLocalDebugInfo {
    name: String,
    name_span: Location,
    ty: SnapshotTypeId,
    origin: LocalDebugOrigin,
    locations: Vec<DebugLocationRange>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotFunctionDebugInfo {
    locals: Vec<SnapshotLocalDebugInfo>,
}

/// Finalized function metadata plus a reconstructible script/native/structural body reference.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotModuleFunction {
    definition: SnapshotCallableDefinition,
    body: SnapshotFunctionBody,
    parameter_passing: Vec<ArgConvention>,
    spans: Option<SnapshotFunctionSpans>,
    locals: Vec<SnapshotLocalDecl>,
    debug_info: SnapshotFunctionDebugInfo,
}

fn live_ty(types: &[Type], id: SnapshotTypeId) -> Result<Type, SnapshotError> {
    types
        .get(id.0 as usize)
        .copied()
        .ok_or(SnapshotError::InvalidTypeReference(id.0))
}

impl SnapshotFunctionSpans {
    fn capture(value: &ModuleFunctionSpans) -> Self {
        Self {
            name: value.name,
            args: value.args.clone(),
            args_span: value.args_span,
            ret_ty: value.ret_ty,
            span: value.span,
        }
    }

    fn materialize(&self) -> ModuleFunctionSpans {
        ModuleFunctionSpans {
            name: self.name,
            args: self.args.clone(),
            args_span: self.args_span,
            ret_ty: self.ret_ty,
            span: self.span,
        }
    }
}

impl SnapshotLocalDecl {
    fn capture(
        value: &ELocalDecl,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        let storage = match value.storage {
            LocalStorage::NonOwning => SnapshotLocalStorage::NonOwning,
            LocalStorage::Owned { drop } => SnapshotLocalStorage::Owned { drop },
            LocalStorage::Deferred(value) => match value {},
        };
        Ok(Self {
            name: (value.name.0.to_string(), value.name.1),
            mut_ty: value.mut_ty,
            ty: graph.capture(value.ty)?,
            ty_span: value.ty_span,
            scope: value.scope,
            storage,
            slot: value.slot,
            assignment_mode: value.assignment_mode,
            clone: value.clone,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<ELocalDecl, SnapshotError> {
        Ok(ELocalDecl {
            name: (self.name.0.as_str().into(), self.name.1),
            mut_ty: self.mut_ty,
            ty: live_ty(types, self.ty)?,
            ty_span: self.ty_span,
            scope: self.scope,
            storage: match self.storage {
                SnapshotLocalStorage::NonOwning => LocalStorage::NonOwning,
                SnapshotLocalStorage::Owned { drop } => LocalStorage::Owned { drop },
            },
            slot: self.slot,
            assignment_mode: self.assignment_mode,
            clone: self.clone,
        })
    }
}

impl SnapshotFunctionDebugInfo {
    fn capture(
        value: &FunctionDebugInfo,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            locals: value
                .locals
                .iter()
                .map(|local| {
                    Ok(SnapshotLocalDebugInfo {
                        name: local.name.to_string(),
                        name_span: local.name_span,
                        ty: graph.capture(local.ty)?,
                        origin: local.origin,
                        locations: local.locations.clone(),
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<FunctionDebugInfo, SnapshotError> {
        Ok(FunctionDebugInfo {
            locals: self
                .locals
                .iter()
                .map(|local| {
                    Ok(LocalDebugInfo {
                        name: local.name.as_str().into(),
                        name_span: local.name_span,
                        ty: live_ty(types, local.ty)?,
                        origin: local.origin,
                        locations: local.locations.clone(),
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
        })
    }
}

impl SnapshotModuleFunction {
    pub(crate) fn capture(
        value: &ModuleFunction,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            definition: SnapshotCallableDefinition::capture(&value.definition, graph)?,
            body: SnapshotFunctionBody::capture(value)?,
            parameter_passing: value.parameter_passing.clone(),
            spans: value.spans.as_ref().map(SnapshotFunctionSpans::capture),
            locals: value
                .locals
                .iter()
                .map(|local| SnapshotLocalDecl::capture(local, graph))
                .collect::<Result<_, _>>()?,
            debug_info: SnapshotFunctionDebugInfo::capture(&value.debug_info, graph)?,
        })
    }

    pub(crate) fn materialize(
        &self,
        types: &[Type],
        catalog: &NativeCallableCatalog,
        hir_node_count: usize,
    ) -> Result<ModuleFunction, SnapshotError> {
        let (code, origin) = self.body.materialize(catalog, hir_node_count)?;
        Ok(ModuleFunction {
            definition: self.definition.materialize(types)?,
            code,
            origin,
            parameter_passing: self.parameter_passing.clone(),
            spans: self.spans.as_ref().map(SnapshotFunctionSpans::materialize),
            locals: self
                .locals
                .iter()
                .map(|local| local.materialize(types))
                .collect::<Result<_, _>>()?,
            debug_info: self.debug_info.materialize(types)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, compiler::snapshot::NativeTypeCatalog};

    #[test]
    fn all_std_functions_round_trip_with_rebound_bodies() {
        let session = CompilerSession::new();
        let catalog = NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| catalog.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);
        let functions = session
            .std_module()
            .functions
            .iter()
            .map(|function| SnapshotModuleFunction::capture(function, &mut graph))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let graph = graph.finish().unwrap();
        let types = graph.materialize(&|name| catalog.resolve(name)).unwrap();
        let callables =
            NativeCallableCatalog::capture_from_functions(session.std_module().functions.iter())
                .unwrap();

        for (expected, snapshot) in session.std_module().functions.iter().zip(functions) {
            let restored = snapshot
                .materialize(&types, &callables, session.std_module().hir_arena.len())
                .unwrap();
            assert_eq!(restored.origin, expected.origin);
            assert_eq!(
                restored.definition.signature(),
                expected.definition.signature()
            );
            assert_eq!(restored.parameter_passing, expected.parameter_passing);
            assert_eq!(restored.locals.len(), expected.locals.len());
            assert_eq!(restored.debug_info, expected.debug_info);
        }
    }
}
