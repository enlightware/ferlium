use crate::{
    FxHashMap,
    containers::b,
    module::TypeDefId,
    types::{
        effects::{EffType, Effect},
        mutability::MutType,
        r#type::{
            BareNativeTypeB, FnArgType, FnType, NamedType, NativeType, SubscriptMemberType,
            SubscriptResultConvention, SubscriptType, Type, TypeKind, TypeVar, store_types,
        },
    },
};

use super::SnapshotError;

/// Snapshot-local reference into [`SnapshotTypeGraph::nodes`].
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct SnapshotTypeId(pub(crate) u32);

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotFnArgType {
    pub(crate) ty: SnapshotTypeId,
    pub(crate) mut_ty: MutType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotFnType {
    pub(crate) args: Vec<SnapshotFnArgType>,
    pub(crate) ret: SnapshotTypeId,
    /// Effects have no process-local identity, so their logical set is sufficient.
    pub(crate) effects: Vec<Effect>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotSubscriptMemberType {
    pub(crate) effects: Vec<Effect>,
    pub(crate) result_convention: SubscriptResultConvention,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotSubscriptType {
    pub(crate) args: Vec<SnapshotFnArgType>,
    pub(crate) ret: SnapshotTypeId,
    pub(crate) ref_member: Option<SnapshotSubscriptMemberType>,
    pub(crate) mut_member: Option<SnapshotSubscriptMemberType>,
}

/// Structural, process-independent equivalent of one interned [`TypeKind`].
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotTypeKind {
    Variable(TypeVar),
    Native {
        canonical_name: String,
        arguments: Vec<SnapshotTypeId>,
    },
    Variant(Vec<(String, SnapshotTypeId)>),
    Tuple(Vec<SnapshotTypeId>),
    Record(Vec<(String, SnapshotTypeId)>),
    Function(SnapshotFnType),
    Subscript(SnapshotSubscriptType),
    Named {
        def: TypeDefId,
        params: Vec<SnapshotTypeId>,
        effect_params: Vec<Vec<Effect>>,
    },
    Never,
}

/// Transitive closure of the interned types reachable from snapshot roots.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotTypeGraph {
    pub(crate) nodes: Vec<SnapshotTypeKind>,
}

/// Deterministically captures a set of live type roots into a snapshot-local graph.
pub(crate) struct SnapshotTypeGraphBuilder<'a> {
    native_name: &'a dyn Fn(&BareNativeTypeB) -> Option<String>,
    ids: FxHashMap<Type, SnapshotTypeId>,
    nodes: Vec<Option<SnapshotTypeKind>>,
}

impl<'a> SnapshotTypeGraphBuilder<'a> {
    pub(crate) fn new(native_name: &'a dyn Fn(&BareNativeTypeB) -> Option<String>) -> Self {
        Self {
            native_name,
            ids: FxHashMap::default(),
            nodes: Vec::new(),
        }
    }

    pub(crate) fn capture(&mut self, ty: Type) -> Result<SnapshotTypeId, SnapshotError> {
        if let Some(id) = self.ids.get(&ty) {
            return Ok(*id);
        }

        // Reserve before descending so recursive worlds close back over this ID.
        let id = SnapshotTypeId(self.nodes.len() as u32);
        self.ids.insert(ty, id);
        self.nodes.push(None);
        let kind = self.capture_kind(&ty.data())?;
        self.nodes[id.0 as usize] = Some(kind);
        Ok(id)
    }

    pub(crate) fn finish(self) -> Result<SnapshotTypeGraph, SnapshotError> {
        let nodes = self
            .nodes
            .into_iter()
            .enumerate()
            .map(|(index, node)| node.ok_or(SnapshotError::IncompleteTypeGraph(index as u32)))
            .collect::<Result<_, _>>()?;
        Ok(SnapshotTypeGraph { nodes })
    }

    pub(crate) fn capture_fn_type(
        &mut self,
        function: &FnType,
    ) -> Result<SnapshotFnType, SnapshotError> {
        Ok(SnapshotFnType {
            args: self.capture_args(&function.args)?,
            ret: self.capture(function.ret)?,
            effects: function.effects.iter().collect(),
        })
    }

    pub(crate) fn capture_subscript_type(
        &mut self,
        subscript: &SubscriptType,
    ) -> Result<SnapshotSubscriptType, SnapshotError> {
        Ok(SnapshotSubscriptType {
            args: self.capture_args(&subscript.args)?,
            ret: self.capture(subscript.ret)?,
            ref_member: subscript.ref_member.as_ref().map(Self::capture_member),
            mut_member: subscript.mut_member.as_ref().map(Self::capture_member),
        })
    }

    fn capture_args(
        &mut self,
        args: &[FnArgType],
    ) -> Result<Vec<SnapshotFnArgType>, SnapshotError> {
        args.iter()
            .map(|arg| {
                Ok(SnapshotFnArgType {
                    ty: self.capture(arg.ty)?,
                    mut_ty: arg.mut_ty,
                })
            })
            .collect()
    }

    fn capture_member(member: &SubscriptMemberType) -> SnapshotSubscriptMemberType {
        SnapshotSubscriptMemberType {
            effects: member.effects.iter().collect(),
            result_convention: member.result_convention,
        }
    }

    fn capture_kind(&mut self, kind: &TypeKind) -> Result<SnapshotTypeKind, SnapshotError> {
        Ok(match kind {
            TypeKind::Variable(var) => SnapshotTypeKind::Variable(*var),
            TypeKind::Native(native) => {
                let canonical_name = (self.native_name)(&native.bare_ty).ok_or_else(|| {
                    SnapshotError::UnnamedNativeType(native.bare_ty.type_name().to_owned())
                })?;
                SnapshotTypeKind::Native {
                    canonical_name,
                    arguments: native
                        .arguments
                        .iter()
                        .map(|ty| self.capture(*ty))
                        .collect::<Result<_, _>>()?,
                }
            }
            TypeKind::Variant(variants) => SnapshotTypeKind::Variant(
                variants
                    .iter()
                    .map(|(name, ty)| Ok((name.to_string(), self.capture(*ty)?)))
                    .collect::<Result<_, SnapshotError>>()?,
            ),
            TypeKind::Tuple(types) => SnapshotTypeKind::Tuple(
                types
                    .iter()
                    .map(|ty| self.capture(*ty))
                    .collect::<Result<_, _>>()?,
            ),
            TypeKind::Record(fields) => SnapshotTypeKind::Record(
                fields
                    .iter()
                    .map(|(name, ty)| Ok((name.to_string(), self.capture(*ty)?)))
                    .collect::<Result<_, SnapshotError>>()?,
            ),
            TypeKind::Function(function) => {
                SnapshotTypeKind::Function(self.capture_fn_type(function)?)
            }
            TypeKind::Subscript(subscript) => {
                SnapshotTypeKind::Subscript(self.capture_subscript_type(subscript)?)
            }
            TypeKind::Named(NamedType {
                def,
                params,
                effect_params,
            }) => SnapshotTypeKind::Named {
                def: *def,
                params: params
                    .iter()
                    .map(|ty| self.capture(*ty))
                    .collect::<Result<_, _>>()?,
                effect_params: effect_params
                    .iter()
                    .map(|effects| effects.iter().collect())
                    .collect(),
            },
            TypeKind::Never => SnapshotTypeKind::Never,
        })
    }
}

impl SnapshotTypeGraph {
    /// Re-intern every node together. Local references let `store_types` recover recursive SCCs.
    pub(crate) fn materialize(
        &self,
        native_type: &dyn Fn(&str) -> Option<BareNativeTypeB>,
    ) -> Result<Vec<Type>, SnapshotError> {
        let local = |id: SnapshotTypeId| -> Result<Type, SnapshotError> {
            if (id.0 as usize) < self.nodes.len() {
                Ok(Type::new_local(id.0))
            } else {
                Err(SnapshotError::InvalidTypeReference(id.0))
            }
        };
        let effects = |effects: &[Effect]| -> EffType { effects.iter().copied().collect() };
        let arg = |arg: &SnapshotFnArgType| -> Result<FnArgType, SnapshotError> {
            Ok(FnArgType::new(local(arg.ty)?, arg.mut_ty))
        };
        let member = |member: &SnapshotSubscriptMemberType| SubscriptMemberType {
            effects: effects(&member.effects),
            result_convention: member.result_convention,
        };

        let kinds = self
            .nodes
            .iter()
            .map(|node| {
                Ok(match node {
                    SnapshotTypeKind::Variable(var) => TypeKind::Variable(*var),
                    SnapshotTypeKind::Native {
                        canonical_name,
                        arguments,
                    } => TypeKind::Native(b(NativeType::new(
                        native_type(canonical_name).ok_or_else(|| {
                            SnapshotError::UnknownNativeType(canonical_name.clone())
                        })?,
                        arguments
                            .iter()
                            .map(|id| local(*id))
                            .collect::<Result<_, _>>()?,
                    ))),
                    SnapshotTypeKind::Variant(variants) => TypeKind::Variant(
                        variants
                            .iter()
                            .map(|(name, id)| Ok((name.as_str().into(), local(*id)?)))
                            .collect::<Result<_, SnapshotError>>()?,
                    ),
                    SnapshotTypeKind::Tuple(types) => TypeKind::Tuple(
                        types
                            .iter()
                            .map(|id| local(*id))
                            .collect::<Result<_, _>>()?,
                    ),
                    SnapshotTypeKind::Record(fields) => TypeKind::Record(
                        fields
                            .iter()
                            .map(|(name, id)| Ok((name.as_str().into(), local(*id)?)))
                            .collect::<Result<_, SnapshotError>>()?,
                    ),
                    SnapshotTypeKind::Function(function) => TypeKind::Function(b(FnType::new(
                        function.args.iter().map(arg).collect::<Result<_, _>>()?,
                        local(function.ret)?,
                        effects(&function.effects),
                    ))),
                    SnapshotTypeKind::Subscript(subscript) => {
                        TypeKind::Subscript(b(SubscriptType::new(
                            subscript.args.iter().map(arg).collect::<Result<_, _>>()?,
                            local(subscript.ret)?,
                            subscript.ref_member.as_ref().map(member),
                            subscript.mut_member.as_ref().map(member),
                        )))
                    }
                    SnapshotTypeKind::Named {
                        def,
                        params,
                        effect_params,
                    } => TypeKind::Named(NamedType {
                        def: *def,
                        params: params
                            .iter()
                            .map(|id| local(*id))
                            .collect::<Result<_, _>>()?,
                        effect_params: effect_params.iter().map(|set| effects(set)).collect(),
                    }),
                    SnapshotTypeKind::Never => TypeKind::Never,
                })
            })
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        Ok(store_types(&kinds))
    }
}

#[cfg(test)]
mod tests {
    use crate::types::r#type::bare_native_type;

    use super::*;

    #[test]
    fn recursive_type_graph_round_trip_reinterns_the_same_structure() {
        let recursive = TypeKind::Variant(vec![
            ("End".into(), Type::unit()),
            ("Next".into(), Type::new_local(1)),
        ]);
        let link = TypeKind::Tuple(vec![Type::primitive::<isize>(), Type::new_local(0)]);
        // Build the recursive SCC with local references in one interner transaction.
        let original = store_types(&[recursive, link])[0];

        let native_name = |bare: &BareNativeTypeB| {
            if *bare == bare_native_type::<()>() {
                Some("unit".to_owned())
            } else if *bare == bare_native_type::<isize>() {
                Some("int".to_owned())
            } else {
                None
            }
        };
        let mut builder = SnapshotTypeGraphBuilder::new(&native_name);
        let root = builder.capture(original).unwrap();
        let graph = builder.finish().unwrap();
        let resolve = |name: &str| match name {
            "unit" => Some(bare_native_type::<()>()),
            "int" => Some(bare_native_type::<isize>()),
            _ => None,
        };
        let restored = graph.materialize(&resolve).unwrap()[root.0 as usize];

        assert_eq!(restored, original);
        assert!(restored.is_global_recursive());
    }
}
