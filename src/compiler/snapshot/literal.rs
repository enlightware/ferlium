use crate::{
    hir::value::{LiteralNativeValue, LiteralValue},
    std::{math::Float, string::StaticStr},
};

use super::SnapshotError;

/// Portable literal data used by cached HIR and pattern alternatives.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotLiteral {
    Unit,
    Bool(bool),
    Int(i64),
    FloatBits(u64),
    StaticString(String),
    Tuple(Vec<SnapshotLiteral>),
    VariantTag(String),
}

impl SnapshotLiteral {
    pub(crate) fn capture(value: &LiteralValue) -> Result<Self, SnapshotError> {
        Ok(match value {
            LiteralValue::Native(value) => capture_native(value.as_ref())?,
            LiteralValue::Tuple(values) => {
                Self::Tuple(values.iter().map(Self::capture).collect::<Result<_, _>>()?)
            }
            LiteralValue::VariantTag(tag) => Self::VariantTag(tag.to_string()),
        })
    }

    pub(crate) fn materialize(&self) -> Result<LiteralValue, SnapshotError> {
        Ok(match self {
            Self::Unit => LiteralValue::new_native(()),
            Self::Bool(value) => LiteralValue::new_native(*value),
            Self::Int(value) => {
                LiteralValue::new_native(isize::try_from(*value).map_err(|_| {
                    SnapshotError::InvalidNativeLiteral(
                        "integer does not fit target isize".to_owned(),
                    )
                })?)
            }
            Self::FloatBits(bits) => {
                LiteralValue::new_native(Float::new(f64::from_bits(*bits)).map_err(|_| {
                    SnapshotError::InvalidNativeLiteral("non-finite float".to_owned())
                })?)
            }
            Self::StaticString(value) => LiteralValue::new_native(StaticStr::new(value)),
            Self::Tuple(values) => LiteralValue::new_tuple(
                values
                    .iter()
                    .map(Self::materialize)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Self::VariantTag(tag) => LiteralValue::new_variant_tag(tag.as_str().into()),
        })
    }
}

fn capture_native(value: &dyn LiteralNativeValue) -> Result<SnapshotLiteral, SnapshotError> {
    let value = LiteralNativeValue::as_any(value);
    if value.is::<()>() {
        Ok(SnapshotLiteral::Unit)
    } else if let Some(value) = value.downcast_ref::<bool>() {
        Ok(SnapshotLiteral::Bool(*value))
    } else if let Some(value) = value.downcast_ref::<isize>() {
        Ok(SnapshotLiteral::Int(*value as i64))
    } else if let Some(value) = value.downcast_ref::<Float>() {
        Ok(SnapshotLiteral::FloatBits(value.into_inner().to_bits()))
    } else if let Some(value) = value.downcast_ref::<StaticStr>() {
        Ok(SnapshotLiteral::StaticString(value.as_str().to_owned()))
    } else {
        Err(SnapshotError::UnknownNativeLiteral(
            std::any::type_name_of_val(value).to_owned(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_and_recursive_literals_round_trip() {
        let literal = LiteralValue::new_tuple(vec![
            LiteralValue::new_native(true),
            LiteralValue::new_native(42_isize),
            LiteralValue::new_native(Float::new(1.25).unwrap()),
            LiteralValue::new_native(StaticStr::new("hello")),
        ]);
        let snapshot = SnapshotLiteral::capture(&literal).unwrap();
        assert_eq!(snapshot.materialize().unwrap(), literal);
    }
}
