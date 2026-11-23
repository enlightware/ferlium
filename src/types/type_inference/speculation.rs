// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Speculative work on a state that can be snapshotted and rolled back, such as a type inference.

use std::ops::{Deref, DerefMut};

/// A state that can be snapshotted and rolled back to a snapshot.
pub(crate) trait Snapshotting {
    type Snapshot;
    fn snapshot(&mut self) -> Self::Snapshot;
    fn rollback_to(&mut self, snapshot: Self::Snapshot);
    /// Keep the changes since `snapshot`, which a snapshot further out can still undo.
    fn commit(&mut self, snapshot: Self::Snapshot);
}

/// Speculative work on a state, which the speculation derefs to: what it changes is rolled back
/// when it is dropped, however it is left, an error included, unless it is kept.
pub(crate) struct Speculation<'a, T: Snapshotting> {
    state: &'a mut T,
    snapshot: Option<T::Snapshot>,
}

impl<'a, T: Snapshotting> Speculation<'a, T> {
    pub(crate) fn new(state: &'a mut T) -> Self {
        let snapshot = Some(state.snapshot());
        Self { state, snapshot }
    }

    /// Keep what the speculation changed.
    pub(crate) fn keep(mut self) {
        let snapshot = self.snapshot.take().expect("an active speculation");
        self.state.commit(snapshot);
    }

    /// Roll back what the speculation changed so far, and continue speculating.
    pub(crate) fn restart(&mut self) {
        let snapshot = self.snapshot.take().expect("an active speculation");
        self.state.rollback_to(snapshot);
        self.snapshot = Some(self.state.snapshot());
    }
}

impl<T: Snapshotting> Deref for Speculation<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.state
    }
}

impl<T: Snapshotting> DerefMut for Speculation<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.state
    }
}

impl<T: Snapshotting> Drop for Speculation<'_, T> {
    fn drop(&mut self) {
        if let Some(snapshot) = self.snapshot.take() {
            self.state.rollback_to(snapshot);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Location,
        std::math::int_type,
        types::{r#type::Type, type_inference::unify::UnifiedTypeInference},
    };

    /// A state recording its changes, which a snapshot truncates.
    #[derive(Default)]
    struct Log(Vec<u32>);

    impl Snapshotting for Log {
        type Snapshot = usize;
        fn snapshot(&mut self) -> usize {
            self.0.len()
        }
        fn rollback_to(&mut self, snapshot: usize) {
            self.0.truncate(snapshot);
        }
        fn commit(&mut self, _snapshot: usize) {}
    }

    fn fail_while_speculating(log: &mut Log) -> Result<(), ()> {
        let mut speculation = Speculation::new(log);
        speculation.0.push(2);
        Err(())?;
        speculation.keep();
        Ok(())
    }

    #[test]
    fn speculation_rolls_back_unless_kept() {
        let mut log = Log(vec![0]);
        let mut speculation = Speculation::new(&mut log);
        speculation.0.push(1);
        drop(speculation);
        assert_eq!(log.0, [0]);

        assert!(fail_while_speculating(&mut log).is_err());
        assert_eq!(log.0, [0]);

        let mut speculation = Speculation::new(&mut log);
        speculation.0.push(1);
        speculation.restart();
        assert_eq!(speculation.0, [0]);
        speculation.0.push(3);
        speculation.keep();
        assert_eq!(log.0, [0, 3]);
    }

    /// A speculation on an inference closes the snapshots of its tables, whether it is kept or
    /// rolled back: ena records every change while one is open.
    #[test]
    fn speculation_on_an_inference_closes_its_snapshots() {
        let span = Location::new_synthesized();
        let var = Type::variable_id(0);
        let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
        for keep in [false, true] {
            let mut speculation = inference.speculate();
            speculation
                .unify_same_type(var, span, int_type(), span)
                .unwrap();
            if keep {
                speculation.keep();
            } else {
                drop(speculation);
            }
            assert_eq!(inference.open_snapshots(), 0);
            let expected = if keep { int_type() } else { var };
            assert_eq!(inference.substitute_in_type(var).unwrap(), expected);
        }
    }
}
