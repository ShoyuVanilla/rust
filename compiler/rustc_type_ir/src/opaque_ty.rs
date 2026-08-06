use std::marker::PhantomData;

use derive_where::derive_where;
use rustc_index::Idx;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable_NoContext, Encodable_NoContext, StableHash_NoContext};
use rustc_type_ir_macros::{GenericTypeVisitable, TypeFoldable_Generic, TypeVisitable_Generic};

use crate::inherent::*;
use crate::solve::AliasBoundKind;
use crate::{
    self as ty, Binder, Flags, Interner, Region, TypeFoldable, TypeFolder, TypeSuperFoldable,
    TypeVisitableExt,
};

#[derive_where(Clone, Copy, Hash, PartialEq, Debug; I: Interner)]
#[derive(TypeVisitable_Generic, GenericTypeVisitable, TypeFoldable_Generic)]
#[cfg_attr(
    feature = "nightly",
    derive(Encodable_NoContext, Decodable_NoContext, StableHash_NoContext)
)]
pub struct OpaqueTypeKey<I: Interner> {
    pub def_id: I::LocalOpaqueTyId,
    pub args: I::GenericArgs,
}

impl<I: Interner> Eq for OpaqueTypeKey<I> {}

impl<I: Interner> OpaqueTypeKey<I> {
    pub fn iter_captured_args(self, cx: I) -> impl Iterator<Item = (usize, I::GenericArg)> {
        let variances = cx.variances_of(self.def_id.into());
        std::iter::zip(self.args.iter(), variances.iter()).enumerate().filter_map(
            |(i, (arg, v))| match (arg.kind(), v) {
                (_, ty::Invariant) => Some((i, arg)),
                (ty::GenericArgKind::Lifetime(_), ty::Bivariant) => None,
                _ => panic!("unexpected opaque type arg variance"),
            },
        )
    }

    pub fn fold_captured_lifetime_args(
        self,
        cx: I,
        mut f: impl FnMut(Region<I>) -> Region<I>,
    ) -> Self {
        let Self { def_id, args } = self;
        let variances = cx.variances_of(def_id.into());
        let args =
            std::iter::zip(args.iter(), variances.iter()).map(|(arg, v)| match (arg.kind(), v) {
                (ty::GenericArgKind::Lifetime(_), ty::Bivariant) => arg,
                (ty::GenericArgKind::Lifetime(lt), _) => f(lt).into(),
                _ => arg,
            });
        let args = cx.mk_args_from_iter(args);
        Self { def_id, args }
    }
}

// TODO: comments here

#[derive_where(Clone, Copy, Hash, PartialEq, Debug; I: Interner)]
#[derive(TypeVisitable_Generic, GenericTypeVisitable, TypeFoldable_Generic)]
#[cfg_attr(
    feature = "nightly",
    derive(Encodable_NoContext, Decodable_NoContext, StableHash_NoContext)
)]
pub struct OpaqueHiddenTyBound<I: Interner> {
    pub kind: AliasBoundKind,
    pub bound: Binder<I, I::Clause>,
    #[derive_where(skip(Debug))]
    _tcx: PhantomData<fn() -> I>,
}

impl<I: Interner> Eq for OpaqueHiddenTyBound<I> {}

impl<I: Interner> OpaqueHiddenTyBound<I> {
    pub fn new(cx: I, self_ty: I::Ty, kind: AliasBoundKind, bound: I::Clause) -> Self {
        let outermost = bound.outer_exclusive_binder();
        let bound = bound.fold_with(&mut TyReplacer {
            cx,
            from: self_ty,
            to: Ty::new_anon_bound(cx, outermost, ty::BoundVar::new(0)),
        });
        let bound = Binder::bind_with_vars(
            bound,
            I::BoundVarKinds::from_vars(cx, [ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon)]),
        );

        OpaqueHiddenTyBound { kind, bound, _tcx: PhantomData }
    }

    // TODO: mk_with_def_id or sth?

    pub fn instantiate(self, cx: I, ty: I::Ty) -> I::Clause {
        let OpaqueHiddenTyBound { kind: _, bound, _tcx } = self;

        debug_assert_eq!(
            bound.bound_vars().as_slice(),
            &[ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon)]
        );

        let bound = bound.skip_binder();
        debug_assert!(bound.has_escaping_bound_vars());
        let outermost = bound.outer_exclusive_binder().shifted_in(1);

        let res = self.bound.skip_binder().fold_with(&mut TyReplacer {
            cx,
            from: Ty::new_anon_bound(cx, outermost, ty::BoundVar::new(0)),
            to: ty,
        });
        debug_assert!(!res.has_escaping_bound_vars());

        res
    }
}

struct TyReplacer<I: Interner> {
    cx: I,
    from: I::Ty,
    to: I::Ty,
}

impl<I: Interner> TypeFolder<I> for TyReplacer<I> {
    fn cx(&self) -> I {
        self.cx
    }

    fn fold_ty(&mut self, t: I::Ty) -> I::Ty {
        if t == self.from { self.to } else { t.super_fold_with(self) }
    }
}
