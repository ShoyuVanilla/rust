//! Data structure used to inspect trait solver behavior.
//!
//! During trait solving we optionally build "proof trees", the root of
//! which is a [GoalEvaluation]. These  trees are used by the compiler
//! to inspect the behavior of the trait solver and to access its internal
//! state, e.g. for diagnostics and when selecting impls during codegen.
//!
//! Because each nested goal in the solver gets [canonicalized] separately
//! and we discard inference progress via "probes", we cannot mechanically
//! use proof trees without somehow "lifting up" data local to the current
//! `InferCtxt`. To use the data from evaluation we therefore canonicalize
//! it and store it as a [CanonicalState].
//!
//! Proof trees are only shallow, we do not compute the proof tree for nested
//! goals. Visiting proof trees instead recomputes nested goals in the parents
//! inference context when necessary.
//!
//! [canonicalized]: https://rustc-dev-guide.rust-lang.org/solve/canonicalization.html

use crate::solve::{
    CandidateSource, CanonicalInput, Certainty, Goal, GoalSource, QueryInput, QueryResult,
};
use crate::{Canonical, CanonicalVarValues, Interner};
use rustc_type_ir_macros::{TypeFoldable_Generic, TypeVisitable_Generic};
use std::fmt::Debug;
use std::hash::Hash;

/// Some `data` together with information about how they relate to the input
/// of the canonical query.
///
/// This is only ever used as [CanonicalState]. Any type information in proof
/// trees used mechanically has to be canonicalized as we otherwise leak
/// inference variables from a nested `InferCtxt`.
#[derive(derivative::Derivative)]
#[derivative(
    Clone(bound = "T: Clone"),
    Copy(bound = "T: Copy"),
    PartialEq(bound = "T: PartialEq"),
    Eq(bound = "T: Eq"),
    Hash(bound = "T: Hash"),
    Debug(bound = "T: Debug")
)]
#[derive(TypeVisitable_Generic, TypeFoldable_Generic)]
pub struct State<I: Interner, T> {
    pub var_values: CanonicalVarValues<I>,
    pub data: T,
}

pub type CanonicalState<I, T> = Canonical<I, State<I, T>>;

/// When evaluating a goal we also store the original values
/// for the `CanonicalVarValues` of the canonicalized goal.
/// We use this to map any [CanonicalState] from the local `InferCtxt`
/// of the solver query to the `InferCtxt` of the caller.
#[derive(derivative::Derivative)]
#[derivative(PartialEq(bound = ""), Eq(bound = ""), Hash(bound = ""))]
pub struct GoalEvaluation<I: Interner> {
    pub uncanonicalized_goal: Goal<I, I::Predicate>,
    pub orig_values: Vec<I::GenericArg>,
    pub evaluation: CanonicalGoalEvaluation<I>,
}

#[derive(derivative::Derivative)]
#[derivative(PartialEq(bound = ""), Eq(bound = ""), Hash(bound = ""), Debug(bound = ""))]
pub struct CanonicalGoalEvaluation<I: Interner> {
    pub goal: CanonicalInput<I>,
    pub kind: CanonicalGoalEvaluationKind<I>,
    pub result: QueryResult<I>,
}

#[derive(derivative::Derivative)]
#[derivative(PartialEq(bound = ""), Eq(bound = ""), Hash(bound = ""), Debug(bound = ""))]
pub enum CanonicalGoalEvaluationKind<I: Interner> {
    Overflow,
    CycleInStack,
    ProvisionalCacheHit,
    Evaluation { final_revision: I::CanonicalGoalEvaluationStepRef },
}

#[derive(derivative::Derivative)]
#[derivative(PartialEq(bound = ""), Eq(bound = ""), Hash(bound = ""), Debug(bound = ""))]
pub struct CanonicalGoalEvaluationStep<I: Interner> {
    pub instantiated_goal: QueryInput<I, I::Predicate>,

    /// The actual evaluation of the goal, always `ProbeKind::Root`.
    pub evaluation: Probe<I>,
}

/// A self-contained computation during trait solving. This either
/// corresponds to a `EvalCtxt::probe(_X)` call or the root evaluation
/// of a goal.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""), Hash(bound = ""))]
pub struct Probe<I: Interner> {
    /// What happened inside of this probe in chronological order.
    pub steps: Vec<ProbeStep<I>>,
    pub kind: ProbeKind<I>,
    pub final_state: CanonicalState<I, ()>,
}

#[derive(derivative::Derivative)]
#[derivative(PartialEq(bound = ""), Eq(bound = ""), Hash(bound = ""), Debug(bound = ""))]
pub enum ProbeStep<I: Interner> {
    /// We added a goal to the `EvalCtxt` which will get proven
    /// the next time `EvalCtxt::try_evaluate_added_goals` is called.
    AddGoal(GoalSource, CanonicalState<I, Goal<I, I::Predicate>>),
    /// A call to `probe` while proving the current goal. This is
    /// used whenever there are multiple candidates to prove the
    /// current goal.
    NestedProbe(Probe<I>),
    /// A trait goal was satisfied by an impl candidate.
    RecordImplArgs { impl_args: CanonicalState<I, I::GenericArgs> },
    /// A call to `EvalCtxt::evaluate_added_goals_make_canonical_response` with
    /// `Certainty` was made. This is the certainty passed in, so it's not unified
    /// with the certainty of the `try_evaluate_added_goals` that is done within;
    /// if it's `Certainty::Yes`, then we can trust that the candidate is "finished"
    /// and we didn't force ambiguity for some reason.
    MakeCanonicalResponse { shallow_certainty: Certainty },
}

/// What kind of probe we're in. In case the probe represents a candidate, or
/// the final result of the current goal - via [ProbeKind::Root] - we also
/// store the [QueryResult].
#[derive(derivative::Derivative)]
#[derivative(
    Clone(bound = ""),
    Copy(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = ""),
    Hash(bound = ""),
    Debug(bound = "")
)]
#[derive(TypeVisitable_Generic, TypeFoldable_Generic)]
pub enum ProbeKind<I: Interner> {
    /// The root inference context while proving a goal.
    Root { result: QueryResult<I> },
    /// Trying to normalize an alias by at least one step in `NormalizesTo`.
    TryNormalizeNonRigid { result: QueryResult<I> },
    /// Probe entered when normalizing the self ty during candidate assembly
    NormalizedSelfTyAssembly,
    /// A candidate for proving a trait or alias-relate goal.
    TraitCandidate { source: CandidateSource<I>, result: QueryResult<I> },
    /// Used in the probe that wraps normalizing the non-self type for the unsize
    /// trait, which is also structurally matched on.
    UnsizeAssembly,
    /// During upcasting from some source object to target object type, used to
    /// do a probe to find out what projection type(s) may be used to prove that
    /// the source type upholds all of the target type's object bounds.
    UpcastProjectionCompatibility,
    /// Looking for param-env candidates that satisfy the trait ref for a projection.
    ShadowedEnvProbing,
    /// Try to unify an opaque type with an existing key in the storage.
    OpaqueTypeStorageLookup { result: QueryResult<I> },
}
