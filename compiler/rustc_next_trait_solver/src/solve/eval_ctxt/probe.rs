use std::marker::PhantomData;

use rustc_type_ir::inherent::*;
use rustc_type_ir::search_graph::CandidateHeadUsages;
use rustc_type_ir::{self as ty, InferCtxtLike, Interner};
use tracing::instrument;

use crate::canonical::instantiate_and_apply_query_response;
use crate::delegate::SolverDelegate;
use crate::solve::assembly::Candidate;
use crate::solve::eval_ctxt::{CurrentGoalKind, EvaluationResult};
use crate::solve::{
    BuiltinImplSource, CandidateSource, Certainty, EvalCtxt, Goal, GoalSource, GoalStalledOn,
    NoSolution, QueryResult, inspect,
};

pub(in crate::solve) struct ProbeCtxt<'me, 'a, D, I, F, T>
where
    D: SolverDelegate<Interner = I>,
    I: Interner,
{
    ecx: &'me mut EvalCtxt<'a, D, I>,
    probe_kind: F,
    _result: PhantomData<T>,
}

impl<D, I, F, T> ProbeCtxt<'_, '_, D, I, F, T>
where
    F: FnOnce(&T) -> inspect::ProbeKind<I>,
    D: SolverDelegate<Interner = I>,
    I: Interner,
{
    pub(in crate::solve) fn enter_single_candidate(
        self,
        f: impl FnOnce(&mut EvalCtxt<'_, D>) -> T,
    ) -> (T, CandidateHeadUsages) {
        self.ecx.search_graph.enter_single_candidate();
        let mut candidate_usages = CandidateHeadUsages::default();
        let result = self.enter(|ecx| {
            let result = f(ecx);
            candidate_usages = ecx.search_graph.finish_single_candidate();
            result
        });
        (result, candidate_usages)
    }

    pub(in crate::solve) fn enter(self, f: impl FnOnce(&mut EvalCtxt<'_, D>) -> T) -> T {
        let nested_goals = self.ecx.nested_goals.clone();
        self.enter_inner(f, nested_goals)
    }

    pub(in crate::solve) fn enter_without_propagated_nested_goals(
        self,
        f: impl FnOnce(&mut EvalCtxt<'_, D>) -> T,
    ) -> T {
        self.enter_inner(f, Default::default())
    }

    fn enter_inner(
        self,
        f: impl FnOnce(&mut EvalCtxt<'_, D>) -> T,
        propagated_nested_goals: Vec<(GoalSource, Goal<I, I::Predicate>, Option<GoalStalledOn<I>>)>,
    ) -> T {
        let ProbeCtxt { ecx: outer, probe_kind, _result } = self;

        let delegate = outer.delegate;
        let max_input_universe = outer.max_input_universe;
        let mut nested = EvalCtxt {
            delegate,
            var_kinds: outer.var_kinds,
            var_values: outer.var_values,
            current_goal_kind: outer.current_goal_kind,
            max_input_universe,
            initial_opaque_types_storage_num_entries: outer
                .initial_opaque_types_storage_num_entries,
            search_graph: outer.search_graph,
            nested_goals: propagated_nested_goals,
            origin_span: outer.origin_span,
            tainted: outer.tainted,
            inspect: outer.inspect.take_and_enter_probe(),
        };
        let r = nested.delegate.probe(|| {
            let r = f(&mut nested);
            nested.inspect.probe_final_state(delegate, max_input_universe);
            r
        });
        if !nested.inspect.is_noop() {
            let probe_kind = probe_kind(&r);
            nested.inspect.probe_kind(probe_kind);
            outer.inspect = nested.inspect.finish_probe();
        }
        r
    }
}

pub(in crate::solve) struct TraitProbeCtxt<'me, 'a, D, I, F>
where
    D: SolverDelegate<Interner = I>,
    I: Interner,
{
    cx: ProbeCtxt<'me, 'a, D, I, F, EvaluationResult<I>>,
    source: CandidateSource<I>,
}

impl<D, I, F> TraitProbeCtxt<'_, '_, D, I, F>
where
    D: SolverDelegate<Interner = I>,
    I: Interner,
    F: FnOnce(&EvaluationResult<I>) -> inspect::ProbeKind<I>,
{
    #[instrument(level = "debug", skip_all, fields(source = ?self.source))]
    pub(in crate::solve) fn enter(
        self,
        f: impl FnOnce(&mut EvalCtxt<'_, D>) -> EvaluationResult<I>,
    ) -> Result<Candidate<I>, NoSolution> {
        let (result, head_usages) = self.cx.enter_single_candidate(f);
        result.map(|result| Candidate { source: self.source, result, head_usages })
    }
}

impl<'a, D, I> EvalCtxt<'a, D, I>
where
    D: SolverDelegate<Interner = I>,
    I: Interner,
{
    /// `probe_kind` is only called when proof tree building is enabled so it can be
    /// as expensive as necessary to output the desired information.
    pub(in crate::solve) fn probe<F, T>(&mut self, probe_kind: F) -> ProbeCtxt<'_, 'a, D, I, F, T>
    where
        F: FnOnce(&T) -> inspect::ProbeKind<I>,
    {
        ProbeCtxt { ecx: self, probe_kind, _result: PhantomData }
    }

    pub(in crate::solve) fn probe_builtin_trait_candidate(
        &mut self,
        source: BuiltinImplSource,
    ) -> TraitProbeCtxt<'_, 'a, D, I, impl FnOnce(&EvaluationResult<I>) -> inspect::ProbeKind<I>>
    {
        self.probe_trait_candidate(CandidateSource::BuiltinImpl(source))
    }

    pub(in crate::solve) fn probe_trait_candidate(
        &mut self,
        source: CandidateSource<I>,
    ) -> TraitProbeCtxt<'_, 'a, D, I, impl FnOnce(&EvaluationResult<I>) -> inspect::ProbeKind<I>>
    {
        TraitProbeCtxt {
            cx: ProbeCtxt {
                ecx: self,
                probe_kind: move |result: &EvaluationResult<I>| {
                    inspect::ProbeKind::TraitCandidate {
                        source,
                        result: result.clone().map(|c| c.unchecked_map(|(resp, _)| resp)),
                    }
                },
                _result: PhantomData,
            },
            source,
        }
    }

    /// When probing candidates for the `NormalizesTo` goal, the projection term should be
    /// fully unconstrained. This helps it by replacing the projection term to an unconstrained
    /// inference var, probe with `CurrentGoalKind::NormalizesTo` to handle ambiguous nested
    /// goals, instantiate and apply the response and then add those nested goals to the root
    /// context.
    pub(in crate::solve) fn probe_with_unconstrained_projection_term(
        &mut self,
        goal: Goal<I, ty::NormalizesTo<I>>,
        f: impl FnOnce(&mut EvalCtxt<'_, D, I>, Goal<I, ty::NormalizesTo<I>>) -> EvaluationResult<I>,
    ) -> Result<(I::Term, Certainty), NoSolution> {
        let cx = self.cx();
        let unconstrained_term = self.next_term_infer_of_kind(goal.predicate.term);
        let unconstrained_goal = goal
            .with(cx, ty::NormalizesTo { alias: goal.predicate.alias, term: unconstrained_term });
        let extended_var_values = cx.mk_args_from_iter(
            self.var_values.var_values.iter().chain(std::iter::once(unconstrained_term.into())),
        );
        let mut extended_var_kinds = self.var_kinds.to_vec();
        let extra_var_kind = match unconstrained_term.kind() {
            ty::TermKind::Ty(_) => ty::CanonicalVarKind::Ty {
                ui: self.max_input_universe,
                sub_root: ty::BoundVar::from_usize(extended_var_kinds.len()),
            },
            ty::TermKind::Const(_) => ty::CanonicalVarKind::Const(self.max_input_universe),
        };
        extended_var_kinds.push(extra_var_kind);
        let extended_var_kinds = cx.mk_canonical_var_kinds(&extended_var_kinds);

        let resp = self.probe(|_| inspect::ProbeKind::ShadowedEnvProbing).enter(|ecx| {
            ecx.current_goal_kind = CurrentGoalKind::NormalizesTo;
            ecx.var_values.var_values = extended_var_values;
            ecx.var_kinds = extended_var_kinds;
            f(ecx, unconstrained_goal)
        })?;

        let (nested_goals, certainty) = instantiate_and_apply_query_response(
            self.delegate,
            goal.param_env,
            extended_var_values.as_slice(),
            resp,
            self.origin_span,
        );

        for (source, nested_goal) in nested_goals.0 {
            self.add_goal(source, nested_goal);
        }

        Ok((unconstrained_term, certainty))
    }
}
