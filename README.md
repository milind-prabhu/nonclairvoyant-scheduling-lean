# Non-clairvoyant DAG scheduling in Lean

Lean formalization of the main results of **Non-Clairvoyant Scheduling is Hard Even for Trees**,
Kunal Agrawal, Owen Druzgal, Milind Prabhu, and Jinhao Zhao,
[arXiv:2610.11006v1](https://arxiv.org/abs/2610.11006v1).

**All four main theorems are now formalized**, including both randomized
lower bounds against an oblivious adversary. The FIFO upper-bound proof is
verified from finite scheduling definitions through the actual offline optimum.
SFF now has an executable deterministic construction, with checked feasibility,
termination, realization of the round specification, and a bound of 44 times
OPT squared when supplied the optimum (or a positive upper bound).
The batched FIFO upper bound is also verified from concrete schedule states:
maximum flow is at most `(Nat.clog 2 OPT + 2) * OPT`. The record inequality,
unfinished-batch count, and backlog bound are all derived in Lean. The doubling
controller now has a checked finite schedule construction with maximum flow
at most `352 * OPT * min m OPT`. FIFO, SFF, and the combined controller have checked public-history realizations
and cross-instance non-clairvoyance theorems. The general deterministic lower bound is now fully quantified over causal
schedulers: the constructed out-forest has `L ≤ OPT ≤ 2L`, and
`min m OPT * OPT ≤ 64 * maxFlow`. Its hidden-key construction, layer-count
bound, offline ordering, and forcing argument are all checked.
The constant-OPT FIFO lower bound is also verified: every deterministic causal
FIFO scheduler has an instance with `OPT ≤ 6` and flow at least `3*(m-1)`.
The deterministic batched lower bound is now also verified: at scale
`L = 8*c*5^c`, every deterministic causal scheduler with `2*c ≤ m` has a
fixed out-forest with `OPT = L`, releases at multiples of OPT, and flow at
least `c*L`. This gives
`min m (Nat.clog 2 OPT) * OPT ≤ 7 * maxFlow`.
The randomized lower bounds use fixed finite hard families, separated
concatenations, exact counting of bad input sequences, and integration over
an arbitrary probability space of random seeds. They produce one fixed input
with `min m OPT * OPT ≤ 128 * E[maxFlow]` for general arrivals, and
`min m (Nat.clog 2 OPT) * OPT ≤ 14 * E[maxFlow]` for batched arrivals.
Infinite expected flow is included through the extended nonnegative integral.
`fifoScheduler` and `combinedScheduler` instantiate the same causal scheduler
model used by the lower bounds. See [STATUS.md](STATUS.md) for the theorem map,
parameter ranges, and precise modeling scope.

## Main checked theorems

Browse the [interactive dependency blueprint](blueprint/README.md), or view
the [main-results graph](blueprint/generated/Nonclairvoyant_Scheduling_Dependency_Graph.svg).
It includes seven proof views, searchable Lean statements and source, and a
separate module import graph. Every proof arrow is traced to compiled Lean
dependencies.

| Paper result | Main declaration | Explicit guarantee |
| --- | --- | --- |
| Theorem 1, deterministic | `deterministic_competitive_lower` | `min m OPT * OPT ≤ 64 * maxFlow` |
| Theorem 1, randomized | `randomized_competitive_lower` | `min m OPT * OPT ≤ 128 * E[maxFlow]` on one fixed input |
| Theorem 2 | `exists_optimal_order_scheduler` | One causal scheduler with `maxFlow ≤ 352 * OPT * min m OPT` on every finite instance |
| Theorem 3 | `fifo_constant_optimum_lower`, `fifoSchedule_constant_optimum_lower` | `OPT ≤ 6` and FIFO flow at least `3*(m-1)` |
| Theorem 4, upper | `fifoSchedule_batched_bound`, `batched_fifo_combined_bound` | Logarithmic FIFO bound, together with the general processor bound |
| Theorem 4, deterministic lower | `batched_competitive_lower` | `min m (Nat.clog 2 OPT) * OPT ≤ 7 * maxFlow` |
| Theorem 4, randomized lower | `randomized_batched_competitive_lower` | `min m (Nat.clog 2 OPT) * OPT ≤ 14 * E[maxFlow]` on one fixed input |

General lower bounds hold for `m ≥ 2` and every positive multiple `L` of
sixteen, with `L ≤ OPT ≤ 2L`. Batched lower bounds use
`OPT = 8*c*5^c`, for positive `c` with `2*c ≤ m`, and certify that every
release is a multiple of OPT. The constants are explicit witnesses for the
paper's asymptotic statements.

`Scheduling.Instance.fifo_competitive` proves

```lean
theorem fifo_competitive {m : ℕ} {S : Assignment}
    (hm : 0 < m) (hS : I.Valid m S) (hF : I.IsFIFO m S) :
    m * I.maxFlow S ≤ (m * m + m - 1) * I.optimum m hm
```

For positive `m`, this is exactly the paper's factor
`m + 1 - 1/m`, expressed with integer multiplication instead of division.
`optimum` is the attained minimum over valid offline schedules, not an
unconstrained parameter named OPT.

The proof derives all of the following:

- Offline work and path bounds (Proposition 5).
- Existence of a ready vertex in every unfinished finite job DAG.
- The backlog bound `Q(t) ≤ m*m*L` (Lemma 9).
- Partial-slot progress using offline execution times.
- The charge `m*F + P ≤ Q(r)` to distinct vertices.
- The exact FIFO maximum-flow bound (Theorem 8).
- Existence and attainment of an offline optimum.

No backlog or sequential-progress guarantee is assumed as a hypothesis of
the FIFO competitive theorem.

`Scheduling.Instance.sffSchedule_known_optimum` proves

```lean
theorem sffSchedule_known_optimum {m : ℕ}
    (hm : 0 < m) (hj : 0 < jobs) :
    I.maxFlow (I.sffSchedule m (I.optimum m hm) (I.optimum_pos hm hj)) ≤
      44 * (I.optimum m hm) ^ 2
```

The SFF proof derives the batch work/eligibility bounds, at most one
large-to-small switch per round, at most `4*L` small batches, at most `4*L`
steps per round, at most `16*m*L²` remaining eligible work, and the aggregate
interference bound. It also bounds the delay from eligibility to admission.
The argument works for every positive upper bound `L` on offline flow; the
theorem above specializes it to the actual optimum.

`SFFRounds` describes the fixed-frontier routine through local operational
conditions: its exact round-length formula, frontier clearing, a fixed
oldest large filler, packed execution slots, and which vertices may run in
a round. It contains no backlog, round-count, round-length upper bound,
interference bound, or flow guarantee. `Batching.execution_rounds` now
constructs a value of this specification from the deterministic executor;
the main scheduler theorem requires no assumed execution witness.

The construction has three layers:

1. `ReadySnapshot` plans a round using exposed ready frontiers and public
   batch labels. It packs small-frontier vertices in a fixed order and uses
   the oldest large batch to fill the final slot.
2. `Batching.run` updates timestamp state. Its checked invariant guarantees
   eligibility, precedence, processor capacity, and that timestamps never
   change after assignment. Timestamp lookups use cached vectors.
3. `Batching.terminates` proves that after the last eligibility time, each
   unfinished round completes a new vertex. A finite prefix therefore
   contains timestamps for every vertex. `execution_rounds` identifies
   these timestamps with the ready-snapshot actions at every round.

`ReadySnapshot.ready_only` proves that identical exposed frontiers give
identical durations, filler choices, actions, and local assignments, even
if other observation fields differ. The planner never reads hidden edges,
topological ranks, or an offline comparison schedule. The environment
simulator uses the input DAG to expose vertices when their predecessors
finish; the planner receives only its resulting snapshots.

The finite horizon used to extract the total assignment is not used by the
round planner. The public-history realization covers different hidden vertex and batch counts,
and proves invariance under increasing identifier renamings used by residual phases.

## Model

An instance has finitely many jobs and vertices. Every vertex has one owner;
edges remain inside a job; a topological rank witnesses acyclicity. Each
vertex takes one unit of time. A schedule assigns a natural-number execution
slot to every vertex and obeys release, precedence, and processor-capacity
constraints. Completion is one plus the last execution slot. Maximum flow
is the maximum completion-minus-release value.

The FIFO predicate states work conservation and priority by job release
time, with arbitrary tie-breaking for jobs sharing a release. The theorem
applies to every valid total schedule satisfying these conditions. Both FIFO and SFF have executable constructions realizing their specifications.
Topological ranks and offline schedules are used in proofs; they are not
inputs to the FIFO policy predicate or to the SFF round planner.

The proofs include unrevealed vertices in remaining work. Readiness tests all
immediate predecessors, as in the paper.

`DeterministicScheduler` assigns a valid total schedule to every finite
instance and satisfies causality across equal revealed-graph histories,
including instances with different hidden dimensions. `RandomizedScheduler`
is a measurable family of these schedulers indexed by an arbitrary seed
space. The seed distribution is any probability measure; it need not have
finite or countable support. The expected-flow conclusions select a single
finite input independently of the seed. The model uses total, terminating
executions on finite inputs. The formalization concerns the paper's own
main results and supporting scheduling arguments, not the cited prior work.

## Files

| Module | Contents |
| --- | --- |
| `Scheduling/Model.lean` | Instance, valid schedule, readiness, maximum flow, FIFO predicate |
| `Scheduling/Counting.lean` | Capacity counting, Proposition 5, ready-vertex existence |
| `Scheduling/Backlog.lean` | Work conservation and complete proof of Lemma 9 |
| `Scheduling/FIFO.lean` | Partial-slot progress and Theorem 8 |
| `Scheduling/FIFOConstruction.lean` | Executable FIFO, termination, feasibility, priority, and upper bounds |
| `Scheduling/Optimum.lean` | Feasible offline schedule, attained optimum, FIFO competitive theorem |
| `Scheduling/FrontierProgress.lean` | Batch frontier-clearing progress and at most L marked rounds |
| `Scheduling/SFFModel.lean` | Batching, eligibility, ready frontiers, operational round specification |
| `Scheduling/SFFRoundBounds.lean` | Switch counting and full proof of Lemma 12 |
| `Scheduling/SFFWork.lean` | Admission work conservation and full proof of Lemma 13 |
| `Scheduling/SFFInterference.lean` | Old-service charges, younger-frontier charges, duration bound |
| `Scheduling/SFF.lean` | Admission delay, canonical batching, SFF upper bound against the actual optimum |
| `Scheduling/Packing.lean` | Executable deterministic packing of finite frontiers into slots |
| `Scheduling/RoundPlanner.lean` | Executable round decisions, local correctness, ready-only dependence |
| `Scheduling/Execution.lean` | Stateful round execution, prefix feasibility, timestamp preservation |
| `Scheduling/Termination.lean` | Finite completion and valid total scheduling assignment |
| `Scheduling/ExecutionBridge.lean` | Exact relation between simulator state, actions, and execution timestamps |
| `Scheduling/SFFConstruction.lean` | Constructed SFF rounds, schedule, upper bound, and existence theorem |
| `Scheduling/Examples.lean` | A chain-plus-fork runtime regression and its proved schedule validity |
| `Scheduling/PhaseTransport.lean` | Phase-local clocks, offline transport, and valid schedule splicing |
| `Scheduling/PhaseFailure.lean` | First failed deadlines, failed guesses, and restart invariant |
| `Scheduling/Combined.lean` | Finite doubling controller and `352 OPT min(m, OPT)` flow bound |
| `Scheduling/Information.lean` | Public policies, history indistinguishability, and FIFO non-clairvoyance |
| `Scheduling/PublicSFF.lean`, `Scheduling/PackingTransport.lean` | Natural-label round observations and packing transport |
| `Scheduling/SFFHistory.lean`, `Scheduling/SFFNonclairvoyant.lean` | Public SFF history policy and cross-instance non-clairvoyance |
| `Scheduling/Renaming.lean` | Policy invariance under increasing identifier renaming |
| `Scheduling/PhaseInformation.lean`, `Scheduling/PhaseObservations.lean` | Visible deadline failures and transport of phase observations |
| `Scheduling/PublicCombined.lean` | Causal public controller and full combined-schedule realization |
| `Scheduling/Residual.lean` | Induced residual instance and shifted optimal schedule |
| `Scheduling/Batched.lean` | Lemma 17 and the integer geometric recurrence |
| `Scheduling/BatchedRecords.lean` | Concrete record inequality, Lemma 18, and Theorem 4 upper bound |
| `Scheduling/OfflinePipeline.lean`, `Scheduling/LayeredForest.lean` | Concrete layered forests, out-forest proof, offline schedule, and `L ≤ OPT ≤ 2L` |
| `Scheduling/RegularBacklog.lean` | Concrete epoch conservation, young-job count, and forcing contradiction |
| `Scheduling/LayeredExecution.lean`, `Scheduling/LayeredForcing.lean` | Key-last layer execution, narrow-layer forcing, and conditional competitive lower bound |
| `Scheduling/PublicGraph.lean`, `Scheduling/HiddenKey.lean` | Full revealed-graph scheduler model, hidden-edge replacement, and deferred key selection |
| `Scheduling/LayeredPrefix.lean`, `Scheduling/LayerAdversary.lean` | Partial forest states, chronological adaptive construction, and termination |
| `Scheduling/LayerChronology.lean`, `Scheduling/LayerRecords.lean`, `Scheduling/JobLayers.lean` | Final key-last certificates, exact layer-size rules, and per-job layer ordering |
| `Scheduling/LayerCount.lean`, `Scheduling/KeyOrder.lean`, `Scheduling/AdversaryOffline.lean` | Layer-count bound and concrete offline schedule for the extracted adversarial forest |
| `Scheduling/ForcingTrace.lean`, `Scheduling/AdversaryForcing.lean`, `Scheduling/DeterministicLower.lean` | Actual forcing-window analysis and quantified deterministic lower bound |
| `Scheduling/StarChain.lean`, `Scheduling/StarChainAdversary.lean` | Rooted stars and chains, `OPT ≤ 6`, and fixed-instance realization of adaptive type choices |
| `Scheduling/StarChainFIFO.lean`, `Scheduling/FIFOLower.lean` | FIFO invariants, recurring idle slots, and the quantified constant-OPT lower bound |
| `Scheduling/OfflineBatched.lean`, `Scheduling/BalancedLayers.lean` | Single-epoch offline packing and exact optimum for canonical balanced layers |
| `Scheduling/FlexibleLayers.lean` | Terminating history-dependent layer construction and transfer to recorded-run certificates |
| `Scheduling/BatchedLayerRule.lean`, `Scheduling/BatchedLayerBudget.lean` | Concrete threshold rule, exact layer counts, and prefix-balance invariant |
| `Scheduling/BatchedForcingArithmetic.lean` | Conditional passivity recurrence and every-epoch backlog contradiction |
| `Scheduling/KeyPrefix.lean`, `Scheduling/RecordedKeys.lean`, `Scheduling/BatchedParentCuts.lean` | Actual key counts, balanced parent boundaries, and leaf-order precedence |
| `Scheduling/BatchedAdversaryOffline.lean` | Exact `OPT = L` for the constructed batched graph |
| `Scheduling/BatchedHistory.lean`, `Scheduling/BatchedWideWork.lean` | Final-execution rule certificates and wide-work lower bound in full epochs |
| `Scheduling/BatchedCredit.lean`, `Scheduling/BatchedCounters.lean`, `Scheduling/BatchedChoice.lean` | Passivity credit, concrete counter transitions, and threshold consequences of the rule |
| `Scheduling/BatchedFrontierCredit.lean`, `Scheduling/BatchedRecordCredit.lean`, `Scheduling/BatchedRevealTimes.lean` | Credit preservation on the actual adaptive run and fixed reveal times for every layer |
| `Scheduling/BatchedWideUpper.lean` | Per-job cutoffs bounding total and suffix wide service in every full epoch |
| `Scheduling/BatchedCutoffArithmetic.lean`, `Scheduling/BatchedAggregate.lean` | Sorted cutoff aggregation and the actual suffix-service recurrence |
| `Scheduling/BatchedForcing.lean`, `Scheduling/BatchedLower.lean` | Every-epoch deficit, backlog contradiction, and quantified deterministic batched lower bound |
| `Scheduling/FiniteForests.lean`, `Scheduling/HardFamilies.lean` | Finite parent-table encoding and fixed hard families for both lower bounds |
| `Scheduling/AppendInstance.lean`, `Scheduling/AppendRestriction.lean` | Separated-copy schedules, local restrictions, optimum bounds, and preservation of batched releases and out-forests |
| `Scheduling/AppendObservation.lean`, `Scheduling/AppendBefore.lean` | Full public-observation decomposition and preservation of execution and flow bounds before future releases |
| `Scheduling/AppendContinuation.lean`, `Scheduling/HardContinuation.lean` | Causal continuation and hard family members after any fixed preceding instance |
| `Scheduling/InstanceSequence.lean`, `Scheduling/FiniteAmplification.lean` | Finite words of separated instances, preservation of instance properties, and the exact counting bound |
| `Scheduling/Randomized.lean`, `Scheduling/RandomizedFamily.lean` | Measurable randomized schedulers, finite-input averaging, and amplified hard families |
| `Scheduling/RandomizedLower.lean` | Both randomized lower bounds against an oblivious adversary, with explicit constants |
| `Scheduling/Schedulers.lean` | Shared observation interface, causal FIFO and combined algorithms, and the unified upper-bound existence theorem |
| `Scheduling/Accounting.lean` | Conditional forcing-epoch and SFF accounting inequalities |
| `Audit.lean` | Axiom reports for the main statements |

## Build

The project pins Lean and Mathlib to **v4.33.0**, with dependency commits in
`lake-manifest.json`. The supplied archive used v4.24.0; this continuation
updates the dependency pin and adapts renamed Finset lemmas and simplification
steps. The mathematical statements of the existing results are unchanged.

After installing elan:

```bash
cd nonclairvoyant-scheduling-lean
lake exe cache get
./verify.sh
```

`verify.sh` builds every imported module, checks for proof holes and custom
axiom declarations or native proof shortcuts in project source, and runs
`Audit.lean`. It also checks every requested dependency report and rejects
axioms outside `propext`, `Classical.choice`, and `Quot.sound`.

The examples check FIFO timestamps `[0, 1, 2, 0, 1, 2]` and SFF timestamps
`[6, 7, 8, 6, 7, 8]` on a chain and a
fork with two processors and `L=3`. Both jobs finish at time 9 after batch
eligibility at time 6. Its middle round exercises large-filler processing.
The timestamp-list check is a compiled runtime regression; its validity is
also proved by the general scheduler theorem. Runtime evaluation is not
used as an axiom or as a shortcut in any mathematical proof.

The archive contains source and verification output, not a bundled Lean
installation or Mathlib cache. A first build therefore needs network access
to download the pinned dependencies.

## Trust and limitations

The project contains no `sorry`, `admit`, or custom axiom declarations.
The important theorem dependency reports use only Lean's usual
`propext`, `Classical.choice`, and `Quot.sound` where needed. The arithmetic
proofs are checked by Lean; no native-evaluation proof shortcut is used.

The proofs are checked against the finite discrete-time definitions described
above. As with any formalization, the correspondence between those definitions
and the paper's intended model is a separate mathematical interpretation;
the exact assumptions and guarantees are visible in the main declarations.
