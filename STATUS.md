# Coverage against arXiv:2610.11006v1

All four main theorems are proved in the finite discrete-time scheduling
model, including the general and batched randomized lower bounds. Theorem
numbers refer to the public v1 PDF. A checked arithmetic implication is not
counted as a full scheduling theorem.

| Paper result | Current status | Main declarations |
| --- | --- | --- |
| Section 2: finite DAG scheduling and flow | Formal definitions and causal public-history realizations for FIFO, SFF, and the combined controller verified | `Instance`, `Valid`, `Ready`, `IsFIFO`, `completion`, `maxFlow`, `run_safe`, `terminates`, `execution_valid` |
| Proposition 5(1): path length | Verified | `path_length_bound` |
| Proposition 5(2): per-job and interval work | Verified | `job_work_bound`, `arrival_work_bound` |
| Lemma 9: FIFO backlog | Verified from the schedule model | `fifo_backlog_bound` |
| Theorem 8: FIFO factor m+1-1/m | Verified for the executable FIFO constructor and every valid FIFO schedule, including a proved attained offline optimum | `fifoSchedule_competitive`, `fifo_maxFlow_bound`, `fifo_competitive` |
| SFF progress observation (1) | Verified for batches whose marked rounds clear their starting frontier | `frontier_round_progress`, `frontier_round_count_bound` |
| Lemma 11: batch bounds | Verified work bounds and denominator-free eligibility counting | `batch_work_bound`, `eligible_count_bound`, `eligible_count_scaled`, `eligible_work_bound` |
| Lemma 12: round lengths and number of small batches | Verified from the operational SFF round specification | `switches_card_le_one`, `small_cover`, `round_bounds` |
| Lemma 13: SFF remaining work | Verified by concrete admitted-work conservation | `admitted_accounting`, `sparse_work_bound`, `remaining_work_bound` |
| Theorem 10: SFF maximum flow ≤44 OPT² | Executable scheduler, validity, termination, round-specification realization, existence, upper bound, and cross-instance public-history non-clairvoyance verified | `execution_rounds`, `sffSchedule_valid`, `sffSchedule_bound`, `sffSchedule_known_optimum`, `exists_sff_schedule`, `ready_only` |
| Section 4.3: shifting and residual restriction | Verified for concrete induced instances, phase-local clocks, and splicing into completed prefixes | `phase_optimum_le`, `splice_valid`, `residual_optimum_le` |
| Theorem 2: combined scheduler | Verified: finite phase construction, feasibility, failure detection, doubling, bound `352 OPT min(m, OPT)`, and a causal scheduler in the same model as the lower bounds | `combinedSchedule_spec`, `combinedScheduler`, `exists_optimal_order_scheduler` |
| Lemma 17: batched residual work and prefix-idle count | Verified from the concrete model | `batch_remaining_work_bound`, `batch_prefix_idle_lt` |
| Lemma 18: logarithmic record bound | Verified from concrete FIFO record states, including the record inequality and the ceiling-logarithm count | `record_prefix_idle`, `record_batch_count` |
| Theorem 4 upper bound | Verified for every valid FIFO schedule with arrivals at multiples of the attained optimum; both bounds combined | `batched_fifo_competitive`, `batched_fifo_combined_bound` |
| Lemma 6 offline schedule for layered forests | Verified for both the static forest model and the adaptively constructed instance; layer count and key-first ordering are derived | `RecordedRun.forcing_layer_count`, `RecordedRun.offline_schedule`, `RecordedRun.optimum_bounds` |
| Lemma 7 forcing capacity calculation | Verified for the actual constructed instance under the contradiction hypothesis of small flow | `RecordedRun.forcing_trace`, `RecordedRun.forcing_interval_work`, `RecordedRun.forcing_epoch_deficit` |
| Theorem 1 deterministic lower bound | Verified for every deterministic causal scheduler: explicit finite out-forest, `L ≤ OPT ≤ 2L`, online flow at least `cL`, and `min(m, OPT) * OPT ≤ 64 * maxFlow` | `deterministic_lower_bound`, `deterministic_competitive_lower` |
| Theorem 1 randomized lower bound | Verified: one fixed out-forest has `L ≤ OPT ≤ 2L` and `min(m, OPT) * OPT ≤ 128 * E[maxFlow]`, for an arbitrary probability space of measurable causal schedulers | `randomized_lower_bound`, `randomized_competitive_lower` |
| Theorem 3 / Theorem 14: FIFO lower bound with constant OPT | Verified for every deterministic causal FIFO scheduler: explicit finite rooted trees of height at most three, `OPT ≤ 6`, flow at least `3*(m-1)`, and `m*OPT ≤ 4*maxFlow` | `StarChain.root_reaches`, `fifo_constant_optimum_lower`, `fifo_competitive_lower` |
| Theorem 4 deterministic batched lower bound | Verified for every deterministic causal scheduler: `OPT = 8*c*5^c`, releases at multiples of OPT, flow at least `c*OPT`, and `min m (Nat.clog 2 OPT) * OPT ≤ 7*maxFlow`, for positive `c` with `2*c ≤ m` | `batched_lower_bound`, `batched_competitive_lower` |
| Theorem 4 randomized batched lower bound | Verified: one fixed out-forest has `OPT = 8*c*5^c`, releases at multiples of OPT, and `min m (Nat.clog 2 OPT) * OPT ≤ 14 * E[maxFlow]`, for positive `c` with `2*c ≤ m` | `randomized_batched_lower_bound`, `randomized_batched_competitive_lower` |

## What the component theorems assume

`frontier_round_count_bound` assumes a monotone sequence of round boundaries,
that all vertices of the batch have arrived by each marked round, predecessor closure,
and that every marked round processes all vertices ready at its start. It
derives the bound on marked-round count. It does not assume a depth-drop or
marked-round-count bound. `SFFRounds.small_round_count` now instantiates
these hypotheses using actual eligible batches and their ready frontiers.

`SFFRounds` is an operational specification on a concrete finite scheduling
assignment and an infinite sequence of round boundaries. Its fields state
the exact round-length formula, clearing of the initial small frontiers,
use of one fixed oldest large filler, eligibility restrictions, packing of
nonfinal slots, filling of the last slot when a large batch exists, and the
allowed sources of service in a round. These are local properties of the
paper's pseudocode. No analytical guarantee is included as a field.

`round_bounds`, `remaining_work_bound`, and `sff_known_optimum` derive the
analytical guarantees from that specification. The executable construction
now supplies all its fields: `execution_rounds` takes no assumed round trace
and no analytical guarantee. `sffSchedule_bound` applies the analysis to the
constructed scheduler, and `exists_sff_schedule` supplies the existence
claim for every finite instance with an offline flow bound.

The public SFF policy caches the starting frontier for each round and reads
new observations only at round boundaries. `sffSchedule_publicPolicy` proves
that this policy realizes the constructed schedule; `sffSchedule_nonclairvoyant`
proves equal decisions from equal public observation prefixes, including across
instances with different numbers of hidden vertices and batches. Packing and
round decisions commute with increasing identifier renamings.

`residual_optimum_le` constructs the induced instance by reindexing both the
surviving vertices and their active jobs. It proves all schedule constraints
and the flow bound under a uniform time shift. It does not merely assume
that an abstract residual instance has small optimum.

`batch_remaining_work_bound` derives the lower bound on offline execution
times of the remaining vertices from FIFO's partial-slot progress, then
counts their feasible offline slots. Its work bound is not a hypothesis.

`LayeredForest` constructs actual instances with one key per layer and
at most one parent per vertex. Its keys come first in the offline indexing;
this indexing is not yet an adversarial labeling for online algorithms.
`offline_schedule` supplies all three feasibility constraints for the paper's
pipelined schedule, and `optimum_bounds` derives `L ≤ OPT ≤ 2L` from exact
job sizes and the bound on layer count.

`KeyLast` states that each key is executed in the last slot used by its layer.
From this property, `layer_execution_order` proves that the algorithm exhausts
each layer before processing the next, and `ready_same_layer` proves that each
job exposes at most one unfinished layer. `NewLayersNarrow` restricts the sizes
of layers revealed during a forcing interval. The local processed-work bound,
an idle slot, and the forcing-epoch deficit are all derived from these two
structural conditions. `regular_idleBacklog_eq` identifies accumulated idle
capacity with actual unfinished vertices; `regular_young_backlog` counts the
last unfinished jobs. `forcing_competitive_lower` combines these results with
the attained offline optimum. It does not yet quantify over online algorithms:
the final quantified theorem now constructs and analyzes the adversarial
instance directly, as described below. The older conditional forest results
remain reusable components, but they are not assumptions of the main theorem.

The older standalone numerical lemma `Accounting.sff_duration_bound` assumes
the service and interference inequalities. Those inequalities are now
derived separately in `SFFInterference.lean`; the main SFF theorem uses the
new concrete round analysis rather than treating those bounds as inputs.
`geometric_record_sum` is still a standalone conditional arithmetic lemma.
The new `record_prefix_idle` derives that inequality from actual strict record
backlogs using prefix-work conservation and `batch_remaining_work_bound`.
`record_batch_count` handles arbitrary sets of unfinished batches (including
gaps), and `batched_backlog_bound` extends the record bound to every batch
boundary. `batched_fifo_competitive` proves the ceiling-logarithm flow bound
relative to the attained offline optimum; `batched_fifo_combined_bound` takes
the minimum with the exact general-arrival FIFO bound. No record inequality
or backlog bound is assumed by these final theorems. As in the general FIFO
result, validity and the local FIFO rule are hypotheses on the schedule;
the executable `fifoSchedule` now supplies both hypotheses via
`fifoSchedule_valid` and `fifoSchedule_isFIFO`. Its termination proof uses
only acyclicity and progress after the last arrival; no offline bound is an
input. `fifoSchedule_batched_bound` applies the logarithmic guarantee directly
to that constructor.

`Information.lean` defines public observations using natural-number labels,
without encoding the total hidden vertex or job count. `fifoSelect_public`
identifies the implemented selector with a single function of that public
observation. `fifoSchedule_nonclairvoyant` proves identical execution choices
for two instances with identical current ready observations, even when their
numbers of jobs and vertices differ. The generic `OnlinePolicy` also proves
state and decision equality from equal observed history prefixes. SFF is linked to this interface by `sffSchedule_publicPolicy`. The combined
controller uses the same raw observations, with proved causality.

`combinedSchedule_spec` constructs the full assignment by recursively running
fresh SFF phases, stopping at the first failed deadline, doubling the guess,
and switching to the constructed FIFO schedule. Its proof derives each phase's
guarantee from the original offline optimum and preserves every completed
prefix. The initial serial assignment is only an empty-prefix representation
at time zero; none of its timestamps are executed. Residual vertices are
reindexed in increasing identifier order to preserve deterministic tie-breaking.
`combinedSchedule_publicPolicy` proves that this finite assignment is realized
by the computable `publicCombined` decision function. That function scans only
observed deadlines through the queried time and uses the public SFF/FIFO policies
on delayed observations. `publicCombined_causal` and
`combinedSchedule_nonclairvoyant` establish causality and cross-instance
non-clairvoyance, including the restart decisions. Failure visibility is derived
from unfinished ready vertices; no hidden job-completion oracle is assumed.

## Adaptive adversary construction

`PublicGraph.lean` defines `DeterministicScheduler` using the full public
information permitted by the paper: released jobs, revealed vertices and
owners, revealed edges, and ready vertices. The scheduler must supply a valid
total schedule on every finite DAG and identical decisions on identical public
history prefixes. This covers algorithms with finite maximum flow; failure to
complete a finite instance already precludes a finite competitive guarantee.

`hidden_replacement` proves that changing hidden incoming edges preserves the
execution prefix when both old and new edges keep the changed vertices hidden.
`select_hidden_key` uses a temporary barrier to select a last frontier vertex;
the barrier's outgoing edges are never visible during the prefix being fixed.
Thus the proof does not assume an algorithm cannot distinguish visible joins
from trees.

`LayeredPrefix` represents closed layers, one current frontier per job, and
unrevealed suffixes. Each advance commits a key, gives the next frontier that
parent, and preserves all earlier decisions. `CompletionRun` always advances
an earliest finishing frontier and terminates because `remainingMass` strictly
decreases. At completion no barriers remain and every vertex has at most one
parent. The actual forcing-window layer-size rule is supplied by
`forcingLayerRule`, with first forcing time obtained by rounding the job's
release epoch up to a multiple of `c`.

`RecordedRun` retains every layer's vertex interval, chosen key, and closing
time. Its intervals cover the jobs and do not overlap within a job. Every
chosen key runs last in its layer in the final fixed instance; parents of
subsequently revealed layers are the recorded keys. `job_layers` proves that
the intervals tile each job and that every new width equals the rule's value
at the preceding closing time plus one. `job_times_pairwise` proves that
closing times strictly increase within each job. These are derived from the
causal construction, rather than assumed as adversary hypotheses.

## Quantified deterministic lower bound

`forcing_layer_count` proves that the actual records contain at most `L`
layers per job. Narrow-layer requests inject into a single forcing half-epoch;
wide layers are charged to the job's `mL` work, allowing one final partial
layer. `KeyOrder.lean` constructs an injective ordering with all recorded keys
first. Every edge source is a recorded key, so `pipeline_valid` gives the
actual extracted instance a schedule with flow at most `2L`. The work lower
bound gives `L ≤ OPT`.

`RecordedRun.forcing_trace` derives the local timing and narrow-layer
conditions from final parent edges and key timestamps. Under a `cL` flow
bound, `alive_firstForcingTime` proves that every alive job is in its first
forcing half-epoch. The service bound then forces an idle slot, and concrete
backlog conservation yields a contradiction.

`deterministic_lower_bound` quantifies over every `DeterministicScheduler m`
and constructs an out-forest with `c * (c * (m * L))` jobs, `mL` vertices per
job, `L ≤ OPT ≤ 2L`, and online flow at least `cL`, whenever `m ≥ 2`, `c > 0`,
`L > 0` is even, `16c ≤ L`, and `2c ≤ m`. It assumes neither a hidden-key
trace nor an offline schedule. `deterministic_competitive_lower` chooses
`c = min (m/2) (L/16)` for any positive multiple `L` of sixteen and derives

`min m OPT * OPT ≤ 64 * maxFlow (A.schedule I)`.

This is the deterministic `Ω(min(m, OPT))` claim with an explicit absolute
constant and arbitrarily large scale parameter. The randomized extension is
proved separately using finite-family amplification and integration below.

## Constant-optimum FIFO lower bound

`StarChain.toInstance` gives every job `3m` vertices and releases job `j` at
`3j`. This translates the paper's first arrival from slot one to slot zero.
Short jobs are stars; long jobs have a root, one middle vertex, and leaves.
`root_reaches` and `at_most_one_parent` certify rooted out-trees of height
at most three. `offline_schedule` supplies a concrete pipelined schedule
with maximum flow at most six for every choice of job types.

`change_type` applies full revealed-graph causality to prove that changing
a job's type after its root executes preserves every earlier slot and that
slot's middle-vertex set. `exists_type_consistent` successively fixes the
earliest unfixed root and produces one static instance satisfying the
paper's rule: a root receives a long job precisely when its slot executes
no middle vertex. The final lower-bound theorem does not assume this rule
as an input; it derives the instance from the scheduler.

`stateInvariant_all` proves that ready leaves are older than every
unprocessed root and that ready leaves exclude ready middle vertices.
Under the contradiction hypothesis of flow at most `3(m-1)`, fewer than
`m` jobs are alive, so slots without leaves are idle. During a run of
slots with leaves, the ready-leaf set can only shrink; the flow bound
therefore limits such a run. `block_has_idle` proves an idle slot in every
block of `3(m-1)+1` slots. With `(3(m-1)+1)*m*m` jobs, concrete work
conservation contradicts the bound on young remaining jobs.

`fifo_constant_optimum_lower` consequently constructs the fixed instance
for every deterministic causal FIFO scheduler on `m ≥ 2` processors.
`fifo_competitive_lower` states the resulting `m/4` competitive lower bound
without division: `m * OPT ≤ 4 * maxFlow`. No offline schedule, adversarial
trace, type rule, or FIFO invariant is assumed by these two final theorems.

## Deterministic batched lower bound

`OfflineBatched` packs the keys on one processor and the leaves on the
other processors within the same arrival epoch. Its precedence premise
is an explicit inequality on the key-first vertex order. `BalancedLayers`
constructs a canonical forest from the set of wide-layer positions and
the prefix condition. It derives that inequality and proves `OPT = L`
for every nonempty family. The actual adaptive graph is now handled by
`BatchedAdversary.offline_schedule` and `BatchedAdversary.optimum_eq`.
`history_parent_cut` shows that every installed parent edge crosses a
prefix with at least `m` vertices per preceding layer. `RecordedRun.keys_card`
counts the actual distinct keys, and `keyFirstPosition_leaf_after_cut`
turns the prefix bound into the leaf-precedence inequality. The resulting
schedule uses the original labels and edges of the fixed final instance.

`FlexibleRun` permits arbitrary history-dependent layer widths and proves
that every finite such run admits a static `LayerSizeRule` certificate.
The proof changes only rule entries at prefixes already closed, so all
existing `RecordedRun` timing, coverage, and parent-edge results apply.
`HistoryRun` supplies the operational recursion and a termination proof for
every rule that respects the remaining vertex budget and exposes a
nonempty frontier when work remains.

`BatchedAdversary.rule` implements the epoch threshold: it counts wide
vertices processed in the current epoch, uses threshold `(2m-1)*D`, resets
at epoch boundaries, and detects earlier idle slots from the concrete
schedule prefix. It includes explicit wide-count and prefix-balance
guards. `rule_width_shape` proves that valid budgets produce whole layers,
not truncated ones. `exists_balanced_layer_run` constructs a fixed final
instance and certifies that every layer has width `2m-1` or one, every job
has exactly `L/2` of each type, and every chronological prefix has at least
as many wide as narrow layers for every job. `final_job_length` gives
exactly `L` layers. All these properties are derived from the rule.

`BatchedForcing.PassivityBounds` states the suffix-service inequalities
for ordered passivity times. `no_full_epoch` solves that recurrence and
contradicts `L = 8*c*5^c`. The aggregate service inequalities are now
derived from the actual execution, as described below. The prefix guard
is proved not to override the threshold in a full epoch.
`regular_every_epoch_flow_lower` supplies the final backlog contradiction
for `c*m*L` jobs; its every-epoch deficit premise is now discharged by
`BatchedAdversary.forcing_epoch_deficit`.

`history_rule_in_final` proves that every next-layer choice agrees with
its evaluation on the final fixed schedule. This includes the epoch work
counter and idle-slot detector: neither retains a dependency on a partial
graph's potentially different future execution. `nonwide_is_narrow_key`
and `nonwide_same_slot_injective` show that at most one narrow vertex per
job can execute in a slot. `full_epoch_wide_lower` therefore derives the
paper's lower service bound `(m-c)*(b-a)` for any subinterval of a full
epoch under the small-flow contradiction hypothesis.

`ThresholdCredit b d w n x` is the passivity invariant: either
`x ≤ b*(w-n)`, or both `b*d ≤ x` and `d ≤ w-n`. Here `x` is wide work
processed during the epoch, `d` its remaining length, and `w-n` the layer
surplus. The wide and narrow transition lemmas and `CreditTrace.credit`
are checked. `wide_below` proves that a balanced-prefix guard cannot
restart wide service once this invariant holds. `credit_after_record`
now proves preservation for the concrete counter, including epoch resets.
`frontierCredit_advance` carries this certificate through each actual
adaptive step, with final parent edges supplying the new frontier's
execution lower bound. `initial_record_credit` derives the certificate
for every recorded layer, without assuming an abstract credit trace.

`exists_record_reveal_times` assigns a fixed certified reveal time to
each layer. `full_epoch_job_cutoffs` then derives a cutoff `t` for every
job in any full epoch `[iL, (i+1)L)`: its total wide service is at most
`(2m-1)*((i+1)L-t+1)`, and its service in any suffix starting at or after
`t` is at most `2m-1`. The proof chooses the last wide layer revealed
before the epoch ends. Earlier wide layers are completed before its
reveal time, and later layers execute no vertices in the epoch. A layer
revealed before the epoch contributes at most its own width.

`cutoffs_passivity` partitions wide service by job, sorts the alive jobs
by cutoff time, and sums their bounds. At any cutoff, earlier jobs each
contribute at most one wide layer, while later jobs contribute at most
their total epoch work. `full_epoch_passivity` uses the small-flow bound
to limit the alive-job count to `c`, and combines these upper bounds with
`full_epoch_wide_lower`. It derives `PassivityBounds` for the actual
schedule. `forcing_epoch_deficit` applies the geometric contradiction,
and `flow_lower` applies concrete backlog conservation.

`batched_lower_bound` quantifies over every deterministic causal scheduler
on `m ≥ 2` processors and every positive `c` with `2*c ≤ m`. It constructs
a fixed out-forest with `c*m*L` jobs, `m*L` vertices per job,
`L = 8*c*5^c`, exact optimum `L`, and flow at least `c*L`. Each job `j`
is released at `j*OPT`, so the batched-arrival restriction is explicitly
part of the conclusion. No trace, offline schedule, cutoff, credit,
service inequality, or deficit is assumed by the final theorem.
`batched_competitive_lower` uses `Nat.clog 2 L ≤ 7*c` to give the explicit
bound `min m (Nat.clog 2 OPT) * OPT ≤ 7*maxFlow`.

The randomized extension mentioned in Section 6.2 is proved by the
separate amplification and expectation argument below.

## Randomized lower bounds

`ForestCode` encodes each out-forest by a finite parent table on fixed
job and vertex labels. Its ordering condition certifies acyclicity, and
the type has a proved finite enumeration. `ofPrefix_toInstance` identifies
every completed adaptive construction with its code exactly, including
the labels supplied to the online scheduler.

`HardFamily.general` and `HardFamily.batched` filter these codes by the
required offline optimum bounds. They are fixed finite sets independent
of the scheduler. `general_hard` and `batched_hard` prove that every
deterministic causal scheduler has a member of the corresponding family
on which its flow is at least `c*L`. Every member has the required offline
schedule, out-forest structure, and regular release times.

`Instance.append` forms a disjoint union with fresh labels and a time
shift for the second instance. `append_offline` preserves an offline
flow bound when the copies' schedules do not overlap. `leftSchedule_valid`
and `rightSchedule_valid` restrict any valid global execution to valid
local schedules; `maxFlow_left_le` and `maxFlow_right_le` show that local
flow lower bounds transfer to the combined instance. The combined optimum
dominates both local optima. `append_optimum_eq` preserves an exact optimum
under the separation condition, and `append_batched_releases` preserves
release divisibility when the offset is a multiple of the batch length.
`append_outForest` preserves the graph restriction.

`append_graphObservation` decomposes the full public observation into
the old instance's observation and the new instance's observation with
shifted job labels, vertex labels, and release times. It covers arrivals,
visible vertices, visible edges, and ready vertices. Before the second
copy's release, `append_graphObservation_before` identifies the observation
with the old instance alone. Causality then gives `append_slots_before`
and `append_flow_lower`: a future copy cannot change earlier slots or
erase a flow lower bound whose deadlines precede its release.

`DeterministicScheduler.continuation` restricts the execution on an
appended instance and subtracts its release offset. Its validity and full
public-history causality are now proved, even if old jobs remain unfinished.
The causality proof inducts over global time, reconstructing the old
history from earlier equal decisions and the new history from the local
observation hypothesis. It works across different hidden job and vertex
counts. `general_hard_after` and `batched_hard_after` apply the fixed-family
theorems to this continuation. After every fixed preceding instance, at
least one member of the same family forces combined flow at least `c*L`.

`InstanceSequence.concatenate` forms finite words of copies at fixed offsets.
Its proofs preserve the offline bound, a lower bound on the optimum,
out-forest structure, and release divisibility. `bad_persists` shows that a
prefix with flow at least `cL` stays bad. `exists_bad_next` gives a bad next
symbol after every prefix, using the causal continuation results.

For an alphabet of size `N`, `safe_card_le` bounds the number of safe words
of length `k` by `(N-1)^k`. `half_words_bad` proves that at least half the
length-`N` words are bad, using an integer binomial bound. `cost_sum_lower`
turns this count into a lower bound on the sum of flow over all words.
These are exact finite counting statements; no independence or conditional
success estimate is assumed.

`RandomizedScheduler` assigns a deterministic causal scheduler to each seed
in an arbitrary measurable space, with measurable flow on every finite input.
`expectedFlow` is the extended nonnegative integral, so it also handles
infinite expectations. `exists_expected_large` integrates the pointwise
finite sum inequality against any probability measure, interchanges a finite
sum and integral, and selects one fixed word with expected flow at least
`cL/2`. It does not restrict the random seed distribution to finite support.

`HardFamily.expected_lower` instantiates this argument with parent-table
families and stride `(jobs + b + c)*L`, where `bL` is the offline bound.
Every resulting copy fits in the next gap under its offline schedule, and
any earlier `cL` flow threshold is preserved. The fixed concatenation has
`L ≤ OPT ≤ bL` and all releases divisible by `L`.

`randomized_lower_bound` uses `b=2`; `randomized_competitive_lower` chooses
`c = min(m/2, L/16)` and proves
`min m OPT * OPT ≤ 128 * E[maxFlow]` for each positive multiple `L` of sixteen.
`randomized_batched_lower_bound` uses `b=1` and `L=8*c*5^c`, giving exact
optimum `L` and releases at multiples of OPT.
`randomized_batched_competitive_lower` derives
`min m (Nat.clog 2 OPT) * OPT ≤ 14 * E[maxFlow]`.
The input in each conclusion is fixed independently of the seed.

## Shared scheduler model and verification

`readyObservation_eq_of_graphObservation_eq` proves that the frontier
observations used by the executable algorithms are determined by the full
revealed-graph observations used by the lower bounds. `fifoScheduler` and
`combinedScheduler` package the constructed algorithms as valid causal
`DeterministicScheduler` values. `exists_optimal_order_scheduler` states
Theorem 2 as one algorithm working on every finite instance, including the
empty instance. `fifoSchedule_constant_optimum_lower` applies the FIFO lower
bound to the constructed FIFO algorithm.

The model uses finite jobs, unit-time vertices, integral release times,
and total valid schedules. Randomization is a measurable family of total
causal schedulers; nontermination is not represented by a schedule timestamp.
The development proves the paper's main results and their scheduling
arguments, rather than formalizing cited background results or prose.

`verify.sh` builds the root module, scans all project Lean files for proof
holes and unchecked declarations, and checks the axiom reports in `Audit.lean`
against the allowlist `propext`, `Classical.choice`, and `Quot.sound`.
There are no placeholder declarations for missing results.
