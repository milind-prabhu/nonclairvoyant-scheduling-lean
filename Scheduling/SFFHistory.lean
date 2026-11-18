import Scheduling.PublicSFF

namespace Scheduling
open Finset

abbrev SFFMemory := Option (PublicSnapshot × ℕ)

/-- At a boundary, cache the public frontier and begin slot zero. During a
round, use the cached frontier and ignore newly revealed work until the
next boundary, exactly as in the fixed-frontier executor. -/
def sffStep (m : ℕ) (_t : ℕ) (observation : PublicSnapshot) (state : SFFMemory) :
    Finset ℕ × SFFMemory :=
  let plan := state.getD (observation, 0)
  (plan.1.action m plan.2,
    if plan.2 + 1 < plan.1.duration m then some (plan.1, plan.2 + 1) else none)

def sffPolicy (m : ℕ) : OnlinePolicy PublicSnapshot SFFMemory (Finset ℕ) where
  initial := none
  step := sffStep m

def roundMemory (m : ℕ) (Q : PublicSnapshot) (j : ℕ) : SFFMemory :=
  if 0 < j ∧ j < Q.duration m then some (Q, j) else none

theorem sffStep_roundMemory (m t j : ℕ) (Q observation : PublicSnapshot)
    (hj : j < Q.duration m) (hobs : j = 0 → observation = Q) :
    sffStep m t observation (roundMemory m Q j) =
      (Q.action m j, roundMemory m Q (j + 1)) := by
  by_cases hz : j = 0
  · subst j
    rw [hobs rfl]
    simp [sffStep, roundMemory]
  · have hp : 0 < j := by omega
    simp [sffStep, roundMemory, hp, hj]

theorem sffPolicy_round_state (m : ℕ) (history : ℕ → PublicSnapshot)
    (a : ℕ) (Q : PublicSnapshot)
    (ha : (sffPolicy m).state history a = none) (hQ : history a = Q)
    (j : ℕ) (hj : j ≤ Q.duration m) :
    (sffPolicy m).state history (a + j) = roundMemory m Q j := by
  induction j with
  | zero => simpa [roundMemory] using ha
  | succ j ih =>
    have hprev := ih (by omega)
    have hstep := sffStep_roundMemory m (a + j) j Q (history (a + j))
      (by omega) (by intro hz; simpa [hz] using hQ)
    change ((sffPolicy m).step (a + j) (history (a + j))
      ((sffPolicy m).state history (a + j))).2 = _
    rw [hprev]
    exact congrArg Prod.snd hstep

theorem sffPolicy_round_decision (m : ℕ) (history : ℕ → PublicSnapshot)
    (a : ℕ) (Q : PublicSnapshot)
    (ha : (sffPolicy m).state history a = none) (hQ : history a = Q)
    (j : ℕ) (hj : j < Q.duration m) :
    (sffPolicy m).decision history (a + j) = Q.action m j := by
  unfold OnlinePolicy.decision
  rw [sffPolicy_round_state m history a Q ha hQ j hj.le]
  exact congrArg Prod.fst (sffStep_roundMemory m (a + j) j Q (history (a + j))
    hj (by intro hz; simpa [hz] using hQ))

namespace Batching
variable {jobs vertices batches L : ℕ} {I : Instance jobs vertices}
variable (B : Batching I L batches) [DecidableRel I.edge]

/-- The environment reveals ready frontiers based on work completed strictly
before the current slot. The result has no hidden-instance size parameter. -/
def publicHistory (m t : ℕ) : PublicSnapshot :=
  (B.observe ⟨t, fun v => if B.execution m v < t then some (B.execution m v) else none⟩).expose

theorem publicHistory_boundary {m : ℕ} (hm : 0 < m) (k : ℕ) :
    B.publicHistory m (B.run m k).clock = (B.observe (B.run m k)).expose := by
  unfold publicHistory
  have he : (⟨(B.run m k).clock,
      fun v => if B.execution m v < (B.run m k).clock then some (B.execution m v) else none⟩ :
      ExecutionState vertices) = B.run m k := by
    have hstamp := funext (fun v => (B.run_stamp_exact hm k v).symm)
    cases h : B.run m k with
    | mk c stamp =>
      simp only [h] at hstamp ⊢
      exact congrArg (ExecutionState.mk c) hstamp
  rw [he]

theorem publicPolicy_boundary_state {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (sffPolicy m).state (B.publicHistory m) (B.run m k).clock = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := sffPolicy_round_state m (B.publicHistory m) (B.run m k).clock
      (B.observe (B.run m k)).expose ih (B.publicHistory_boundary hm k)
      ((B.observe (B.run m k)).expose.duration m) le_rfl
    rw [ReadySnapshot.expose_duration] at h
    change (sffPolicy m).state (B.publicHistory m)
      ((B.run m k).clock + (B.observe (B.run m k)).duration m) = none
    simpa only [roundMemory, ReadySnapshot.expose_duration, lt_self_iff_false,
      and_false, ↓reduceIte] using h

theorem exists_execution_round (m t : ℕ) :
    ∃ k, (B.run m k).clock ≤ t ∧ t < (B.run m (k + 1)).clock := by
  have hex : ∃ k, t < (B.run m k).clock :=
    ⟨t + 1, lt_of_lt_of_le (by omega) (B.run_clock_ge m (t + 1))⟩
  let n := Nat.find hex
  have hn : t < (B.run m n).clock := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp [he, run, ExecutionState.initial] at hn
  refine ⟨n - 1, ?_, ?_⟩
  · by_contra h
    have hmin := Nat.find_min' hex (show t < (B.run m (n - 1)).clock by omega)
    change n ≤ n - 1 at hmin
    omega
  · simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hn

/-- The finite scheduling assignment is exactly the slot-by-slot public
policy on its environment's observation history. -/
theorem execution_publicPolicy {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (univ.filter (fun v => B.execution m v = t)).image Fin.val =
      (sffPolicy m).decision (B.publicHistory m) t := by
  obtain ⟨k, hk₁, hk₂⟩ := B.exists_execution_round m t
  have hj : t - (B.run m k).clock < (B.observe (B.run m k)).expose.duration m := by
    rw [ReadySnapshot.expose_duration]
    change t < (B.run m k).clock + (B.observe (B.run m k)).duration m at hk₂
    omega
  have hp := sffPolicy_round_decision m (B.publicHistory m) (B.run m k).clock
    (B.observe (B.run m k)).expose (B.publicPolicy_boundary_state hm k)
    (B.publicHistory_boundary hm k) (t - (B.run m k).clock) hj
  rw [Nat.add_sub_of_le hk₁, ReadySnapshot.expose_action] at hp
  rw [B.execution_slot_eq hm hk₁ hk₂]
  exact hp.symm

/-- Equal public history prefixes force equal SFF decisions across arbitrary
finite hidden domains. No equality of hidden DAGs, domain sizes, or future
batch sets is required. -/
theorem execution_nonclairvoyant {otherJobs otherVertices otherBatches otherL m : ℕ}
    {J : Instance otherJobs otherVertices} (C : Batching J otherL otherBatches)
    [DecidableRel J.edge] (hm : 0 < m) (t : ℕ)
    (h : ∀ u ≤ t, B.publicHistory m u = C.publicHistory m u) :
    (univ.filter (fun v => B.execution m v = t)).image Fin.val =
      (univ.filter (fun v => C.execution m v = t)).image Fin.val := by
  rw [B.execution_publicPolicy hm, C.execution_publicPolicy hm]
  exact (sffPolicy m).decision_eq_of_history_eq _ _ t h

end Batching
end Scheduling
