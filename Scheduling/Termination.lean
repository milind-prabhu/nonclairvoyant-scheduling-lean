import Scheduling.Execution

namespace Scheduling.Batching
open Finset
variable {jobs vertices batches L : ℕ} {I : Instance jobs vertices}
variable (B : Batching I L batches) [DecidableRel I.edge]

theorem exists_ready_unfinished (s : ExecutionState vertices)
    (hu : ∃ v, s.stamp v = none) :
    ∃ v, s.stamp v = none ∧ ∀ u, I.edge u v → s.stamp u ≠ none := by
  have aux : ∀ n v, I.rank v = n → s.stamp v = none →
      ∃ w, s.stamp w = none ∧ ∀ u, I.edge u w → s.stamp u ≠ none := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hs
      by_cases hp : ∀ u, I.edge u v → s.stamp u ≠ none
      · exact ⟨v, hs, hp⟩
      · push Not at hp
        obtain ⟨u, he, hu⟩ := hp
        exact ih (I.rank u) (by have := I.rank_increases he; omega) u rfl hu
  obtain ⟨v, hv⟩ := hu
  exact aux (I.rank v) v rfl hv

theorem advance_progress {m : ℕ} (hm : 0 < m) (s : ExecutionState vertices)
    (he : ∀ b, B.eligible b ≤ s.clock) (hu : ∃ v, s.stamp v = none) :
    s.completed.card + 1 ≤ (B.advance m s).completed.card := by
  obtain ⟨v, hv, hp⟩ := exists_ready_unfinished (I := I) s hu
  have hobs : v ∈ (B.observe s).ready (B.vertexBatch v) :=
    mem_filter.mpr ⟨mem_univ _, rfl, he _, hv, hp⟩
  obtain ⟨w, k, hk, hw⟩ := (B.observe s).progress hm hobs
  have hready := B.selected_ready hw
  have hn : w ∉ s.completed := by simp [ExecutionState.completed, hready.2.1]
  have hd : w ∈ (B.advance m s).completed := by
    simp [ExecutionState.completed, advance, hw]
  have hc := card_le_card (insert_subset_iff.mpr ⟨hd, B.completed_mono m s⟩)
  rw [card_insert_of_notMem hn] at hc
  exact hc

theorem run_clock_ge (m k : ℕ) : k ≤ (B.run m k).clock := by
  induction k with
  | zero => omega
  | succ k ih =>
    have h := B.clock_strict m (B.run m k)
    change (B.run m k).clock < (B.run m (k + 1)).clock at h
    omega

theorem run_preserves_stamp {m a b : ℕ} (hab : a ≤ b) {v : Fin vertices} {t : ℕ}
    (hv : (B.run m a).stamp v = some t) : (B.run m b).stamp v = some t := by
  induction b, hab using Nat.le_induction with
  | base => exact hv
  | succ b hab ih => exact B.preserves_stamp ih

def lastEligibility : ℕ := univ.sup B.eligible
def completionRound : ℕ := B.lastEligibility + vertices

omit [DecidableRel I.edge] in
theorem eligible_by_last (b : Fin batches) : B.eligible b ≤ B.lastEligibility :=
  le_sup (mem_univ b)

/-- Once all batches are eligible, each unfinished round completes at least
one new vertex. Consequently the construction assigns every finite vertex
an execution time after at most lastEligibility + vertices rounds. -/
theorem terminates {m : ℕ} (hm : 0 < m) (v : Fin vertices) :
    (B.run m B.completionRound).stamp v ≠ none := by
  intro hn
  have hfinal : v ∉ (B.run m B.completionRound).completed := by
    simp [ExecutionState.completed, hn]
  have hcount : ∀ i, i ≤ vertices → i ≤ (B.run m (B.lastEligibility + i)).completed.card := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      have hip := ih (by omega)
      have hv : (B.run m (B.lastEligibility + i)).stamp v = none := by
        by_contra hne
        have hmem : v ∈ (B.run m (B.lastEligibility + i)).completed :=
          mem_filter.mpr ⟨mem_univ _, hne⟩
        have hsub := B.run_completed_mono m (show B.lastEligibility + i ≤ B.completionRound by unfold completionRound; omega)
        exact hfinal (hsub hmem)
      have he : ∀ b, B.eligible b ≤ (B.run m (B.lastEligibility + i)).clock := by
        intro b
        have h₁ := B.eligible_by_last b
        have h₂ := B.run_clock_ge m (B.lastEligibility + i)
        omega
      have hp := B.advance_progress hm (B.run m (B.lastEligibility + i)) he ⟨v, hv⟩
      have hidx : B.lastEligibility + i + 1 = B.lastEligibility + (i + 1) := by omega
      change (B.run m (B.lastEligibility + i)).completed.card + 1 ≤
        (B.run m (B.lastEligibility + i + 1)).completed.card at hp
      rw [hidx] at hp
      omega
  have hc := hcount vertices le_rfl
  change vertices ≤ (B.run m B.completionRound).completed.card at hc
  have heq : (B.run m B.completionRound).completed = univ :=
    eq_of_subset_of_card_le (subset_univ _) (by simpa using hc)
  rw [heq] at hfinal
  exact hfinal (mem_univ _)

def execution (m : ℕ) : Assignment (vertices := vertices) :=
  fun v => ((B.run m B.completionRound).stamp v).getD 0

theorem execution_stamp {m : ℕ} (hm : 0 < m) (v : Fin vertices) :
    (B.run m B.completionRound).stamp v = some (B.execution m v) := by
  have hn := B.terminates hm v
  cases h : (B.run m B.completionRound).stamp v with
  | none => exact False.elim (hn h)
  | some t => simp [execution, h]

/-- The executable construction produces a valid scheduling assignment.
It does not take an offline comparison schedule as input. -/
theorem execution_valid {m : ℕ} (hm : 0 < m) : I.Valid m (B.execution m) := by
  have hs := B.run_safe m B.completionRound
  constructor
  · intro v
    have ht := (hs.stamps v (B.execution m v) (B.execution_stamp hm v)).1
    have hr := B.released_by_eligible (v := v) rfl
    omega
  · intro u v he
    have ht := (hs.stamps v (B.execution m v) (B.execution_stamp hm v)).2.2 u he
    obtain ⟨a, ha, hav⟩ := ht
    have heq := Option.some.inj (ha.symm.trans (B.execution_stamp hm u))
    omega
  · intro t
    apply (card_le_card (t := univ.filter (fun v =>
      (B.run m B.completionRound).stamp v = some t)) ?_).trans (hs.capacity t)
    intro v hv
    have he := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _, by rw [B.execution_stamp hm v, he]⟩

end Scheduling.Batching
