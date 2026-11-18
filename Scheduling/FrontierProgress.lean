import Scheduling.FIFO

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- A batch can contain several jobs. It must contain every predecessor of
each vertex it contains. This is true of a union of complete job DAGs. -/
def PredecessorClosed (B : Finset (Fin vertices)) : Prop :=
  ∀ {u v}, v ∈ B → I.edge u v → u ∈ B

noncomputable def markedRounds (mark : ℕ → Prop) (K : ℕ) : Finset ℕ :=
  (range K).filter mark

theorem markedRounds_succ (mark : ℕ → Prop) (K : ℕ) :
    (markedRounds mark (K + 1)).card = (markedRounds mark K).card +
      (if mark K then 1 else 0) := by
  classical
  by_cases h : mark K <;> simp [markedRounds, range_add_one, filter_insert, h]

/-- Frontier processing in rounds. On every marked round, all vertices ready
at its start are processed before its end. Any other work is unrestricted.
This is the structural progress lemma used by SFF, for the concrete DAG model. -/
theorem frontier_round_progress {m : ℕ} {S O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (B : Finset (Fin vertices)) (hB : I.PredecessorClosed B)
    (boundary : ℕ → ℕ) (mono : Monotone boundary) (mark : ℕ → Prop)
    (released : ∀ k, mark k → ∀ v ∈ B, I.release (I.owner v) ≤ boundary k)
    (advance : ∀ k, mark k → ∀ v ∈ B, I.Ready S (boundary k) v → S v < boundary (k + 1))
    (K : ℕ) (v : Fin vertices) (hv : v ∈ B) (hu : boundary K ≤ S v) :
    I.release (I.owner v) + (markedRounds mark K).card ≤ O v := by
  classical
  induction K generalizing v with
  | zero => simpa [markedRounds] using hO.release v
  | succ K ih =>
    have hb : boundary K ≤ boundary (K + 1) := mono (by omega)
    have hprev := ih v hv (by omega)
    have hc := markedRounds_succ mark K
    by_cases hm : mark K
    · rw [if_pos hm] at hc
      have hn : ¬ I.Ready S (boundary K) v := by
        intro hr
        have := advance K hm v hv hr
        omega
      have he : ∃ u, I.edge u v ∧ boundary K ≤ S u := by
        by_contra hn'
        push Not at hn'
        apply hn
        refine ⟨released K hm v hv, by omega, ?_⟩
        intro u he
        have := hn' u he
        omega
      obtain ⟨u, he, hu⟩ := he
      have hp := ih u (hB hv he) hu
      have ho := I.same_job he
      rw [ho] at hp
      have := hO.precedence he
      omega
    · rw [if_neg hm] at hc
      omega

/-- SFF's first progress observation: a batch can be small at the start of
at most L rounds. The premises describe frontier processing, not a depth or
round-count bound. Instantiating the complete SFF trace is separate work. -/
theorem frontier_round_count_bound {m L : ℕ} {S O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L)
    (B : Finset (Fin vertices)) (hB : I.PredecessorClosed B)
    (boundary : ℕ → ℕ) (mono : Monotone boundary) (mark : ℕ → Prop)
    (released : ∀ k, mark k → ∀ v ∈ B, I.release (I.owner v) ≤ boundary k)
    (advance : ∀ k, mark k → ∀ v ∈ B, I.Ready S (boundary k) v → S v < boundary (k + 1))
    (active : ∀ k, mark k → ∃ v ∈ B, boundary k ≤ S v)
    (K : ℕ) : (markedRounds mark K).card ≤ L := by
  classical
  induction K with
  | zero => simp [markedRounds]
  | succ K ih =>
    rw [markedRounds_succ]
    by_cases hm : mark K
    · rw [if_pos hm]
      obtain ⟨v, hv, hu⟩ := active K hm
      have hp := I.frontier_round_progress hO B hB boundary mono mark released advance K v hv hu
      have hl := hL v
      omega
    · rw [if_neg hm]
      omega

end Scheduling.Instance
