import Scheduling.Combined
import Scheduling.SFFNonclairvoyant

namespace Scheduling
open Finset

/-- Failure detection uses only the release times of currently ready
vertices. Every unfinished arrived DAG has a ready vertex, so hidden work
need not be counted or inspected. -/
def deadlineVisible (B t : ℕ) (Q : FIFOObservation) : Bool :=
  decide (∃ x ∈ Q, (ofLex x).1 + 88 * B ^ 2 ≤ t)

theorem deadlineVisible_iff (B t : ℕ) (Q : FIFOObservation) :
    deadlineVisible B t Q = true ↔ ∃ x ∈ Q, (ofLex x).1 + 88 * B ^ 2 ≤ t := by
  simp [deadlineVisible]

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Splicing a future continuation preserves all completed work at every
earlier time, including the restart boundary before that slot executes. -/
theorem splice_prefix_time {S : Assignment (vertices := vertices)} {s t : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) (ht : t ≤ s) (v : Fin vertices) :
    I.splice S s T v < t ↔ S v < t := by
  classical
  by_cases hv : S v < s
  · rw [I.splice_preserves_prefix T hv]
  · have hs : v ∈ I.survivors S s := mem_filter.mpr ⟨mem_univ _, by omega⟩
    simp only [splice, dif_pos hs]
    omega

/-- The recursive controller never revises the executed prefix, without
requiring any offline bound or performance invariant. -/
theorem combinedAux_prefix_time {m : ℕ} (hm : 0 < m)
    (fuel B : ℕ) (hB : 0 < B) (S : Assignment (vertices := vertices)) (s t : ℕ)
    (ht : t ≤ s) (v : Fin vertices) :
    I.combinedAux m hm fuel B hB S s v < t ↔ S v < t := by
  classical
  induction fuel generalizing B S s with
  | zero => exact I.splice_prefix_time _ ht v
  | succ fuel ih =>
    by_cases hswitch : B < m
    · simp only [combinedAux, if_pos hswitch]
      by_cases hf : I.PhaseFails (I.sffPhase m B hB S s) s B
      · rw [dif_pos hf]
        have hs := (I.failureTime_spec hf).1
        exact (ih (2 * B) (by omega) (I.sffPhase m B hB S s)
          (I.failureTime hf) (ht.trans hs)).trans (I.splice_prefix_time _ ht v)
      · rw [dif_neg hf]
        exact I.splice_prefix_time _ ht v
    · simp only [combinedAux, if_neg hswitch]
      exact I.splice_prefix_time _ ht v

variable [DecidableRel I.edge]

theorem readyObservation_prefix {S T : Assignment (vertices := vertices)} {t : ℕ}
    (h : ∀ v, S v < t ↔ T v < t) : I.readyObservation S t = I.readyObservation T t := by
  unfold readyObservation
  congr 1
  ext v
  have hv : t ≤ S v ↔ t ≤ T v := by have := h v; omega
  simp only [mem_filter, mem_univ, true_and, hv, h]

theorem splice_readyObservation {S : Assignment (vertices := vertices)} {s t : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) (ht : t ≤ s) :
    I.readyObservation (I.splice S s T) t = I.readyObservation S t :=
  I.readyObservation_prefix (I.splice_prefix_time T ht)

theorem combinedAux_readyObservation {m : ℕ} (hm : 0 < m)
    (fuel B : ℕ) (hB : 0 < B) (S : Assignment (vertices := vertices)) (s t : ℕ)
    (ht : t ≤ s) :
    I.readyObservation (I.combinedAux m hm fuel B hB S s) t = I.readyObservation S t :=
  I.readyObservation_prefix (I.combinedAux_prefix_time hm fuel B hB S s t ht)

/-- The first failed deadline is visible from the exposed ready frontier. -/
theorem failureTime_visible {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : I.PhaseFails S s B) :
    deadlineVisible B (I.failureTime hf) (I.readyObservation S (I.failureTime hf)) = true := by
  obtain ⟨_, v, he, hv⟩ := I.failureTime_spec hf
  have hr : I.release (I.owner v) ≤ I.failureTime hf := by omega
  obtain ⟨w, hw, hready⟩ := I.exists_ready (S := S) hr ⟨v, rfl, hv⟩
  apply (deadlineVisible_iff _ _ _).mpr
  refine ⟨I.fifoPriority w, (I.mem_readyObservation _ _ _).mpr ⟨w, hready, rfl⟩, ?_⟩
  change I.release (I.owner w) + 88 * B ^ 2 ≤ I.failureTime hf
  rw [hw]
  omega

/-- No earlier time in a phase can trigger the public failure detector. -/
theorem before_failure_not_visible {S : Assignment (vertices := vertices)} {s B t : ℕ}
    (hf : I.PhaseFails S s B)
    (hs : ∀ v, s ≤ S v → s ≤ I.release (I.owner v) + 88 * B ^ 2)
    (hst : s ≤ t) (ht : t < I.failureTime hf) :
    deadlineVisible B t (I.readyObservation S t) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨x, hx, hd⟩ := (deadlineVisible_iff _ _ _).mp h
  obtain ⟨v, hv, rfl⟩ := (I.mem_readyObservation _ _ _).mp hx
  change I.release (I.owner v) + 88 * B ^ 2 ≤ t at hd
  have hstart := hs v (hst.trans hv.2.1)
  have hmin := I.failureTime_le hf v hstart (hd.trans hv.2.1)
  omega

theorem no_failure_not_visible {S : Assignment (vertices := vertices)} {s B t : ℕ}
    (hf : ¬ I.PhaseFails S s B)
    (hs : ∀ v, s ≤ S v → s ≤ I.release (I.owner v) + 88 * B ^ 2)
    (hst : s ≤ t) : deadlineVisible B t (I.readyObservation S t) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨x, hx, hd⟩ := (deadlineVisible_iff _ _ _).mp h
  obtain ⟨v, hv, rfl⟩ := (I.mem_readyObservation _ _ _).mp hx
  change I.release (I.owner v) + 88 * B ^ 2 ≤ t at hd
  exact hf ⟨_, hs v (hst.trans hv.2.1), v, rfl, hd.trans hv.2.1⟩

end Instance
end Scheduling
