import Scheduling.Optimum

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

noncomputable def batchRemaining (S : Assignment (vertices := vertices)) (r t : ℕ) :
    Finset (Fin vertices) := univ.filter (fun v => I.release (I.owner v) = r ∧ t ≤ S v)

/-- Lemma 17: residual work of jobs sharing release r fits into the last
L-z slots of an offline schedule, where z counts prefix-idle slots under FIFO.
This result does not require the other arrivals to be batched. -/
theorem batch_remaining_work_bound {m L r t : ℕ} {S O : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O) (hL : I.FlowBound O L)
    (hrt : r ≤ t) :
    (I.batchRemaining S r t).card ≤ m * (L - (I.partialSlots m S r t).card) := by
  classical
  have h := card_le_slots O m (r + (I.partialSlots m S r t).card) (r + L)
    (I.batchRemaining S r t) hO.capacity (by
      intro v hv
      have hv' := (mem_filter.mp hv).2
      have hp := I.partial_progress hS hF hO (I.owner v) t (by rw [hv'.1]; exact hrt) v rfl hv'.2
      have hb := hL v
      rw [hv'.1] at hp hb
      exact ⟨hp, hb⟩)
  have heq : r + L - (r + (I.partialSlots m S r t).card) =
      L - (I.partialSlots m S r t).card := by omega
  rw [heq] at h
  exact h

theorem batch_prefix_idle_lt {m L r t : ℕ} {S O : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O) (hL : I.FlowBound O L)
    (hrt : r ≤ t) (hu : (I.batchRemaining S r t).Nonempty) :
    (I.partialSlots m S r t).card < L := by
  obtain ⟨v, hv⟩ := hu
  have hv' := (mem_filter.mp hv).2
  have h := I.partial_slots_lt hS hF hO hL (I.owner v) (by rw [hv'.1]; exact hrt) ⟨v, rfl, hv'.2⟩
  simpa [hv'.1] using h

end Scheduling.Instance

namespace Scheduling.Accounting
open Finset

/-- Integer record inequalities force exponential growth of the prefix-idle
counts. Indices run from newest to oldest, reversing the order in Lemma 18. -/
theorem geometric_record_sum (z : ℕ → ℕ) (q : ℕ)
    (hz : ∀ i < q, 1 + ∑ j ∈ range i, z j ≤ z i) :
    2 ^ q ≤ 1 + ∑ i ∈ range q, z i := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hp := ih (by intro i hi; exact hz i (by omega))
    have hq := hz q (by omega)
    rw [sum_range_succ, pow_succ]
    omega

theorem geometric_record_oldest (z : ℕ → ℕ) {q L : ℕ} (hq : 0 < q)
    (hz : ∀ i < q, 1 + ∑ j ∈ range i, z j ≤ z i)
    (hL : z (q - 1) < L) : 2 ^ (q - 1) < L := by
  have hsum := geometric_record_sum z (q - 1) (by intro i hi; exact hz i (by omega))
  have hlast := hz (q - 1) (by omega)
  omega

end Scheduling.Accounting
