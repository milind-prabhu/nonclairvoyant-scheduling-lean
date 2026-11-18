import Scheduling.RegularBacklog

namespace Scheduling.BatchedForcing

/-- The capacity inequalities for an epoch's ordered passivity times.
The head is the remaining length before the first passivity event; each
following entry is the remaining length at a job's event. -/
inductive PassivityBounds (m c : ℕ) : List ℕ → Prop
  | nil : PassivityBounds m c []
  | cons (d : ℕ) (tail : List ℕ)
      (bound : (m - c) * d ≤ (2 * m - 1) * (c + (tail.map (· + 2)).sum))
      (rest : PassivityBounds m c tail) : PassivityBounds m c (d :: tail)

theorem passivity_step {m c d s : ℕ} (hm : 0 < m) (hc : 2 * c ≤ m)
    (h : (m - c) * d ≤ (2 * m - 1) * (c + s)) :
    d + 2 ≤ 4 * c + 2 + 4 * s := by
  have hp : 0 < m - c := by omega
  have hb : 2 * m - 1 ≤ 4 * (m - c) := by omega
  have hmul := Nat.mul_le_mul_right (c + s) hb
  have hd : d ≤ 4 * (c + s) := by
    have hh : (m - c) * d ≤ (m - c) * (4 * (c + s)) := by nlinarith
    exact Nat.le_of_mul_le_mul_left hh hp
  omega

theorem PassivityBounds.sum_bound {m c : ℕ} (hm : 0 < m) (hc : 2 * c ≤ m)
    {ds : List ℕ} (h : PassivityBounds m c ds) :
    4 * (ds.map (· + 2)).sum + (4 * c + 2) ≤ (4 * c + 2) * 5 ^ ds.length := by
  induction h with
  | nil => simp
  | cons d tail bound rest ih =>
    have hd := passivity_step hm hc bound
    simp only [List.map_cons, List.sum_cons, List.length_cons, pow_succ]
    nlinarith

/-- The geometric estimate used in the batched lower bound. The service
inequalities must still be derived from the adaptive execution. -/
theorem PassivityBounds.epoch_length_bound {m c L : ℕ} (hm : 0 < m) (hc : 2 * c ≤ m)
    {ds : List ℕ} (h : PassivityBounds m c (L :: ds)) (hlen : ds.length ≤ c) :
    L + 2 ≤ (4 * c + 2) * 5 ^ c := by
  cases h with
  | cons d tail bound rest =>
    have hd := passivity_step hm hc bound
    have hs := rest.sum_bound hm hc
    have hp : 5 ^ ds.length ≤ 5 ^ c := Nat.pow_le_pow_right (by omega) hlen
    have hmul := Nat.mul_le_mul_left (4 * c + 2) hp
    omega

theorem no_full_epoch {m c : ℕ} (hm : 0 < m) (hc : 0 < c) (hcm : 2 * c ≤ m)
    {ds : List ℕ} (hlen : ds.length ≤ c) :
    ¬ PassivityBounds m c ((8 * c * 5 ^ c) :: ds) := by
  intro h
  have hb := h.epoch_length_bound hm hcm hlen
  have hp : 0 < 5 ^ c := pow_pos (by omega) c
  nlinarith

end Scheduling.BatchedForcing

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- With one deficit in every epoch, `cmL` jobs suffice for the final
backlog contradiction. This is the counting step of the batched lower
bound, conditional on its epoch-forcing property. -/
theorem regular_every_epoch_flow_lower {m L c : ℕ} {S : Assignment (vertices := vertices)}
    (hm : 0 < m) (hL : 0 < L) (hc : 0 < c) (hn : jobs = c * (m * L))
    (hS : I.Valid m S) (hrelease : ∀ j, I.release j = j.val * L)
    (hwork : ∀ j, (I.jobVertices j).card = m * L)
    (hidle : I.FlowBound S (c * L) → ∀ i < jobs, I.epochWork S L i < m * L) :
    c * L ≤ I.maxFlow S := by
  by_contra hh
  have hflow : I.FlowBound S (c * L) := (I.flowBound_iff_maxFlow_le S _).mpr (by omega)
  have hp : 0 < m * L := Nat.mul_pos hm hL
  have hcj : c ≤ jobs := by
    rw [hn]
    have h := Nat.mul_le_mul_left c (show 1 ≤ m * L from hp)
    simpa only [Nat.mul_one] using h
  have hy := I.regular_young_backlog hcj hL hrelease hwork hflow
  rw [← I.regular_idleBacklog_eq hS hL hwork] at hy
  have hacc : jobs ≤ Accounting.idleBacklog (m * L) (I.epochWork S L) jobs := by
    simpa only [Nat.one_mul] using
      Accounting.forcing_epochs_accumulate (c := 1) (K := jobs) (by omega)
        (by simpa only [Nat.one_mul] using hidle hflow)
  have hc1 : c - 1 + 1 = c := by omega
  nlinarith

end Scheduling.Instance
