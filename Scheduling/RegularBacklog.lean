import Scheduling.Accounting
import Scheduling.Optimum

namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)
attribute [local instance] Classical.propDecidable

theorem interval_card_eq_sum (S : Assignment (vertices := vertices)) (a b : ℕ) :
    (univ.filter (fun v => a ≤ S v ∧ S v < b)).card =
      ∑ t ∈ Ico a b, (univ.filter (fun v => S v = t)).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := S)
    (fun v hv => mem_Ico.mpr (mem_filter.mp hv).2)]
  apply sum_congr rfl
  intro t ht
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact And.right
  · intro he
    exact ⟨by rw [he]; exact mem_Ico.mp ht, he⟩

theorem interval_deficit_has_idle {m a b : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S)
    (hdeficit : (univ.filter (fun v => a ≤ S v ∧ S v < b)).card < m * (b - a)) :
    ∃ t ∈ Ico a b, (univ.filter (fun v => S v = t)).card < m := by
  classical
  by_contra hn
  push Not at hn
  have he : ∀ t ∈ Ico a b, (univ.filter (fun v => S v = t)).card = m := by
    intro t ht; exact (hS.capacity t).antisymm (hn t ht)
  rw [interval_card_eq_sum S a b, sum_congr rfl he] at hdeficit
  simp [Nat.mul_comm] at hdeficit

noncomputable def epochWork (_I : Instance jobs vertices)
    (S : Assignment (vertices := vertices)) (L i : ℕ) : ℕ :=
  (univ.filter (fun v => S v / L = i)).card

theorem epochWork_eq_sum (S : Assignment (vertices := vertices)) {L : ℕ}
    (hL : 0 < L) (i : ℕ) :
    I.epochWork S L i = ∑ t ∈ Ico (i * L) ((i + 1) * L),
      (univ.filter (fun v => S v = t)).card := by
  rw [← interval_card_eq_sum S]
  unfold epochWork
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  have hd := Nat.div_add_mod (S v) L
  have hr := Nat.mod_lt (S v) hL
  generalize S v % L = r at *
  constructor
  · intro he; rw [he] at hd; constructor <;> nlinarith
  · intro h
    have hlo := (Nat.le_div_iff_mul_le hL).mpr h.1
    have hhi := (Nat.div_lt_iff_lt_mul hL).mpr h.2
    omega

theorem epochWork_lt_of_idle {m L i t : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hL : 0 < L) (ht : t ∈ Ico (i * L) ((i + 1) * L))
    (hidle : (univ.filter (fun v => S v = t)).card < m) : I.epochWork S L i < m * L := by
  rw [I.epochWork_eq_sum S hL i]
  have h := sum_lt_sum (s := Ico (i * L) ((i + 1) * L))
    (f := fun t => (univ.filter (fun v => S v = t)).card) (g := fun _ => m)
    (by intro u _; exact hS.capacity u) ⟨t, ht, hidle⟩
  have hlen : (i + 1) * L - i * L = L := by rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
  simp only [sum_const, Nat.card_Ico, hlen] at h
  simpa [Nat.mul_comm] using h

theorem epochWork_le {m L : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hL : 0 < L) (i : ℕ) : I.epochWork S L i ≤ m * L := by
  classical
  have h := card_le_slots S m (i * L) ((i + 1) * L)
    (univ.filter (fun v => S v / L = i)) hS.capacity (by
      intro v hv
      have he := (mem_filter.mp hv).2
      have hd := Nat.div_add_mod (S v) L
      have hr := Nat.mod_lt (S v) hL
      rw [he] at hd
      generalize S v % L = r at *
      constructor <;> nlinarith)
  simpa only [epochWork, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left] using h

theorem regular_vertex_count {W : ℕ}
    (hwork : ∀ j, (I.jobVertices j).card = W) : vertices = jobs * W := by
  classical
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin vertices)))
    (t := (univ : Finset (Fin jobs))) (f := I.owner) (by simp)
  simp only [jobVertices] at hwork
  simpa [hwork] using h

theorem regular_alive_card_le {L c : ℕ} {S : Assignment (vertices := vertices)}
    (hL : 0 < L) (hrelease : ∀ j, I.release j = j.val * L)
    (hflow : I.FlowBound S (c * L)) (i : ℕ) : (I.alive S (i * L)).card ≤ c := by
  classical
  have hc := card_le_card_of_injOn Fin.val (s := I.alive S (i * L))
    (t := Ico (i + 1 - c) (i + 1)) (by
      intro j hj
      obtain ⟨hr, v, ho, ht⟩ := (mem_filter.mp hj).2
      rw [hrelease] at hr
      have hf := hflow v
      rw [ho, hrelease] at hf
      have hji : j.val ≤ i := by
        by_contra hn
        have := Nat.mul_le_mul_right L (show i + 1 ≤ j.val by omega)
        nlinarith
      have hij : i < j.val + c := by
        by_contra hn
        have := Nat.mul_le_mul_right L (show j.val + c ≤ i by omega)
        nlinarith
      exact mem_Ico.mpr ⟨by omega, by omega⟩)
    (by intro u _ v _ huv; exact Fin.ext huv)
  have hcard : (Ico (i + 1 - c) (i + 1)).card ≤ c := by rw [Nat.card_Ico]; omega
  exact hc.trans hcard

theorem regular_epoch_no_arrivals {m L i : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (_hL : 0 < L)
    (hrelease : ∀ j, I.release j = j.val * L)
    (v : Fin vertices) (ht : S v < (i + 1) * L) : I.release (I.owner v) ≤ i * L := by
  have hr := hS.release v
  rw [hrelease] at hr ⊢
  have hj : (I.owner v).val ≤ i := by
    by_contra hn
    have := Nat.mul_le_mul_right L (show i + 1 ≤ (I.owner v).val by omega)
    omega
  exact Nat.mul_le_mul_right L hj

theorem epochWork_sum (S : Assignment (vertices := vertices)) {L : ℕ}
    (hL : 0 < L) (N : ℕ) :
    ∑ i ∈ range N, I.epochWork S L i = (univ.filter (fun v => S v < N * L)).card := by
  classical
  have h := card_eq_sum_card_fiberwise
    (s := univ.filter (fun v : Fin vertices => S v < N * L))
    (t := range N) (f := fun v => S v / L) (by
      intro v hv
      exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hL).mpr (mem_filter.mp hv).2))
  rw [h]
  apply sum_congr rfl
  intro i hi
  unfold epochWork
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro he
    exact ⟨(Nat.div_lt_iff_lt_mul hL).mp (by rw [he]; exact mem_range.mp hi), he⟩
  · exact And.right

/-- The abstract sum of idle capacity is exactly the number of vertices
unfinished after the last arrival epoch. -/
theorem idleBacklog_eq_remaining {m L N : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hL : 0 < L) (hvertices : vertices = N * (m * L)) :
    Accounting.idleBacklog (m * L) (I.epochWork S L) N =
      (univ.filter (fun v => N * L ≤ S v)).card := by
  have hc := Accounting.idleBacklog_conservation (I.epochWork_le hS hL) N
  rw [I.epochWork_sum S hL] at hc
  have hp := card_filter_add_card_filter_not (s := univ)
    (fun v : Fin vertices => S v < N * L)
  simp only [not_lt, card_univ, Fintype.card_fin] at hp
  omega

theorem regular_idleBacklog_eq {m L : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hL : 0 < L)
    (hwork : ∀ j, (I.jobVertices j).card = m * L) :
    Accounting.idleBacklog (m * L) (I.epochWork S L) jobs =
      (univ.filter (fun v => jobs * L ≤ S v)).card := by
  classical
  have hc := Accounting.idleBacklog_conservation (I.epochWork_le hS hL) jobs
  rw [I.epochWork_sum S hL] at hc
  have hp := card_filter_add_card_filter_not (s := univ) (fun v : Fin vertices => S v < jobs * L)
  simp only [not_lt, card_univ, Fintype.card_fin] at hp
  have ht := I.regular_vertex_count hwork
  omega

/-- Under a `cL` flow bound, only the last `c-1` jobs can remain at `jobs*L`.
The count includes all unrevealed vertices of those jobs. -/
theorem regular_young_backlog {m L c : ℕ} {S : Assignment (vertices := vertices)}
    (hc : c ≤ jobs) (_hL : 0 < L)
    (hrelease : ∀ j, I.release j = j.val * L)
    (hwork : ∀ j, (I.jobVertices j).card = m * L)
    (hflow : I.FlowBound S (c * L)) :
    (univ.filter (fun v => jobs * L ≤ S v)).card ≤ (c - 1) * (m * L) := by
  classical
  let R := univ.filter (fun v : Fin vertices => jobs * L ≤ S v)
  have hyoung : ∀ v ∈ R, (I.owner v).val ∈ Ioo (jobs - c) jobs := by
    intro v hv
    have ht := (mem_filter.mp hv).2
    have hf := hflow v
    rw [hrelease] at hf
    have hj := (I.owner v).isLt
    have ho : jobs < (I.owner v).val + c := by
      by_contra hn
      have := Nat.mul_le_mul_right L (show (I.owner v).val + c ≤ jobs by omega)
      nlinarith
    exact mem_Ioo.mpr ⟨by omega, hj⟩
  have he := card_eq_sum_card_fiberwise (s := R) (f := fun v => (I.owner v).val) hyoung
  rw [show (univ.filter (fun v => jobs * L ≤ S v)).card = R.card from rfl, he]
  calc
    _ ≤ ∑ _j ∈ Ioo (jobs - c) jobs, m * L := by
      apply sum_le_sum
      intro j hj
      have hjn := (mem_Ioo.mp hj).2
      have hsub : R.filter (fun v => (I.owner v).val = j) ⊆ I.jobVertices ⟨j, hjn⟩ := by
        intro v hv
        simp only [jobVertices, mem_filter, mem_univ, true_and]
        exact Fin.ext (mem_filter.mp hv).2
      exact (card_le_card hsub).trans (hwork ⟨j, hjn⟩).le
    _ ≤ (c - 1) * (m * L) := by
      have hcard : (Ioo (jobs - c) jobs).card ≤ c - 1 := by
        rw [Nat.card_Ioo]
        omega
      simpa using Nat.mul_le_mul_right (m * L) hcard

/-- The deterministic lower-bound contradiction for a concrete schedule.
Only the adversary's idle-slot property remains as a hypothesis. -/
theorem regular_forcing_flow_lower {m L c : ℕ} {S : Assignment (vertices := vertices)}
    (hm : 0 < m) (hL : 0 < L) (hc : 0 < c)
    (hn : jobs = c * (c * (m * L)))
    (hS : I.Valid m S)
    (hrelease : ∀ j, I.release j = j.val * L)
    (hwork : ∀ j, (I.jobVertices j).card = m * L)
    (hidle : ∀ k < c * (m * L), I.epochWork S L (c * k) < m * L) :
    c * L ≤ I.maxFlow S := by
  by_contra h
  have hflow : I.FlowBound S (c * L) :=
    (I.flowBound_iff_maxFlow_le S _).mpr (by omega)
  have hcap : 0 < m * L := Nat.mul_pos hm hL
  have hcj : c ≤ jobs := by
    rw [hn]
    have hp : 0 < c * (m * L) := Nat.mul_pos hc hcap
    simpa using Nat.mul_le_mul_left c (show 1 ≤ c * (m * L) by omega)
  have hy := I.regular_young_backlog hcj hL hrelease hwork hflow
  rw [← I.regular_idleBacklog_eq hS hL hwork] at hy
  conv at hy => lhs; arg 3; rw [hn]
  exact Accounting.forcing_backlog_contradiction hc hcap hidle hy

end Scheduling.Instance
