import Scheduling.Counting

namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

theorem remaining_le_alive_work {m L : ℕ}
    {O S : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) (t : ℕ) :
    (I.remaining S t).card ≤ (I.alive S t).card * (m * L) := by
  classical
  have heq : (I.remaining S t).card =
      ∑ j ∈ I.alive S t, ((I.remaining S t).filter (fun v => I.owner v = j)).card :=
    card_eq_sum_card_fiberwise (by
      intro v hv
      have h := (mem_filter.mp hv).2
      exact mem_filter.mpr ⟨mem_univ _, h.1, v, rfl, h.2⟩)
  rw [heq]
  calc
    _ ≤ ∑ _j ∈ I.alive S t, m * L := by
      apply sum_le_sum
      intro j _
      apply (card_le_card (t := I.jobVertices j) ?_).trans (I.job_work_bound hO hL j)
      intro v hv
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩
    _ = _ := by simp

theorem full_of_many_alive {m : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) {t : ℕ}
    (ha : m ≤ (I.alive S t).card) :
    (univ.filter (fun v => S v = t)).card = m := by
  classical
  by_contra hne
  have hlt : (univ.filter (fun v => S v = t)).card < m :=
    lt_of_le_of_ne (hS.capacity t) hne
  have hsub : I.alive S t ⊆ (univ.filter (fun v => S v = t)).image I.owner := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    obtain ⟨v, hv, hr⟩ := I.exists_ready hj'.1 hj'.2
    have he : S v = t := by
      by_contra he
      exact hne (hF.work_conserving t v hr he)
    exact mem_image.mpr ⟨v, by simp [he], hv⟩
  have hc := (card_le_card hsub).trans (card_image_le)
  omega

noncomputable def executedDuring (_I : Instance jobs vertices) (S : Assignment (vertices := vertices)) (a b : ℕ) :
    Finset (Fin vertices) := univ.filter (fun v => a ≤ S v ∧ S v < b)

theorem executedDuring_card {S : Assignment (vertices := vertices)} {m a b : ℕ}
    (full : ∀ t, a ≤ t → t < b → (univ.filter (fun v => S v = t)).card = m) :
    (I.executedDuring S a b).card = m * (b - a) := by
  classical
  have heq : (I.executedDuring S a b).card =
      ∑ t ∈ Ico a b, ((I.executedDuring S a b).filter (fun v => S v = t)).card :=
    card_eq_sum_card_fiberwise (by intro v hv; exact mem_Ico.mpr (mem_filter.mp hv).2)
  rw [heq]
  calc
    _ = ∑ t ∈ Ico a b, m := by
      apply sum_congr rfl
      intro t ht
      have ht' := mem_Ico.mp ht
      have he : (I.executedDuring S a b).filter (fun v => S v = t) =
          univ.filter (fun v => S v = t) := by
        ext v
        simp only [executedDuring, mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨by omega, h⟩
      rw [he, full t ht'.1 ht'.2]
    _ = _ := by simp [Nat.mul_comm]

/-- Conservation of work between the last sparse state and the present.
The old state includes slot `s-1`; ignoring service in that slot only weakens
the inequality. -/
theorem backlog_accounting {m s t : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hst : s ≤ t) :
    (I.remaining S t).card + (I.executedDuring S s t).card ≤
      (if s = 0 then 0 else (I.remaining S (s - 1)).card) +
      (univ.filter (fun v => s ≤ I.release (I.owner v) ∧ I.release (I.owner v) ≤ t)).card := by
  classical
  let old : Finset (Fin vertices) := if s = 0 then ∅ else I.remaining S (s - 1)
  let new := univ.filter (fun v => s ≤ I.release (I.owner v) ∧ I.release (I.owner v) ≤ t)
  have hd : Disjoint (I.remaining S t) (I.executedDuring S s t) := by
    apply disjoint_left.mpr
    intro v hv hw
    have hv' := (mem_filter.mp hv).2
    have hw' := (mem_filter.mp hw).2
    omega
  have hsub : I.remaining S t ∪ I.executedDuring S s t ⊆ old ∪ new := by
    intro v hv
    have hr : I.release (I.owner v) ≤ t := by
      rcases mem_union.mp hv with h | h
      · exact (mem_filter.mp h).2.1
      · have := (mem_filter.mp h).2; have := hS.release v; omega
    have hs : s ≤ S v := by
      rcases mem_union.mp hv with h | h
      · have := (mem_filter.mp h).2; omega
      · exact (mem_filter.mp h).2.1
    by_cases hnew : s ≤ I.release (I.owner v)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hnew, hr⟩)
    · apply mem_union_left
      have hs0 : s ≠ 0 := by omega
      simp only [old, hs0, ↓reduceIte]
      exact mem_filter.mpr ⟨mem_univ _, by omega, by omega⟩
  have hc := (card_le_card hsub).trans (card_union_le old new)
  rw [card_union_of_disjoint hd] at hc
  by_cases hs : s = 0 <;> simpa [old, new, hs] using hc

/-- Lemma 9. This theorem derives the backlog bound from concrete finite
schedule constraints, not from a backlog-bound hypothesis. -/
theorem fifo_backlog_bound {m L : ℕ} {S O : Assignment (vertices := vertices)}
    (hm : 0 < m) (hS : I.Valid m S) (hF : I.IsFIFO m S)
    (hO : I.Valid m O) (hL : I.FlowBound O L) (t : ℕ) :
    (I.remaining S t).card ≤ m * m * L := by
  classical
  have sparse : ∀ u, (I.alive S u).card < m →
      (I.remaining S u).card ≤ (m - 1) * m * L := by
    intro u hu
    have h := I.remaining_le_alive_work hO hL (S := S) u
    have hc : (I.alive S u).card ≤ m - 1 := by omega
    exact h.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (m * L) hc)
  by_cases ht : (I.alive S t).card < m
  · exact (sparse t ht).trans (by exact Nat.mul_le_mul_right L (Nat.mul_le_mul_right m (Nat.sub_le m 1)))
  · let P := fun s => s ≤ t ∧ ∀ u, s ≤ u → u ≤ t → m ≤ (I.alive S u).card
    have hex : ∃ s, P s := by
      refine ⟨t, le_rfl, ?_⟩
      intro u hu hut
      have he : u = t := by omega
      rw [he]
      omega
    let s := Nat.find hex
    have hs := Nat.find_spec hex
    have hst : s ≤ t := hs.1
    have hold : (if s = 0 then 0 else (I.remaining S (s - 1)).card) ≤
        (m - 1) * m * L := by
      split_ifs with hzero
      · exact Nat.zero_le _
      · apply sparse
        by_contra hn
        have hp : P (s - 1) := by
          refine ⟨by omega, ?_⟩
          intro u hu hut
          by_cases he : u = s - 1
          · subst u; omega
          · exact hs.2 u (by omega) hut
        have hmin := Nat.find_min' hex hp
        change s ≤ s - 1 at hmin
        omega
    have hfull : (I.executedDuring S s t).card = m * (t - s) :=
      I.executedDuring_card (fun u hu hut => I.full_of_many_alive hS hF (hs.2 u hu (by omega)))
    have hacc := I.backlog_accounting hS hst
    have harr := I.arrival_work_bound (a := s) (b := t) hO hL
    rw [hfull] at hacc
    have htL : t + L - s = t - s + L := by omega
    rw [htL] at harr
    have hm1 : m - 1 + 1 = m := by omega
    nlinarith

end Scheduling.Instance
