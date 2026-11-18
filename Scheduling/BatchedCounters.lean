import Scheduling.BatchedWideWork
import Scheduling.BatchedCredit

namespace Scheduling.BatchedAdversary
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ}

theorem wideRecorded_append (m : ℕ) (history : List (LayerRecord jobs work))
    (r : LayerRecord jobs work) (j : Fin jobs) (v : Fin (jobs * work)) :
    WideRecorded m (history ++ [r]) j v ↔ WideRecorded m history j v ∨
      (job v = j ∧ r.owner = j ∧ r.stop - r.start = 2 * m - 1 ∧
        r.start ≤ (position v).val ∧ (position v).val < r.stop) := by
  unfold WideRecorded
  constructor
  · rintro ⟨ho, s, hs, hrest⟩
    rcases List.mem_append.mp hs with hs | hs
    · exact Or.inl ⟨ho, s, hs, hrest⟩
    · have he : s = r := List.mem_singleton.mp hs
      subst s
      exact Or.inr ⟨ho, hrest⟩
  · rintro (⟨ho, s, hs, hrest⟩ | ⟨ho, hrest⟩)
    · exact ⟨ho, s, List.mem_append_left _ hs, hrest⟩
    · exact ⟨ho, r, List.mem_append_right _ (List.mem_singleton_self r), hrest⟩

theorem wideCount_append (m : ℕ) (history : List (LayerRecord jobs work))
    (r : LayerRecord jobs work) (j : Fin jobs) :
    wideCount m (history ++ [r]) j = wideCount m history j +
      if r.owner = j ∧ r.stop - r.start = 2 * m - 1 then 1 else 0 := by
  by_cases ho : r.owner = j <;> by_cases hw : r.stop - r.start = 2 * m - 1 <;>
    simp [wideCount, List.filter_append, ho, hw]

theorem narrowCount_append (history : List (LayerRecord jobs work))
    (r : LayerRecord jobs work) (j : Fin jobs) :
    narrowCount (history ++ [r]) j = narrowCount history j +
      if r.owner = j ∧ r.stop - r.start = 1 then 1 else 0 := by
  by_cases ho : r.owner = j <;> by_cases hw : r.stop - r.start = 1 <;>
    simp [narrowCount, List.filter_append, ho, hw]

theorem owner_interval_card_le (j : Fin jobs) (a b : ℕ) :
    (univ.filter (fun v : Fin (jobs * work) => job v = j ∧ a ≤ (position v).val ∧
      (position v).val < b)).card ≤ b - a := by
  have hc := card_le_card_of_injOn (fun v : Fin (jobs * work) => (position v).val)
    (s := univ.filter (fun v => job v = j ∧ a ≤ (position v).val ∧ (position v).val < b))
    (t := Ico a b) (by intro v hv; exact mem_Ico.mpr (mem_filter.mp hv).2.2) (by
      intro u hu v hv he
      exact LayeredForest.coordinates_injective (Prod.ext
        ((mem_filter.mp hu).2.1.trans (mem_filter.mp hv).2.1.symm) he))
  simpa only [Nat.card_Ico] using hc

theorem epochWideWork_append_le (m L : ℕ) (history : List (LayerRecord jobs work))
    (r : LayerRecord jobs work) (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (t : ℕ) :
    epochWideWork m L (history ++ [r]) j S t ≤ epochWideWork m L history j S t + (r.stop - r.start) := by
  let old := univ.filter (fun v => WideRecorded m history j v ∧ (t / L) * L ≤ S v ∧ S v < t)
  let layer := univ.filter (fun v : Fin (jobs * work) => job v = j ∧
    r.start ≤ (position v).val ∧ (position v).val < r.stop)
  have hs : univ.filter (fun v => WideRecorded m (history ++ [r]) j v ∧
      (t / L) * L ≤ S v ∧ S v < t) ⊆ old ∪ layer := by
    intro v hv
    obtain ⟨hw, ht⟩ := (mem_filter.mp hv).2
    rcases (wideRecorded_append m history r j v).mp hw with hw | hw
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hw, ht⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hw.1, hw.2.2.2⟩)
  have hc := (card_le_card hs).trans (card_union_le old layer)
  exact hc.trans (Nat.add_le_add_left (owner_interval_card_le j r.start r.stop) old.card)

theorem epochWideWork_append_unchanged (m L : ℕ) (history : List (LayerRecord jobs work))
    (r : LayerRecord jobs work) (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (t : ℕ)
    (hr : r.owner ≠ j ∨ r.stop - r.start ≠ 2 * m - 1) :
    epochWideWork m L (history ++ [r]) j S t = epochWideWork m L history j S t := by
  unfold epochWideWork
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, wideRecorded_append]
  constructor
  · rintro ⟨hw | hw, ht⟩
    · exact ⟨hw, ht⟩
    · rcases hr with howner | hwidth
      · exact False.elim (howner hw.2.1)
      · exact False.elim (hwidth hw.2.2.1)
  · rintro ⟨hw, ht⟩; exact ⟨Or.inl hw, ht⟩

theorem epochWideWork_time_closed (m L : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) {t u : ℕ}
    (htu : t ≤ u) (hepoch : t / L = u / L)
    (hclosed : ∀ v, WideRecorded m history j v → S v < t) :
    epochWideWork m L history j S u = epochWideWork m L history j S t := by
  unfold epochWideWork
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, hepoch]
  constructor
  · rintro ⟨hw, hlo, _⟩; exact ⟨hw, hlo, hclosed v hw⟩
  · rintro ⟨hw, hlo, hhi⟩; exact ⟨hw, hlo, hhi.trans_le htu⟩

theorem epochWideWork_zero_closed (m L : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (t : ℕ)
    (hclosed : ∀ v, WideRecorded m history j v → S v < (t / L) * L) :
    epochWideWork m L history j S t = 0 := by
  unfold epochWideWork
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hh := (mem_filter.mp hv).2
  have ht := hclosed v hh.1
  omega

theorem epoch_start_after {L t u : ℕ} (hL : 0 < L) (htu : t ≤ u) (hne : t / L ≠ u / L) :
    t ≤ (u / L) * L := by
  have hdiv : t / L ≤ u / L := Nat.div_le_div_right htu
  have hlt : t / L < u / L := by omega
  exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hL).mp hlt)

theorem remaining_epoch_strict {L t u : ℕ} (hL : 0 < L) (htu : t < u)
    (hepoch : t / L = u / L) :
    L - u % L < L - t % L := by
  have ht := Nat.div_add_mod t L
  have hu := Nat.div_add_mod u L
  rw [hepoch] at ht
  have hmt := Nat.mod_lt t hL
  have hmu := Nat.mod_lt u hL
  omega

/-- Completing a layer preserves threshold credit for the actual service
counter. When the completion enters a new epoch, all older completed
layers disappear from that counter. -/
theorem credit_after_record (hm : 2 ≤ m) (hL : 0 < L)
    (history : List (LayerRecord jobs work)) (r : LayerRecord jobs work)
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (e u : ℕ)
    (ho : r.owner = j) (heu : e < u)
    (hshape : r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1)
    (hbalance : narrowCount history j ≤ wideCount m history j)
    (hclosed : ∀ v, WideRecorded m history j v → S v < e)
    (hcredit : e / L = u / L → BatchedForcing.ThresholdCredit (2 * m - 1) (L - e % L)
      (wideCount m history j) (narrowCount history j) (epochWideWork m L history j S e))
    (hwide : e / L = u / L → r.stop - r.start = 2 * m - 1 →
      wideCount m history j ≤ narrowCount history j ∨
        epochWideWork m L history j S e < (2 * m - 1) * (L - e % L))
    (hnarrow : e / L = u / L → r.stop - r.start = 1 →
      (2 * m - 1) * (L - e % L) ≤ epochWideWork m L history j S e) :
    BatchedForcing.ThresholdCredit (2 * m - 1) (L - u % L)
      (wideCount m (history ++ [r]) j) (narrowCount (history ++ [r]) j)
      (epochWideWork m L (history ++ [r]) j S u) := by
  have hb : 0 < 2 * m - 1 := by omega
  have hbne : 2 * m - 1 ≠ 1 := by omega
  have hd : 0 < L - e % L := by have := Nat.mod_lt e hL; omega
  rcases hshape with hw | hn
  · simp only [wideCount_append, narrowCount_append, ho, hw, hbne,
      and_self, if_true, and_false, if_false, Nat.add_zero]
    have hwork := epochWideWork_append_le m L history r j S u
    rw [hw] at hwork
    by_cases hepoch : e / L = u / L
    · rw [epochWideWork_time_closed m L history j S heu.le hepoch hclosed] at hwork
      exact (hcredit hepoch).wide_step hb hd hbalance (hwide hepoch hw) hwork
    · have hs := epoch_start_after hL heu.le hepoch
      have hz := epochWideWork_zero_closed m L history j S u
        (fun v hv => (hclosed v hv).trans_le hs)
      rw [hz, Nat.zero_add] at hwork
      exact BatchedForcing.ThresholdCredit.first_wide hbalance hwork
  · have hw : r.stop - r.start ≠ 2 * m - 1 := by omega
    simp only [wideCount_append, narrowCount_append, ho, hn, Ne.symm hbne,
      and_self, if_true, and_false, if_false, Nat.add_zero]
    rw [epochWideWork_append_unchanged m L history r j S u (Or.inr hw)]
    by_cases hepoch : e / L = u / L
    · rw [epochWideWork_time_closed m L history j S heu.le hepoch hclosed]
      exact (hcredit hepoch).narrow_step hb hbalance (hnarrow hepoch hn)
        (remaining_epoch_strict hL heu hepoch)
    · have hs := epoch_start_after hL heu.le hepoch
      rw [epochWideWork_zero_closed m L history j S u
        (fun v hv => (hclosed v hv).trans_le hs)]
      exact BatchedForcing.ThresholdCredit.first_narrow

end Scheduling.BatchedAdversary
