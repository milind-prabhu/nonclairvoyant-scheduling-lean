import Scheduling.SFFWork
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Scheduling.SFFRounds
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches m L : ℕ} {I : Instance jobs vertices}
variable {B : Batching I L batches} {S O : Assignment (vertices := vertices)}
variable (R : SFFRounds B m S)

noncomputable def smallFront (k : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => B.vertexBatch v ∈ B.small m S (R.boundary k) ∧ I.Ready S (R.boundary k) v)

noncomputable def youngFront (a k : ℕ) : Finset (Fin vertices) :=
  (R.smallFront k).filter (fun v => a < B.eligible (B.vertexBatch v))

noncomputable def oldService (a k : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => B.eligible (B.vertexBatch v) ≤ a ∧
    R.boundary k ≤ S v ∧ S v < R.boundary (k + 1))

theorem capacity_le_front_plus_one (k : ℕ) :
    m * (R.boundary (k + 1) - R.boundary k) ≤ (R.smallFront k).card + m := by
  have hmul := Nat.div_mul_le_self ((R.smallFront k).card + m - 1) m
  rw [R.length_eq k]
  change m * max 1 (((R.smallFront k).card + m - 1) / m) ≤ _
  by_cases hq : 1 ≤ ((R.smallFront k).card + m - 1) / m
  · rw [max_eq_right hq]
    calc
      _ = ((R.smallFront k).card + m - 1) / m * m := Nat.mul_comm _ _
      _ ≤ (R.smallFront k).card + m - 1 := hmul
      _ ≤ (R.smallFront k).card + m := Nat.sub_le _ _
  · have hq' : ((R.smallFront k).card + m - 1) / m ≤ 1 := by omega
    rw [max_eq_left hq']
    omega

theorem small_front_partition (a k : ℕ) :
    (R.smallFront k).card ≤ (R.oldService a k).card + (R.youngFront a k).card := by
  classical
  have hsub : R.smallFront k ⊆ R.oldService a k ∪ R.youngFront a k := by
    intro v hv
    have hv' := (mem_filter.mp hv).2
    by_cases he : a < B.eligible (B.vertexBatch v)
    · exact mem_union_right _ (mem_filter.mpr ⟨hv, he⟩)
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_univ _, by omega, hv'.2.2.1,
        R.clear_small k (B.vertexBatch v) hv'.1 v rfl hv'.2⟩
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- The only per-round exceptional capacity is one slot when the target batch
is small. When it is large, the oldest filler belongs to the old prefix. -/
theorem round_interference (_hm : 0 < m) {b : Fin batches} {a k : ℕ}
    (hba : B.eligible b ≤ a) (hb : B.Active S (R.boundary k) b) :
    m * (R.boundary (k + 1) - R.boundary k) ≤
      (R.oldService a k).card + (R.youngFront a k).card +
        (if b ∈ B.small m S (R.boundary k) then m else 0) := by
  classical
  by_cases hs : b ∈ B.small m S (R.boundary k)
  · rw [if_pos hs]
    have hc := R.capacity_le_front_plus_one k
    have hp := R.small_front_partition a k
    omega
  · rw [if_neg hs]
    have hl : b ∈ B.large m S (R.boundary k) := (B.active_small_or_large hb).resolve_left hs
    have hf : (I.executedDuring S (R.boundary k) (R.boundary (k + 1))).card =
        m * (R.boundary (k + 1) - R.boundary k) :=
      I.executedDuring_card (fun t ht ht' => R.fill_last k ⟨b, hl⟩ t ht ht')
    have hsub : I.executedDuring S (R.boundary k) (R.boundary (k + 1)) ⊆
        R.oldService a k ∪ R.youngFront a k := by
      intro v hv
      have htime := (mem_filter.mp hv).2
      by_cases he : B.eligible (B.vertexBatch v) ≤ a
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, he, htime⟩)
      · apply mem_union_right
        have hscope := R.service_scope k v htime.1 htime.2
        rcases hscope with hsmall | hfill
        · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hsmall⟩, by omega⟩
        · have ho := R.filler_oldest k (B.vertexBatch v) b hfill hl
          omega
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    rw [hf] at hc
    omega

/-- Old service charges are to distinct vertices in disjoint round intervals. -/
theorem old_service_sum_bound {A K : ℕ} (_hAK : A ≤ K) :
    (∑ k ∈ Ico A K, (R.oldService (R.boundary A) k).card) ≤
      (B.admittedRemaining S (R.boundary A)).card := by
  classical
  have hd : (↑(Ico A K) : Set ℕ).PairwiseDisjoint (R.oldService (R.boundary A)) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro v hvi hvj
    have hvi' := (mem_filter.mp hvi).2
    have hvj' := (mem_filter.mp hvj).2
    rcases lt_or_gt_of_ne hij with h | h
    · have ht := R.strict.monotone (show i + 1 ≤ j by omega)
      omega
    · have ht := R.strict.monotone (show j + 1 ≤ i by omega)
      omega
  rw [← card_biUnion hd]
  apply card_le_card
  intro v hv
  obtain ⟨k, hk, hv⟩ := mem_biUnion.mp hv
  have hv' := (mem_filter.mp hv).2
  have ht := R.strict.monotone (mem_Ico.mp hk).1
  exact mem_filter.mpr ⟨mem_univ _, hv'.1, by omega⟩

/-- Telescoping the round lengths does not lose time to natural subtraction. -/
theorem lengths_sum {A K : ℕ} (hAK : A ≤ K) :
    (∑ k ∈ Ico A K, (R.boundary (k + 1) - R.boundary k)) = R.boundary K - R.boundary A := by
  induction K, hAK using Nat.le_induction with
  | base => simp
  | succ K hAK ih =>
    have he : Ico A (K + 1) = insert K (Ico A K) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    rw [he, sum_insert (by simp), ih]
    have h₁ := R.strict.monotone hAK
    have h₂ := R.strict.monotone (show K ≤ K + 1 by omega)
    omega

/-- The small frontiers of all younger batches cost at most mL per batch
over the whole interval, not m times the interval's length per batch. -/
theorem young_front_sum_bound (hO : I.Valid m O) (hL : I.FlowBound O L)
    {A K : ℕ} (_hAK : A ≤ K) :
    (∑ k ∈ Ico A K, (R.youngFront (R.boundary A) k).card) ≤
      (univ.filter (fun b => R.boundary A < B.eligible b ∧ B.eligible b ≤ R.boundary K)).card * (L * m) := by
  classical
  let N := univ.filter (fun b => R.boundary A < B.eligible b ∧ B.eligible b ≤ R.boundary K)
  have hper : ∀ k ∈ Ico A K, (R.youngFront (R.boundary A) k).card ≤
      ∑ b ∈ N, if b ∈ B.small m S (R.boundary k) then m else 0 := by
    intro k hk
    have heq : (R.youngFront (R.boundary A) k).card =
        ∑ b ∈ N, ((R.youngFront (R.boundary A) k).filter (fun v => B.vertexBatch v = b)).card :=
      card_eq_sum_card_fiberwise (by
        intro v hv
        have hv' := mem_filter.mp hv
        have hsmall := (mem_filter.mp hv'.1).2.1
        have helig := (mem_filter.mp hsmall).2.1.1
        exact mem_filter.mpr ⟨mem_univ _, hv'.2, helig.trans (R.strict.monotone (by have := (mem_Ico.mp hk).2; omega))⟩)
    rw [heq]
    apply sum_le_sum
    intro b hb
    by_cases hsmall : b ∈ B.small m S (R.boundary k)
    · rw [if_pos hsmall]
      have hsub : (R.youngFront (R.boundary A) k).filter (fun v => B.vertexBatch v = b) ⊆
          B.frontier S (R.boundary k) b := by
        intro v hv
        have hi := mem_filter.mp hv
        have hr := (mem_filter.mp (mem_filter.mp hi.1).1).2.2
        exact mem_filter.mpr ⟨mem_univ _, hi.2, hr⟩
      exact (card_le_card hsub).trans (mem_filter.mp hsmall).2.2
    · rw [if_neg hsmall]
      apply Nat.le_zero.mpr
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hi := mem_filter.mp hv
      have hs := (mem_filter.mp (mem_filter.mp hi.1).1).2.1
      rw [hi.2] at hs
      exact hsmall hs
  have hs := sum_le_sum hper
  rw [sum_comm] at hs
  have hb : ∀ b ∈ N, (∑ k ∈ Ico A K, if b ∈ B.small m S (R.boundary k) then m else 0) ≤ L * m := by
    intro b hb
    have hsub : (Ico A K).filter (fun k => b ∈ B.small m S (R.boundary k)) ⊆
        Instance.markedRounds (fun k => b ∈ B.small m S (R.boundary k)) K := by
      intro k hk
      have hk' := mem_filter.mp hk
      simp only [Instance.markedRounds, mem_filter, mem_range]
      exact ⟨(mem_Ico.mp hk'.1).2, hk'.2⟩
    have hc := (card_le_card hsub).trans (R.small_round_count hO hL b K)
    have hm := Nat.mul_le_mul_right m hc
    simpa [sum_ite] using hm
  have hh := hs.trans (sum_le_sum hb)
  simpa [N] using hh

/-- Aggregate interference while the target batch remains unfinished at all
round starts. The count is derived from frontier service and eligibility
spacing; no interference bound is assumed in the round specification. -/
theorem interval_capacity_bound (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L)
    {A K : ℕ} {b : Fin batches} (hAK : A ≤ K)
    (hba : B.eligible b ≤ R.boundary A)
    (hactive : ∀ k, A ≤ k → k < K → B.Active S (R.boundary k) b) :
    m * (R.boundary K - R.boundary A) ≤
      16 * m * L ^ 2 +
      (univ.filter (fun c => R.boundary A < B.eligible c ∧ B.eligible c ≤ R.boundary K)).card * (L * m) + L * m := by
  classical
  have hs := sum_le_sum (s := Ico A K) (fun k hk =>
    R.round_interference hm hba (hactive k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2))
  rw [← mul_sum, R.lengths_sum hAK, sum_add_distrib, sum_add_distrib] at hs
  have ho := (R.old_service_sum_bound hAK).trans (R.remaining_work_bound hm hLp hO hL A)
  have hy := R.young_front_sum_bound hO hL hAK
  have hmcount : (∑ k ∈ Ico A K, if b ∈ B.small m S (R.boundary k) then m else 0) ≤ L * m := by
    have hsub : (Ico A K).filter (fun k => b ∈ B.small m S (R.boundary k)) ⊆
        Instance.markedRounds (fun k => b ∈ B.small m S (R.boundary k)) K := by
      intro k hk
      have hk' := mem_filter.mp hk
      simp only [Instance.markedRounds, mem_filter, mem_range]
      exact ⟨(mem_Ico.mp hk'.1).2, hk'.2⟩
    have hc := (card_le_card hsub).trans (R.small_round_count hO hL b K)
    simpa [sum_ite] using Nat.mul_le_mul_right m hc
  omega

/-- The full SFF duration estimate for every finite prefix of unfinished
rounds, now proved using the concrete schedule and operational round routine. -/
theorem unfinished_interval_bound (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L)
    {A K : ℕ} {b : Fin batches} (hAK : A ≤ K)
    (hba : B.eligible b ≤ R.boundary A)
    (hactive : ∀ k, A ≤ k → k < K → B.Active S (R.boundary k) b) :
    R.boundary K - R.boundary A ≤ 32 * L ^ 2 + 4 * L := by
  have hcap := R.interval_capacity_bound hm hLp hO hL hAK hba hactive
  have hnew := B.eligible_count_scaled hLp (R.strict.monotone hAK)
  have hscaled := Nat.mul_le_mul_left m hnew
  have hmul : m * (R.boundary K - R.boundary A) ≤ m * (32 * L ^ 2 + 4 * L) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hmul hm

end Scheduling.SFFRounds
