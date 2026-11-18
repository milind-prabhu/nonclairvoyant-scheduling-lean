import Scheduling.SFFRoundBounds

namespace Scheduling.Batching
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches L m : ℕ} {I : Instance jobs vertices}
variable (B : Batching I L batches) {S O : Assignment (vertices := vertices)}

noncomputable def eligibleWork (u v : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun w => u < B.eligible (B.vertexBatch w) ∧ B.eligible (B.vertexBatch w) ≤ v)

noncomputable def admittedRemaining (S : Assignment (vertices := vertices)) (t : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun w => B.eligible (B.vertexBatch w) ≤ t ∧ t ≤ S w)

/-- Work admitted through an interval of eligibility times (Lemma 11). -/
theorem eligible_work_bound (hO : I.Valid m O) (hL : I.FlowBound O L)
    {u v : ℕ} (huv : u ≤ v) : (B.eligibleWork u v).card ≤ m * (v - u + 3 * L) := by
  classical
  have h := card_le_slots O m (u - 2 * L) (v + L) (B.eligibleWork u v) hO.capacity (by
    intro w hw
    have hw' := (mem_filter.mp hw).2
    have hl := B.lower (I.owner w)
    have hu := B.upper (I.owner w)
    have he : B.eligible (B.vertexBatch w) ≤ I.release (I.owner w) + 2 * L := by
      dsimp [eligible, vertexBatch]
      nlinarith
    have hp := hO.release w
    have hf := hL w
    have hrel := B.released_by_eligible (v := w) rfl
    exact ⟨by omega, by omega⟩)
  have he : v + L - (u - 2 * L) ≤ v - u + 3 * L := by omega
  exact h.trans (Nat.mul_le_mul_left m he)

/-- Conservation of all admitted work, including unrevealed vertices. -/
theorem admitted_accounting (hE : ∀ w, B.eligible (B.vertexBatch w) ≤ S w)
    {u v : ℕ} (huv : u ≤ v) :
    (B.admittedRemaining S v).card + (I.executedDuring S u v).card ≤
      (B.admittedRemaining S u).card + (B.eligibleWork u v).card := by
  classical
  have hd : Disjoint (B.admittedRemaining S v) (I.executedDuring S u v) := by
    apply disjoint_left.mpr
    intro w hw hz
    have hw' := (mem_filter.mp hw).2
    have hz' := (mem_filter.mp hz).2
    omega
  have hsub : B.admittedRemaining S v ∪ I.executedDuring S u v ⊆
      B.admittedRemaining S u ∪ B.eligibleWork u v := by
    intro w hw
    have hs : u ≤ S w := by
      rcases mem_union.mp hw with h | h
      · have := (mem_filter.mp h).2; omega
      · exact (mem_filter.mp h).2.1
    have he : B.eligible (B.vertexBatch w) ≤ v := by
      rcases mem_union.mp hw with h | h
      · exact (mem_filter.mp h).2.1
      · have := (mem_filter.mp h).2; have := hE w; omega
    by_cases hold : B.eligible (B.vertexBatch w) ≤ u
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hold, hs⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega, he⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  simpa [card_union_of_disjoint hd] using hc

end Scheduling.Batching

namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

theorem executedDuring_card_sum (S : Assignment (vertices := vertices)) (u v : ℕ) :
    (I.executedDuring S u v).card = ∑ t ∈ Ico u v, (univ.filter (fun w => S w = t)).card := by
  classical
  have h := card_eq_sum_card_fiberwise (f := S) (s := I.executedDuring S u v) (t := Ico u v)
    (by intro w hw; exact mem_Ico.mpr (mem_filter.mp hw).2)
  rw [h]
  apply sum_congr rfl
  intro t ht
  have ht' := mem_Ico.mp ht
  congr 1
  ext w
  simp only [executedDuring, mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

/-- Full service except possibly at one timestep loses at most m capacity. -/
theorem service_except_one {m u v bad : ℕ} {S : Assignment (vertices := vertices)}
    (hfull : ∀ t, u ≤ t → t < v → t ≠ bad → (univ.filter (fun w => S w = t)).card = m) :
    m * (v - u) ≤ (I.executedDuring S u v).card + m := by
  classical
  have hslot : ∀ t ∈ Ico u v,
      m ≤ (univ.filter (fun w => S w = t)).card + (if t = bad then m else 0) := by
    intro t ht
    by_cases he : t = bad
    · simp [he]
    · rw [if_neg he, hfull t (mem_Ico.mp ht).1 (mem_Ico.mp ht).2 he]
      omega
  have hs := sum_le_sum hslot
  rw [sum_add_distrib, ← I.executedDuring_card_sum] at hs
  have hbad : (∑ t ∈ Ico u v, if t = bad then m else 0) ≤ m := by
    simp only [sum_ite_eq']
    split_ifs <;> omega
  have hc : (∑ _t ∈ Ico u v, m) = m * (v - u) := by simp [Nat.mul_comm]
  rw [hc] at hs
  omega

end Scheduling.Instance

namespace Scheduling.SFFRounds
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches m L : ℕ} {I : Instance jobs vertices}
variable {B : Batching I L batches} {S O : Assignment (vertices := vertices)}
variable (R : SFFRounds B m S)

theorem sparse_work_bound (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L) {K : ℕ}
    (hn : B.large m S (R.boundary K) = ∅) :
    (B.admittedRemaining S (R.boundary K)).card ≤ 12 * m * L ^ 2 := by
  classical
  have heq : (B.admittedRemaining S (R.boundary K)).card =
      ∑ b ∈ B.small m S (R.boundary K),
        ((B.admittedRemaining S (R.boundary K)).filter (fun v => B.vertexBatch v = b)).card :=
    card_eq_sum_card_fiberwise (by
      intro v hv
      have hv' := (mem_filter.mp hv).2
      have ha : B.Active S (R.boundary K) (B.vertexBatch v) := ⟨hv'.1, v, rfl, hv'.2⟩
      rcases B.active_small_or_large (m := m) ha with hs | hl
      · exact hs
      · rw [hn] at hl; exact False.elim (notMem_empty _ hl))
  have hc : (B.admittedRemaining S (R.boundary K)).card ≤
      (B.small m S (R.boundary K)).card * (3 * m * L) := by
    rw [heq]
    calc
      _ ≤ ∑ _b ∈ B.small m S (R.boundary K), 3 * m * L := by
        apply sum_le_sum
        intro b _
        apply (card_le_card (t := B.batchVertices b) ?_).trans (B.batch_work_bound hO hL b)
        intro v hv
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩
      _ = _ := by simp
  have hcount := (R.round_bounds hm hLp hO hL K).1
  have hmul := Nat.mul_le_mul_right (3 * m * L) hcount
  nlinarith

theorem containing_round {u K t : ℕ} (huK : u ≤ K)
    (htu : R.boundary u ≤ t) (htK : t < R.boundary K) :
    ∃ r, u ≤ r ∧ r < K ∧ R.boundary r ≤ t ∧ t < R.boundary (r + 1) := by
  classical
  let A := (range (K + 1)).filter (fun r => R.boundary r ≤ t)
  have hu : u ∈ A := mem_filter.mpr ⟨mem_range.mpr (by omega), htu⟩
  have hn : A.Nonempty := ⟨u, hu⟩
  let r := A.max' hn
  have hr := mem_filter.mp (Finset.max'_mem A hn)
  have hur : u ≤ r := le_max' A u hu
  have hrK : r < K := by
    have hrle : r ≤ K := by have := mem_range.mp hr.1; omega
    by_contra hge
    have he : r = K := by omega
    have hr' : R.boundary r ≤ t := hr.2
    rw [he] at hr'
    omega
  refine ⟨r, hur, hrK, hr.2, ?_⟩
  by_contra hn'
  have hnext : r + 1 ∈ A := mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩
  have hmax := le_max' A (r + 1) hnext
  change r + 1 ≤ r at hmax
  omega

/-- Lemma 13. The last boundary with no large batch resets the backlog;
all later rounds are full, except possibly the last slot of that one round. -/
theorem remaining_work_bound (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L) (K : ℕ) :
    (B.admittedRemaining S (R.boundary K)).card ≤ 16 * m * L ^ 2 := by
  classical
  let E := (range (K + 1)).filter (fun k => B.large m S (R.boundary k) = ∅)
  have hzero : B.large m S (R.boundary 0) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    have he := (mem_filter.mp hb).2.1.1
    rw [R.starts_zero] at he
    have hp := B.eligible_positive hLp b
    omega
  have he0 : 0 ∈ E := mem_filter.mpr ⟨mem_range.mpr (by omega), hzero⟩
  have hne : E.Nonempty := ⟨0, he0⟩
  let u := E.max' hne
  have hu := mem_filter.mp (Finset.max'_mem E hne)
  have huK : u ≤ K := by have := mem_range.mp hu.1; omega
  have hwu := R.sparse_work_bound hm hLp hO hL hu.2
  have hlarge : ∀ r, u < r → r ≤ K → (B.large m S (R.boundary r)).Nonempty := by
    intro r hur hrK
    by_contra hn
    have he : r ∈ E := mem_filter.mpr ⟨mem_range.mpr (by omega), not_nonempty_iff_eq_empty.mp hn⟩
    have hmax := le_max' E r he
    change r ≤ u at hmax
    omega
  have htimes : R.boundary u ≤ R.boundary K := R.strict.monotone huK
  have hserved : m * (R.boundary K - R.boundary u) ≤
      (I.executedDuring S (R.boundary u) (R.boundary K)).card + m := by
    apply I.service_except_one (bad := R.boundary (u + 1) - 1)
    intro t htu htK htbad
    obtain ⟨r, hur, hrK, htr, hrt⟩ := R.containing_round huK htu htK
    by_cases he : r = u
    · subst r
      apply R.packed u t htr
      omega
    · exact R.fill_last r (hlarge r (by omega) (by omega)) t htr hrt
  have hacc := B.admitted_accounting R.eligible_service htimes
  have harr := B.eligible_work_bound hO hL htimes
  have hl : 3 * L + 1 ≤ 4 * L ^ 2 := by nlinarith
  have hmL := Nat.mul_le_mul_left m hl
  nlinarith

end Scheduling.SFFRounds
