import Scheduling.Batched
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Log

/-! Work conservation at strict record times for batched FIFO arrivals. -/
namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Work left just before the arrivals at time `t`. -/
noncomputable def beforeArrival (S : Assignment (vertices := vertices)) (t : ℕ) :
    Finset (Fin vertices) :=
  univ.filter (fun v => I.release (I.owner v) < t ∧ t ≤ S v)

/-- All releases are multiples of the batch spacing. -/
def BatchedArrivals (L : ℕ) : Prop := ∀ j, L ∣ I.release j

/-- The earlier batches still unfinished just before boundary `h * L`. -/
noncomputable def unfinishedBatches (S : Assignment (vertices := vertices)) (L h : ℕ) :
    Finset ℕ := (range h).filter (fun i => (I.batchRemaining S (i * L) (h * L)).Nonempty)

/-- A prefix retains exactly its unprocessed work; no later arrival joins it. -/
theorem prefix_conservation {S : Assignment (vertices := vertices)} {r t : ℕ}
    (hrt : r ≤ t) :
    (univ.filter (fun v => I.release (I.owner v) ≤ r ∧ t ≤ S v)).card +
      (I.prefixWork S r t).card = (I.remaining S r).card := by
  classical
  let A := univ.filter (fun v => I.release (I.owner v) ≤ r ∧ t ≤ S v)
  have hd : Disjoint A (I.prefixWork S r t) := by
    apply disjoint_left.mpr
    intro v hv hw
    have ha := (mem_filter.mp hv).2
    have hb := (mem_filter.mp hw).2
    try dsimp at ha
    omega
  have he : A ∪ I.prefixWork S r t = I.remaining S r := by
    ext v
    simp only [A, prefixWork, remaining, mem_union, mem_filter, mem_univ, true_and]
    omega
  rw [← card_union_of_disjoint hd, he]

/-- Full prefix slots contribute `m` units even when the target batch has
already finished. This form is useful for comparing record backlogs. -/
theorem prefix_full_work {m r t : ℕ} {S : Assignment (vertices := vertices)} :
    m * (t - r) ≤ (I.prefixWork S r t).card +
      m * (I.partialSlots m S r t).card := by
  classical
  let F := (Ico r t).filter (I.PrefixFull m S r)
  have hpart : F.card + (I.partialSlots m S r t).card = t - r := by
    simpa [F, partialSlots] using
      card_filter_add_card_filter_not (s := Ico r t) (I.PrefixFull m S r)
  have hsum : m * F.card ≤ (I.prefixWork S r t).card := by
    rw [I.prefixWork_card]
    calc
      _ = ∑ s ∈ F, (I.prefixService S r s).card := by
        have he : (∑ s ∈ F, (I.prefixService S r s).card) = ∑ _s ∈ F, m := by
          apply sum_congr rfl
          intro s hs
          exact (mem_filter.mp hs).2
        rw [he]
        simp [Nat.mul_comm]
      _ ≤ ∑ s ∈ Ico r t, (I.prefixService S r s).card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
  rw [← hpart, Nat.mul_add]
  omega

theorem remaining_at_arrival {m L r : ℕ} {S O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) :
    (I.remaining S r).card ≤ (I.beforeArrival S r).card + m * L := by
  classical
  let A := univ.filter (fun v => I.release (I.owner v) = r)
  have hsub : I.remaining S r ⊆ I.beforeArrival S r ∪ A := by
    intro v hv
    have h := (mem_filter.mp hv).2
    by_cases he : I.release (I.owner v) = r
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, he⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, by omega, h.2⟩)
  have ha : A.card ≤ m * L := by
    have h := I.arrival_work_bound (a := r) (b := r) hO hL
    simpa [A, Nat.le_antisymm_iff, and_comm] using h
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ha _))

theorem beforeArrival_partition {S : Assignment (vertices := vertices)} {L h r : ℕ}
    (hL : 0 < L) (hb : I.BatchedArrivals L) (hr : r < h * L) :
    (I.beforeArrival S (h * L)).card =
      (univ.filter (fun v => I.release (I.owner v) ≤ r ∧ h * L ≤ S v)).card +
      ∑ i ∈ (I.unfinishedBatches S L h).filter (fun i => r < i * L),
        (I.batchRemaining S (i * L) (h * L)).card := by
  classical
  let A := univ.filter (fun v => I.release (I.owner v) ≤ r ∧ h * L ≤ S v)
  let Y := univ.filter (fun v => r < I.release (I.owner v) ∧
    I.release (I.owner v) < h * L ∧ h * L ≤ S v)
  have hd : Disjoint A Y := by
    apply disjoint_left.mpr
    intro v hv hw
    have ha := (mem_filter.mp hv).2
    have hy := (mem_filter.mp hw).2
    try dsimp at ha hy
    omega
  have he : I.beforeArrival S (h * L) = A ∪ Y := by
    ext v
    simp only [beforeArrival, A, Y, mem_filter, mem_univ, true_and, mem_union]
    omega
  have hdiv (v : Fin vertices) : I.release (I.owner v) / L * L = I.release (I.owner v) :=
    Nat.div_mul_cancel (hb _)
  have hsum : Y.card = ∑ i ∈ (I.unfinishedBatches S L h).filter (fun i => r < i * L),
      (Y.filter (fun v => I.release (I.owner v) / L = i)).card := by
    apply card_eq_sum_card_fiberwise
    intro v hv
    have hv' := (mem_filter.mp hv).2
    try dsimp at hv'
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hL).mpr hv'.2.1
    · exact ⟨v, mem_filter.mpr ⟨mem_univ _, (hdiv v).symm, hv'.2.2⟩⟩
    · simpa [hdiv v] using hv'.1
  rw [he, card_union_of_disjoint hd, hsum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := (mem_filter.mp hi)
  have hir : i < h := mem_range.mp (mem_filter.mp hi'.1).1
  congr 1
  ext v
  simp only [Y, batchRemaining, mem_filter, mem_univ, true_and]
  have hm : i * L < h * L := Nat.mul_lt_mul_of_pos_right hir hL
  have hdivi : i * L / L = i := Nat.mul_div_cancel i hL
  constructor
  · intro hv
    exact ⟨by rw [← hdiv v, hv.2], hv.1.2.2⟩
  · intro hv
    exact ⟨⟨by omega, by omega, hv.2⟩, by rw [hv.1, hdivi]⟩

/-- The strict record inequality is derived from the concrete schedule and
the offline comparison, rather than assumed as a numerical premise. -/
theorem record_prefix_idle {m L h i : ℕ} {S O : Assignment (vertices := vertices)}
    (_hm : 0 < m) (hLpos : 0 < L) (hb : I.BatchedArrivals L)
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O)
    (hL : I.FlowBound O L)
    (hrecord : ∀ j < h, (I.beforeArrival S (j * L)).card <
      (I.beforeArrival S (h * L)).card)
    (hi : i ∈ I.unfinishedBatches S L h) :
    1 + ∑ j ∈ (I.unfinishedBatches S L h).filter (fun j => i < j),
      (I.partialSlots m S (j * L) (h * L)).card ≤
      (I.partialSlots m S (i * L) (h * L)).card := by
  classical
  have hih : i < h := mem_range.mp (mem_filter.mp hi).1
  have hit : i * L < h * L := Nat.mul_lt_mul_of_pos_right hih hLpos
  let Y := (I.unfinishedBatches S L h).filter (fun j => i < j)
  let z := fun j => (I.partialSlots m S (j * L) (h * L)).card
  let w := fun j => (I.batchRemaining S (j * L) (h * L)).card
  have hycard : Y.card + 1 ≤ h - i := by
    have hsub : Y ⊆ Ico (i + 1) h := by
      intro j hj
      have hj' := mem_filter.mp hj
      have hjh := mem_range.mp (mem_filter.mp hj'.1).1
      exact mem_Ico.mpr ⟨by omega, hjh⟩
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hwz : (∑ j ∈ Y, w j) + m * (∑ j ∈ Y, z j) ≤ Y.card * (m * L) := by
    have hterm : ∀ j ∈ Y, w j + m * z j ≤ m * L := by
      intro j hj
      have hj' := (mem_filter.mp hj).1
      have hjh := mem_range.mp (mem_filter.mp hj').1
      have hjt : j * L ≤ h * L := Nat.mul_le_mul_right L (by omega)
      have hz := I.batch_prefix_idle_lt hS hF hO hL hjt (mem_filter.mp hj').2
      have hw := I.batch_remaining_work_bound hS hF hO hL hjt
      change z j < L at hz
      change w j ≤ m * (L - z j) at hw
      have he : L - z j + z j = L := by omega
      nlinarith
    have hh := sum_le_sum hterm
    simpa [sum_add_distrib, mul_sum] using hh
  have hc := I.prefix_conservation (S := S) hit.le
  have hf := I.prefix_full_work (S := S) (m := m) (r := i * L) (t := h * L)
  have ha := I.remaining_at_arrival (S := S) (r := i * L) hO hL
  have hp := I.beforeArrival_partition (S := S) hLpos hb hit
  have he : (I.unfinishedBatches S L h).filter (fun j => i * L < j * L) = Y := by
    ext j
    simp [Y, Nat.mul_lt_mul_right hLpos]
  rw [he] at hp
  have hr := hrecord i hih
  have htime : h * L - i * L = (h - i) * L := (Nat.sub_mul h i L).symm
  rw [htime] at hf
  have hage := Nat.mul_le_mul_left (m * L) hycard
  change 1 + ∑ j ∈ Y, z j ≤ z i
  change (I.beforeArrival S (h * L)).card = _ + ∑ j ∈ Y, w j at hp
  change m * ((h - i) * L) ≤ _ + m * z i at hf
  nlinarith

end Scheduling.Instance

namespace Scheduling.Accounting
open Finset

/-- Exponential growth for a finite set of batch indices, with newer indices
on the right. This avoids requiring unfinished batches to be consecutive. -/
theorem geometric_finset_sum (B : Finset ℕ) (z : ℕ → ℕ)
    (hz : ∀ i ∈ B, 1 + ∑ j ∈ B.filter (fun j => i < j), z j ≤ z i) :
    2 ^ B.card ≤ 1 + ∑ i ∈ B, z i := by
  classical
  induction B using Finset.induction_on_min with
  | empty => simp
  | insert a B hmin ih =>
    have ha : a ∉ B := by intro ha; exact (lt_irrefl a) (hmin a ha)
    have hB : (insert a B).filter (fun j => a < j) = B := by
      ext j
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hj, hlt⟩
        · omega
        · exact hj
      · intro hj; exact ⟨Or.inr hj, hmin j hj⟩
    have hza := hz a (mem_insert_self _ _)
    rw [hB] at hza
    have hsub : ∀ i ∈ B, 1 + ∑ j ∈ B.filter (fun j => i < j), z j ≤ z i := by
      intro i hi
      have hzi := hz i (mem_insert_of_mem hi)
      have hnot : ¬ i < a := by have := hmin i hi; omega
      simpa [filter_insert, hnot] using hzi
    have hpow := ih hsub
    rw [card_insert_of_notMem ha, pow_succ, sum_insert ha]
    omega

theorem geometric_finset_card (B : Finset ℕ) (z : ℕ → ℕ) (L : ℕ)
    (hz : ∀ i ∈ B, 1 + ∑ j ∈ B.filter (fun j => i < j), z j ≤ z i)
    (hL : ∀ i ∈ B, z i < L) : B.card ≤ Nat.clog 2 L := by
  classical
  by_cases hn : B.Nonempty
  · let a := B.min' hn
    have ha : a ∈ B := B.min'_mem hn
    have hmin : ∀ j ∈ B, a ≤ j := fun j hj => B.min'_le j hj
    have he : B.filter (fun j => a < j) = B.erase a := by
      ext j
      simp only [mem_filter, mem_erase]
      constructor
      · intro hj; exact ⟨by omega, hj.1⟩
      · intro hj; have := hmin j hj.2; exact ⟨hj.2, by omega⟩
    have hza := hz a ha
    rw [he] at hza
    have hsub : ∀ i ∈ B.erase a,
        1 + ∑ j ∈ (B.erase a).filter (fun j => i < j), z j ≤ z i := by
      intro i hi
      apply le_trans _ (hz i (mem_of_mem_erase hi))
      apply Nat.add_le_add_left
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_filter.mpr ⟨mem_of_mem_erase (mem_filter.mp hj).1, (mem_filter.mp hj).2⟩
      · intros; omega
    have hp := geometric_finset_sum (B.erase a) z hsub
    have hlt : 2 ^ (B.erase a).card < L := lt_of_le_of_lt (hp.trans hza) (hL a ha)
    have hc := (Nat.lt_clog_iff_pow_lt (by omega : 1 < 2)).mpr hlt
    have hec := card_erase_add_one ha
    omega
  · simp [not_nonempty_iff_eq_empty.mp hn]

end Scheduling.Accounting

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Lemma 18, now for the actual unfinished batches of a valid FIFO schedule. -/
theorem record_batch_count {m L h : ℕ} {S O : Assignment (vertices := vertices)}
    (hm : 0 < m) (hLpos : 0 < L) (hb : I.BatchedArrivals L)
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O)
    (hL : I.FlowBound O L)
    (hrecord : ∀ j < h, (I.beforeArrival S (j * L)).card <
      (I.beforeArrival S (h * L)).card) :
    (I.unfinishedBatches S L h).card ≤ Nat.clog 2 L := by
  apply Scheduling.Accounting.geometric_finset_card _
    (fun i => (I.partialSlots m S (i * L) (h * L)).card) L
  · intro i hi
    exact I.record_prefix_idle hm hLpos hb hS hF hO hL hrecord hi
  · intro i hi
    have hi' := mem_filter.mp hi
    have hit : i * L ≤ h * L := Nat.mul_le_mul_right L (le_of_lt (mem_range.mp hi'.1))
    exact I.batch_prefix_idle_lt hS hF hO hL hit hi'.2

end Scheduling.Instance

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

theorem beforeArrival_sum {S : Assignment (vertices := vertices)} {L h : ℕ}
    (hL : 0 < L) (hb : I.BatchedArrivals L) :
    (I.beforeArrival S (h * L)).card =
      ∑ i ∈ I.unfinishedBatches S L h, (I.batchRemaining S (i * L) (h * L)).card := by
  classical
  have hdiv (v : Fin vertices) : I.release (I.owner v) / L * L = I.release (I.owner v) :=
    Nat.div_mul_cancel (hb _)
  have he : (I.beforeArrival S (h * L)).card =
      ∑ i ∈ I.unfinishedBatches S L h,
        ((I.beforeArrival S (h * L)).filter (fun v => I.release (I.owner v) / L = i)).card := by
    apply card_eq_sum_card_fiberwise
    intro v hv
    have hv' := (mem_filter.mp hv).2
    refine mem_filter.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hL).mpr hv'.1), ?_⟩
    exact ⟨v, mem_filter.mpr ⟨mem_univ _, (hdiv v).symm, hv'.2⟩⟩
  rw [he]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp (mem_filter.mp hi).1
  have hit : i * L < h * L := Nat.mul_lt_mul_of_pos_right hi' hL
  congr 1
  ext v
  simp only [beforeArrival, batchRemaining, mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    exact ⟨by rw [← hdiv v, hv.2], hv.1.2⟩
  · intro hv
    exact ⟨⟨by omega, hv.2⟩, by rw [hv.1]; exact Nat.mul_div_cancel i hL⟩

/-- A bound at strict records bounds all arrival-boundary backlogs. -/
theorem batched_backlog_bound {m L : ℕ} {S O : Assignment (vertices := vertices)}
    (hm : 0 < m) (hLpos : 0 < L) (hb : I.BatchedArrivals L)
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O)
    (hL : I.FlowBound O L) (h : ℕ) :
    (I.beforeArrival S (h * L)).card ≤ Nat.clog 2 L * (m * L) := by
  classical
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hr : ∀ j < h, (I.beforeArrival S (j * L)).card <
        (I.beforeArrival S (h * L)).card
    · have hc := I.record_batch_count hm hLpos hb hS hF hO hL hr
      rw [I.beforeArrival_sum hLpos hb]
      calc
        _ ≤ ∑ _i ∈ I.unfinishedBatches S L h, m * L := by
          apply sum_le_sum
          intro i hi
          have hi' := mem_range.mp (mem_filter.mp hi).1
          have hw := I.batch_remaining_work_bound hS hF hO hL
            (Nat.mul_le_mul_right L (le_of_lt hi'))
          exact hw.trans (Nat.mul_le_mul_left m (Nat.sub_le _ _))
        _ = (I.unfinishedBatches S L h).card * (m * L) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    · push Not at hr
      obtain ⟨j, hj, hle⟩ := hr
      exact hle.trans (ih j hj)

/-- The batched FIFO upper bound, with its ceiling logarithm and additive
constant, for any positive offline flow bound equal to the batch spacing. -/
theorem batched_fifo_flowBound {m L : ℕ} {S O : Assignment (vertices := vertices)}
    (hm : 0 < m) (hLpos : 0 < L) (hb : I.BatchedArrivals L)
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O)
    (hL : I.FlowBound O L) : I.FlowBound S ((Nat.clog 2 L + 2) * L) := by
  classical
  intro v
  let r := I.release (I.owner v)
  let C := S v + 1
  let P := (I.partialSlots m S r C).card
  let F := ((Ico r C).filter (I.PrefixFull m S r)).card
  have hr : r ≤ S v := hS.release v
  have hp0 := I.partial_slots_lt hS hF hO hL (I.owner v) hr ⟨v, rfl, le_rfl⟩
  have hrec := I.partialSlots_succ (m := m) (S := S) hr
  have hp : P ≤ L := by
    dsimp [P, C, r]
    dsimp [r] at hrec
    split_ifs at hrec <;> omega
  have hpartition : F + P = C - r := by
    dsimp [F, P, partialSlots]
    simpa using card_filter_add_card_filter_not (s := Ico r C) (I.PrefixFull m S r)
  have hwork := I.fifo_service_accounting hS hF (I.owner v) v rfl (t := C) le_rfl
  have ha := I.remaining_at_arrival (S := S) (r := r) hO hL
  have hbkl := I.batched_backlog_bound hm hLpos hb hS hF hO hL (r / L)
  have hrdiv : r / L * L = r := Nat.div_mul_cancel (hb _)
  rw [hrdiv] at hbkl
  change m * F + P ≤ _ at hwork
  have hF : F ≤ (Nat.clog 2 L + 1) * L := by nlinarith
  have hC : C - r ≤ (Nat.clog 2 L + 2) * L := by nlinarith
  dsimp [C, r] at hC hr
  omega

/-- Theorem 4, logarithmic upper bound, specialized to the attained optimum. -/
theorem batched_fifo_competitive {m : ℕ} {S : Assignment (vertices := vertices)}
    (hm : 0 < m) (hj : 0 < jobs) (hb : I.BatchedArrivals (I.optimum m hm))
    (hS : I.Valid m S) (hF : I.IsFIFO m S) :
    I.maxFlow S ≤ (Nat.clog 2 (I.optimum m hm) + 2) * I.optimum m hm := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  exact (I.flowBound_iff_maxFlow_le _ _).mp
    (I.batched_fifo_flowBound hm (I.optimum_pos hm hj) hb hS hF hO hL)

/-- Both FIFO guarantees apply to the same schedule. The minimum is written
without division, preserving the exact general-arrival coefficient. -/
theorem batched_fifo_combined_bound {m : ℕ} {S : Assignment (vertices := vertices)}
    (hm : 0 < m) (hj : 0 < jobs) (hb : I.BatchedArrivals (I.optimum m hm))
    (hS : I.Valid m S) (hF : I.IsFIFO m S) :
    m * I.maxFlow S ≤ min
      ((m * m + m - 1) * I.optimum m hm)
      (m * ((Nat.clog 2 (I.optimum m hm) + 2) * I.optimum m hm)) := by
  exact le_min (I.fifo_competitive hm hS hF)
    (Nat.mul_le_mul_left m (I.batched_fifo_competitive hm hj hb hS hF))

end Scheduling.Instance
