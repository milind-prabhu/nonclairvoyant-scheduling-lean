import Scheduling.SFF
import Mathlib.Data.Finset.Sort

/-! Computable, deterministic packing of a finite set into consecutive slots.
No graph, offline schedule, or noncomputable choice is used by the functions. -/
namespace Scheduling.Packing
open Finset
variable {V : Type*} [LinearOrder V]

def indices (n a b : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => a ≤ i.val ∧ i.val < b)

theorem indices_card (n a b : ℕ) : (indices n a b).card = min b n - a := by
  have he : (indices n a b).image Fin.val = Ico a (min b n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have h := (mem_filter.mp hi).2
      exact mem_Ico.mpr ⟨h.1, lt_min h.2 i.isLt⟩
    · intro hx
      have h := mem_Ico.mp hx
      exact mem_image.mpr ⟨⟨x, (lt_min_iff.mp h.2).2⟩,
        mem_filter.mpr ⟨mem_univ _, h.1, (lt_min_iff.mp h.2).1⟩, rfl⟩
  have hc := card_image_of_injective (indices n a b) Fin.val_injective
  rw [he, Nat.card_Ico] at hc
  exact hc.symm

def slice (s : Finset V) (a b : ℕ) : Finset V :=
  (indices s.card a b).image (s.orderEmbOfFin rfl)

theorem slice_card (s : Finset V) (a b : ℕ) : (slice s a b).card = min b s.card - a := by
  rw [slice, card_image_of_injective _ (s.orderEmbOfFin rfl).injective, indices_card]

theorem slice_subset (s : Finset V) (a b : ℕ) : slice s a b ⊆ s := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := mem_image.mp hv
  exact orderEmbOfFin_mem _ _ _

theorem mem_slice_iff (s : Finset V) (a b : ℕ) (v : V) :
    v ∈ slice s a b ↔ ∃ i : Fin s.card, a ≤ i.val ∧ i.val < b ∧ s.orderEmbOfFin rfl i = v := by
  simp only [slice, indices, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩; exact ⟨i, hi.1, hi.2, he⟩
  · rintro ⟨i, h₁, h₂, he⟩; exact ⟨i, ⟨h₁, h₂⟩, he⟩

theorem slices_disjoint (s : Finset V) {a b c d : ℕ} (hbc : b ≤ c) :
    Disjoint (slice s a b) (slice s c d) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨i, hi₁, hi₂, hi⟩ := (mem_slice_iff _ _ _ _).mp hv
  obtain ⟨j, hj₁, hj₂, hj⟩ := (mem_slice_iff _ _ _ _).mp hw
  have he := (s.orderEmbOfFin rfl).injective (hi.trans hj.symm)
  have he' := congrArg Fin.val he
  omega

/-- An omitted element of the initial slice implies the slice is full. -/
theorem first_slice_full {s : Finset V} {m : ℕ} {v : V}
    (hv : v ∈ s) (hn : v ∉ slice s 0 m) : (slice s 0 m).card = m := by
  let i := (s.orderIsoOfFin rfl).symm ⟨v, hv⟩
  have hi : s.orderEmbOfFin rfl i = v :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨v, hv⟩)
  have him : m ≤ i.val := by
    by_contra h
    exact hn ((mem_slice_iff _ _ _ _).mpr ⟨i, Nat.zero_le _, by omega, hi⟩)
  rw [slice_card, Nat.sub_zero, min_eq_left (by omega)]

/-- Every selected element precedes every omitted element. -/
theorem first_slice_lt {s : Finset V} {m : ℕ} {u v : V}
    (hu : u ∈ slice s 0 m) (hv : v ∈ s) (hn : v ∉ slice s 0 m) : u < v := by
  obtain ⟨i, _, him, hi⟩ := (mem_slice_iff _ _ _ _).mp hu
  let j := (s.orderIsoOfFin rfl).symm ⟨v, hv⟩
  have hj : s.orderEmbOfFin rfl j = v :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨v, hv⟩)
  have hjm : m ≤ j.val := by
    by_contra h
    exact hn ((mem_slice_iff _ _ _ _).mpr ⟨j, Nat.zero_le _, by omega, hj⟩)
  rw [← hi, ← hj]
  exact (s.orderEmbOfFin rfl).strictMono (by show i.val < j.val; omega)

def duration (n m : ℕ) : ℕ := max 1 ((n + m - 1) / m)
def slot (s : Finset V) (m k : ℕ) : Finset V := slice s (k * m) ((k + 1) * m)

theorem duration_pos (n m : ℕ) : 0 < duration n m := by
  unfold duration
  omega

theorem slot_card_le (s : Finset V) (m k : ℕ) : (slot s m k).card ≤ m := by
  rw [slot, slice_card]
  have he : (k + 1) * m = k * m + m := by ring
  omega

theorem before_last_full (s : Finset V) {m k : ℕ} (hm : 0 < m)
    (hk : k + 1 < duration s.card m) : (slot s m k).card = m := by
  have hq : k + 1 < (s.card + m - 1) / m := by unfold duration at hk; omega
  have hp := (Nat.le_div_iff_mul_le hm).mp (show k + 2 ≤ (s.card + m - 1) / m by omega)
  rw [slot, slice_card]
  have hmul : (k + 2) * m = (k + 1) * m + m := by ring
  have hsub : s.card + m - 1 + 1 = s.card + m := by omega
  have hle : (k + 1) * m ≤ s.card := by omega
  rw [min_eq_left hle]
  have he : (k + 1) * m = k * m + m := by ring
  omega

theorem slot_disjoint (s : Finset V) {m i j : ℕ} (hij : i ≠ j) :
    Disjoint (slot s m i) (slot s m j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact slices_disjoint s (Nat.mul_le_mul_right m (show i + 1 ≤ j by omega))
  · exact (slices_disjoint s (Nat.mul_le_mul_right m (show j + 1 ≤ i by omega))).symm

theorem covers (s : Finset V) {m : ℕ} (hm : 0 < m) {v : V} (hv : v ∈ s) :
    ∃ k < duration s.card m, v ∈ slot s m k := by
  let i := (s.orderIsoOfFin rfl).symm ⟨v, hv⟩
  have hi : s.orderEmbOfFin rfl i = v := by
    exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨v, hv⟩)
  have hmod := Nat.mod_lt i.val hm
  have hdiv := Nat.mod_add_div i.val m
  rw [Nat.mul_comm m] at hdiv
  have hcover : s.card ≤ duration s.card m * m := by
    have hquot := Nat.mod_lt (s.card + m - 1) hm
    have hdecomp := Nat.mod_add_div (s.card + m - 1) m
    rw [Nat.mul_comm m] at hdecomp
    have hceil : s.card ≤ ((s.card + m - 1) / m) * m := by omega
    have hmax : (s.card + m - 1) / m ≤ duration s.card m := le_max_right _ _
    exact hceil.trans (Nat.mul_le_mul_right m hmax)
  have hk : i.val / m < duration s.card m := by
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    exact i.isLt.trans_le hcover
  refine ⟨i.val / m, hk, (mem_slice_iff _ _ _ _).mpr ⟨i, ?_, ?_, hi⟩⟩
  · omega
  · have he : (i.val / m + 1) * m = i.val / m * m + m := by ring
    omega

end Scheduling.Packing
