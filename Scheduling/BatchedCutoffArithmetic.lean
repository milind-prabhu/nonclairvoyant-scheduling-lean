import Scheduling.BatchedWideUpper
import Mathlib.Data.List.Sort

namespace Scheduling.BatchedForcing

theorem list_sum_le_mul_sum {α : Type*} (xs : List α) (f g : α → ℕ) (b : ℕ)
    (h : ∀ x ∈ xs, f x ≤ b * g x) : (xs.map f).sum ≤ b * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

theorem list_sum_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (b : ℕ)
    (h : ∀ x ∈ xs, f x ≤ b) : (xs.map f).sum ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem passivityBounds_map {α : Type*} (m c : ℕ) (xs : List α) (D : α → ℕ)
    (h : ∀ before x after, xs = before ++ x :: after →
      (m - c) * D x ≤ (2 * m - 1) * (c + (after.map (fun y => D y + 2)).sum)) :
    PassivityBounds m c (xs.map D) := by
  induction xs with
  | nil => exact PassivityBounds.nil
  | cons x xs ih =>
    apply PassivityBounds.cons
    · rw [List.map_map]
      exact h [] x xs rfl
    · apply ih
      intro before y after he
      exact h (x :: before) y after (by simp only [List.cons_append, he])

/-- Summing per-job cutoff bounds in chronological cutoff order gives
exactly the suffix inequalities used by the geometric recurrence. -/
theorem sorted_cutoffs_passivity {α : Type*} (m c a z : ℕ) (xs : List α)
    (T : α → ℕ) (F : α → ℕ → ℕ)
    (hlen : xs.length ≤ c)
    (hsort : xs.Pairwise (fun x y => T x ≤ T y))
    (htimes : ∀ x ∈ xs, a ≤ T x ∧ T x ≤ z)
    (hcapacity : ∀ u, a ≤ u → u ≤ z → (m - c) * (z - u) ≤ (xs.map (fun x => F x u)).sum)
    (htotal : ∀ x ∈ xs, ∀ u, a ≤ u → u ≤ z → F x u ≤ (2 * m - 1) * (z - T x + 2))
    (hsuffix : ∀ x ∈ xs, ∀ u, T x ≤ u → F x u ≤ 2 * m - 1)
    (haz : a ≤ z) :
    PassivityBounds m c ((z - a) :: xs.map (fun x => z - T x)) := by
  apply PassivityBounds.cons
  · have hu := hcapacity a le_rfl haz
    have hh := list_sum_le_mul_sum xs (fun x => F x a) (fun x => z - T x + 2)
      (2 * m - 1) (fun x hx => htotal x hx a le_rfl haz)
    simp only [List.map_map]
    have hadd := Nat.mul_le_mul_left (2 * m - 1)
      (Nat.le_add_left (xs.map (fun x => z - T x + 2)).sum c)
    exact hu.trans (hh.trans hadd)
  · apply passivityBounds_map
    intro before x after he
    have hx : x ∈ xs := he ▸ List.mem_append_right before List.mem_cons_self
    have hbefore : ∀ y ∈ before, y ∈ xs := fun y hy => he ▸ List.mem_append_left _ hy
    have hafter : ∀ y ∈ after, y ∈ xs := fun y hy =>
      he ▸ List.mem_append_right before (List.mem_cons_of_mem x hy)
    have horder : ∀ y ∈ before, T y ≤ T x := by
      rw [he, List.pairwise_append] at hsort
      intro y hy
      exact hsort.2.2 y hy x List.mem_cons_self
    have hlen' : before.length + 1 ≤ c := by
      rw [he, List.length_append, List.length_cons] at hlen
      omega
    have htime := htimes x hx
    have hu := hcapacity (T x) htime.1 htime.2
    have hb := list_sum_le_length_mul before (fun y => F y (T x)) (2 * m - 1)
      (fun y hy => hsuffix y (hbefore y hy) (T x) (horder y hy))
    have hxbound := hsuffix x hx (T x) le_rfl
    have ha := list_sum_le_mul_sum after (fun y => F y (T x)) (fun y => z - T y + 2)
      (2 * m - 1) (fun y hy => htotal y (hafter y hy) (T x) htime.1 htime.2)
    rw [he, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hu
    have hprefix := Nat.mul_le_mul_right (2 * m - 1) hlen'
    nlinarith

end Scheduling.BatchedForcing
