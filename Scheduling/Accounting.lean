import Scheduling.FrontierProgress

/-! Arithmetic and finite-trace components of Sections 3 and 4.2.
These are deliberately separate from the complete FIFO theorem. They do not
claim that an adversary or an SFF execution satisfying the premises has been
constructed. -/
namespace Scheduling.Accounting
open Finset

/-- The strict capacity gap in Lemma 7, clearing all denominators. -/
theorem forcing_capacity_gap {q c m L processed : ℕ}
    (hm : 0 < m) (hL : 0 < L) (hq : q ≤ c)
    (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (hwork : 2 * processed ≤ q * (4 * m + L)) :
    2 * processed < m * L := by
  have h₁ := Nat.mul_le_mul_right m hcL
  have h₂ := Nat.mul_le_mul_right L hcm
  have h₃ := Nat.mul_le_mul_right (4 * m + L) hq
  have hp : 0 < m * L := Nat.mul_pos hm hL
  nlinarith

/-- A fully loaded epoch's backlog is exactly its accumulated idle capacity. -/
def idleBacklog (capacity : ℕ) (served : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ range N, (capacity - served k)

theorem idleBacklog_conservation {capacity : ℕ} {served : ℕ → ℕ}
    (hcap : ∀ k, served k ≤ capacity) (N : ℕ) :
    idleBacklog capacity served N + ∑ k ∈ range N, served k = N * capacity := by
  unfold idleBacklog
  rw [← sum_add_distrib]
  have he : ∀ k, capacity - served k + served k = capacity :=
    fun k => Nat.sub_add_cancel (hcap k)
  simp [he, sum_const, Nat.mul_comm]

/-- If every c-th epoch wastes a slot, K such epochs force backlog at least K. -/
theorem forcing_epochs_accumulate {capacity c K : ℕ} {served : ℕ → ℕ}
    (hc : 0 < c)
    (hidle : ∀ k < K, served (c * k) < capacity) :
    K ≤ idleBacklog capacity served (c * K) := by
  classical
  let forced := (range K).image (fun k => c * k)
  have hinj : Function.Injective (fun k : ℕ => c * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hc hab
  have hcforced : forced.card = K := by simp [forced, card_image_of_injective _ hinj]
  have hsub : forced ⊆ range (c * K) := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hk) hc)
  have hsum : forced.card ≤ ∑ i ∈ forced, (capacity - served i) := by
    calc
      forced.card = ∑ _i ∈ forced, 1 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
        have := hidle k (mem_range.mp hk)
        omega
  rw [hcforced] at hsum
  exact hsum.trans (sum_le_sum_of_subset hsub)

/-- The final deterministic lower-bound contradiction, after the adversarial
construction has established an idle slot at each forcing epoch. -/
theorem forcing_backlog_contradiction {capacity c : ℕ} {served : ℕ → ℕ}
    (hc : 0 < c) (hcapacity : 0 < capacity)
    (hidle : ∀ k < c * capacity, served (c * k) < capacity)
    (hyoung : idleBacklog capacity served (c * (c * capacity)) ≤ (c - 1) * capacity) : False := by
  have hlarge := forcing_epochs_accumulate hc hidle
  have hc1 : c - 1 + 1 = c := by omega
  nlinarith

/-- Theorem 10's final accounting step (a conditional numerical lemma).
`old` is service to the batches already present on admission; `other` is
service to younger batches together with idle capacity. -/
theorem sff_duration_bound {m L T old other : ℕ} (hm : 0 < m)
    (htotal : m * T = old + other)
    (hold : old ≤ 16 * m * L ^ 2)
    (hother : 2 * other ≤ m * T + 6 * m * L) :
    T ≤ 32 * L ^ 2 + 6 * L := by
  have hscaled : m * T ≤ m * (32 * L ^ 2 + 6 * L) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hscaled hm

theorem sff_flow_bound {L T flow : ℕ} (hL : 0 < L)
    (hT : T ≤ 32 * L ^ 2 + 6 * L)
    (hflow : flow ≤ 2 * L + 4 * L + T) : flow ≤ 44 * L ^ 2 := by
  nlinarith

end Scheduling.Accounting
