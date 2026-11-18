import Scheduling.BatchedCutoffArithmetic

namespace Scheduling.BatchedAdversary
open Finset LayeredPrefix
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ}

theorem jobWideService_mono_start (m : ℕ) (records : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) {a u b : ℕ} (ha : a ≤ u) :
    jobWideService m records j S u b ≤ jobWideService m records j S a b := by
  apply card_le_card
  intro v hv
  obtain ⟨hw, hlo, hhi⟩ := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ _, hw, ha.trans hlo, hhi⟩

theorem wideService_eq_sum_jobs (m : ℕ) (records : List (LayerRecord jobs work))
    (S : Assignment (vertices := jobs * work)) (a b : ℕ) (J : Finset (Fin jobs))
    (howners : ∀ v, WideRecorded m records (job v) v → a ≤ S v → S v < b → job v ∈ J) :
    wideService m records S a b = ∑ j ∈ J, jobWideService m records j S a b := by
  unfold wideService
  rw [card_eq_sum_card_fiberwise (f := job) (fun v hv =>
    howners v (mem_filter.mp hv).2.1 (mem_filter.mp hv).2.2.1 (mem_filter.mp hv).2.2.2)]
  apply sum_congr rfl
  intro j _
  unfold jobWideService
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hw, ht⟩, ho⟩
    rw [ho] at hw
    exact ⟨hw, ht⟩
  · rintro ⟨hw, ht⟩
    exact ⟨⟨by simpa only [hw.1] using hw, ht⟩, hw.1⟩

/-- Per-job cutoffs and the full-slot lower bound imply the aggregate
recurrence after sorting the cutoffs of jobs that can execute this epoch. -/
theorem cutoffs_passivity (records : List (LayerRecord jobs (m * L)))
    (S : Assignment (vertices := jobs * (m * L))) (i c : ℕ) (J : Finset (Fin jobs))
    (T : Fin jobs → ℕ) (hcut : JobCutoffs m L records S i T) (hcard : J.card ≤ c)
    (howners : ∀ v, WideRecorded m records (job v) v → i * L ≤ S v →
      S v < (i + 1) * L → job v ∈ J)
    (hlower : ∀ u, i * L ≤ u → u ≤ (i + 1) * L →
      (m - c) * ((i + 1) * L - u) ≤ wideService m records S u ((i + 1) * L)) :
    ∃ ds : List ℕ, ds.length ≤ c ∧ BatchedForcing.PassivityBounds m c (L :: ds) := by
  let xs := J.toList.mergeSort (fun x y => decide (T x ≤ T y))
  have hp : xs.Perm J.toList := List.mergeSort_perm _ _
  have hlen : xs.length ≤ c := by
    rw [hp.length_eq, Finset.length_toList]
    exact hcard
  have hsort : xs.Pairwise (fun x y => T x ≤ T y) := by
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun x y : Fin jobs => decide (T x ≤ T y))
        (by intro x y z hxy hyz; simp only [decide_eq_true_eq] at *; omega)
        (by intro x y; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) J.toList)
  have hsum : ∀ u, i * L ≤ u → (xs.map (fun j => jobWideService m records j S u ((i + 1) * L))).sum =
      wideService m records S u ((i + 1) * L) := by
    intro u hu
    rw [(hp.map _).sum_eq, Finset.sum_map_toList]
    symm
    exact wideService_eq_sum_jobs m records S u ((i + 1) * L) J
      (fun v hw hvlo hvhi => howners v hw (hu.trans hvlo) hvhi)
  have hb := BatchedForcing.sorted_cutoffs_passivity m c (i * L) ((i + 1) * L) xs T
    (fun j u => jobWideService m records j S u ((i + 1) * L)) hlen hsort
    (fun j _ => ⟨(hcut j).1, (hcut j).2.1⟩)
    (by intro u hlo hhi; rw [hsum u hlo]; exact hlower u hlo hhi)
    (by
      intro j _ u hlo _
      have hh := (jobWideService_mono_start m records j S hlo).trans (hcut j).2.2.1
      have hx := Nat.mul_le_mul_left (2 * m - 1)
        (show (i + 1) * L - T j + 1 ≤ (i + 1) * L - T j + 2 by omega)
      exact hh.trans hx)
    (fun j _ u hu => (hcut j).2.2.2 u hu) (by nlinarith)
  have hlength : (i + 1) * L - i * L = L := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
  exact ⟨xs.map (fun j => (i + 1) * L - T j), by simpa only [List.length_map] using hlen,
    by simpa only [hlength] using hb⟩

end Scheduling.BatchedAdversary
