import Scheduling.RandomizedFamily

namespace Scheduling
open MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [MeasurableSpace Ω]

/-- General randomized lower bound against an oblivious adversary. One
finite out-forest has large expected flow over all random seeds. -/
theorem randomized_lower_bound {m c L : ℕ} (hm : 2 ≤ m) (hc : 0 < c) (hL : 0 < L)
    (heven : 2 * (L / 2) = L) (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedScheduler Ω m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      L ≤ I.optimum m (by omega) ∧ I.optimum m (by omega) ≤ 2 * L ∧
      (c * L : ℝ≥0∞) ≤ 2 * A.expectedFlow μ I := by
  obtain ⟨Q, hf, hlo, hhi, _, hexp⟩ := HardFamily.expected_lower (b := 2) (c := c)
    (by omega : 0 < m) hL μ A (HardFamily.general (c * (c * (m * L))) m L (by omega) hL)
    (fun P hP => (HardFamily.mem_general P).mp hP)
    (fun B Q d => HardFamily.general_hard_after hm hc hL heven hcL hcm B Q.graph d)
  exact ⟨Q.jobs, Q.vertices, Q.graph, hf, hlo, hhi, hexp⟩

/-- The `Ω(min(m, OPT))` lower bound for arbitrary measurable randomized
causal schedulers, at every positive scale divisible by sixteen. -/
theorem randomized_competitive_lower {m L : ℕ} (hm : 2 ≤ m)
    (hL : 16 ≤ L) (hdiv : 16 ∣ L)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedScheduler Ω m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      L ≤ I.optimum m (by omega) ∧ I.optimum m (by omega) ≤ 2 * L ∧
      (↑(min m (I.optimum m (by omega))) : ℝ≥0∞) * I.optimum m (by omega) ≤
        128 * A.expectedFlow μ I := by
  let c := min (m / 2) (L / 16)
  have hc : 0 < c := by dsimp [c]; omega
  have hcL : 16 * c ≤ L := by dsimp [c]; omega
  have hcm : 2 * c ≤ m := by dsimp [c]; omega
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have heven : 2 * (L / 2) = L := by omega
  obtain ⟨jobs, vertices, I, hf, hlo, hhi, hexp⟩ :=
    randomized_lower_bound hm hc (by omega) heven hcL hcm μ A
  refine ⟨jobs, vertices, I, hf, hlo, hhi, ?_⟩
  have hmin : min m (I.optimum m (by omega)) ≤ 32 * c := by
    by_cases hh : m / 2 ≤ L / 16
    · have he : c = m / 2 := min_eq_left hh
      omega
    · have he : c = L / 16 := min_eq_right (by omega)
      omega
  have hn : min m (I.optimum m (by omega)) * I.optimum m (by omega) ≤ 64 * (c * L) := by
    have h₁ := Nat.mul_le_mul_right (I.optimum m (by omega)) hmin
    have h₂ := Nat.mul_le_mul_left c hhi
    nlinarith
  calc
    (↑(min m (I.optimum m (by omega))) : ℝ≥0∞) * I.optimum m (by omega) ≤
        64 * (c * L : ℝ≥0∞) := by
          have hh : (↑(min m (I.optimum m (by omega)) * I.optimum m (by omega)) : ℝ≥0∞) ≤ ↑(64 * (c * L)) := Nat.cast_le.mpr hn
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
    _ ≤ 64 * (2 * A.expectedFlow μ I) := mul_le_mul le_rfl hexp zero_le zero_le
    _ = 128 * A.expectedFlow μ I := by ring

/-- Randomized batched lower bound with exact optimum and releases at
multiples of that optimum. The entire instance is fixed before the seed. -/
theorem randomized_batched_lower_bound {m c : ℕ}
    (hm : 2 ≤ m) (hc : 0 < c) (hcm : 2 * c ≤ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedScheduler Ω m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) = 8 * c * 5 ^ c ∧
      (∀ j, I.optimum m (by omega) ∣ I.release j) ∧
      (c : ℝ≥0∞) * I.optimum m (by omega) ≤ 2 * A.expectedFlow μ I := by
  let L := 8 * c * 5 ^ c
  have hL : 0 < L := Nat.mul_pos (Nat.mul_pos (by omega) hc) (pow_pos (by omega) c)
  have hdiv : 2 ∣ L := ⟨4 * c * 5 ^ c, by dsimp [L]; ring⟩
  have heven : 2 * (L / 2) = L := by
    have := Nat.mod_eq_zero_of_dvd hdiv
    omega
  obtain ⟨Q, hf, hlo, hhi, hrel, hexp⟩ := HardFamily.expected_lower (b := 1) (c := c)
    (by omega : 0 < m) hL μ A (HardFamily.batched (c * (m * L)) m L (by omega) hL)
    (fun P hP => by
      have he := (HardFamily.mem_batched P).mp hP
      exact ⟨he.ge, by simpa only [one_mul] using he.le⟩)
    (fun B Q d => HardFamily.batched_hard_after hm hc hL heven hcm rfl B Q.graph d)
  simp only [one_mul] at hhi
  have he : Q.graph.optimum m (by omega) = L := le_antisymm hhi hlo
  refine ⟨Q.jobs, Q.vertices, Q.graph, hf, he, ?_, ?_⟩
  · simpa only [he] using hrel
  · simpa only [he] using hexp

/-- The logarithmic batched lower bound for randomized causal schedulers. -/
theorem randomized_batched_competitive_lower {m c : ℕ}
    (hm : 2 ≤ m) (hc : 0 < c) (hcm : 2 * c ≤ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedScheduler Ω m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) = 8 * c * 5 ^ c ∧
      (∀ j, I.optimum m (by omega) ∣ I.release j) ∧
      (↑(min m (Nat.clog 2 (I.optimum m (by omega)))) : ℝ≥0∞) * I.optimum m (by omega) ≤
        14 * A.expectedFlow μ I := by
  obtain ⟨jobs, vertices, I, hf, hopt, hrel, hexp⟩ := randomized_batched_lower_bound hm hc hcm μ A
  refine ⟨jobs, vertices, I, hf, hopt, hrel, ?_⟩
  have hlog : Nat.clog 2 (I.optimum m (by omega)) ≤ 7 * c := by
    rw [hopt]
    exact batched_scale_clog_le hc
  have hmin := (min_le_right m (Nat.clog 2 (I.optimum m (by omega)))).trans hlog
  have hn := Nat.mul_le_mul_right (I.optimum m (by omega)) hmin
  calc
    (↑(min m (Nat.clog 2 (I.optimum m (by omega)))) : ℝ≥0∞) * I.optimum m (by omega) ≤
        7 * ((c : ℝ≥0∞) * I.optimum m (by omega)) := by
          have hh : (↑(min m (Nat.clog 2 (I.optimum m (by omega))) * I.optimum m (by omega)) : ℝ≥0∞) ≤ ↑((7 * c) * I.optimum m (by omega)) := Nat.cast_le.mpr hn
          simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hh
    _ ≤ 7 * (2 * A.expectedFlow μ I) := mul_le_mul le_rfl hexp zero_le zero_le
    _ = 14 * A.expectedFlow μ I := by ring

end Scheduling
