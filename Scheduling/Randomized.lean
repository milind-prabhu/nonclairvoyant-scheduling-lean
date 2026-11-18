import Scheduling.FiniteAmplification
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.BigOperators

namespace Scheduling
open Finset MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- A random seed selects a causal scheduler. The seed space may be
arbitrary; only the flow on each finite input must be measurable. -/
structure RandomizedScheduler (Ω : Type*) [MeasurableSpace Ω] (m : ℕ) where
  scheduler : Ω → DeterministicScheduler m
  measurableFlow : ∀ {jobs vertices} (I : Instance jobs vertices),
    Measurable (fun ω => (I.maxFlow ((scheduler ω).schedule I) : ℝ≥0∞))

namespace RandomizedScheduler
variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- Extended nonnegative expectation also covers infinite expected flow. -/
noncomputable def expectedFlow (A : RandomizedScheduler Ω m) (μ : Measure Ω)
    {jobs vertices : ℕ} (I : Instance jobs vertices) : ℝ≥0∞ :=
  ∫⁻ ω, (I.maxFlow ((A.scheduler ω).schedule I) : ℝ≥0∞) ∂μ

end RandomizedScheduler

namespace FiniteAmplification

/-- Finite-input averaging over an arbitrary probability space of seeds.
The selected input is independent of the seed. -/
theorem exists_expected_large {β Ω : Type*} [Fintype β] [Nonempty β]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cost : β → Ω → ℕ) (F : ℕ)
    (hmeas : ∀ b, Measurable (fun ω => (cost b ω : ℝ≥0∞)))
    (hlower : ∀ ω, Fintype.card β * F ≤ 2 * ∑ b, cost b ω) :
    ∃ b, (F : ℝ≥0∞) ≤ 2 * ∫⁻ ω, (cost b ω : ℝ≥0∞) ∂μ := by
  have hp : ∀ ω, (Fintype.card β : ℝ≥0∞) * F ≤ 2 * ∑ b, (cost b ω : ℝ≥0∞) := by
    intro ω
    exact_mod_cast hlower ω
  have hi := lintegral_mono hp (μ := μ)
  rw [lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ (by norm_num), lintegral_finsetSum univ (fun b _ => hmeas b)] at hi
  have hs : (∑ _b : β, (F : ℝ≥0∞)) ≤ ∑ b : β, 2 * ∫⁻ ω, (cost b ω : ℝ≥0∞) ∂μ := by
    simpa only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum] using hi
  obtain ⟨b, _, hb⟩ := ENNReal.exists_le_of_sum_le (s := univ) univ_nonempty hs
  exact ⟨b, hb⟩

end FiniteAmplification

namespace InstanceSequence
variable {α Ω : Type*} [Fintype α] [Nonempty α] [MeasurableSpace Ω] {m : ℕ}

theorem sum_flow_lower (G : α → PackedInstance) (D F : ℕ) (A : DeterministicScheduler m)
    (hgap : ∀ x j, (G x).graph.release j + F ≤ D)
    (hhard : ∀ P : PackedInstance, ∀ d, ∃ x, F ≤ (P.append (G x) d).onlineFlow A) :
    Fintype.card (Fin (Fintype.card α) → α) * F ≤
      2 * ∑ w : Fin (Fintype.card α) → α, (concatenate G D (List.ofFn w)).onlineFlow A :=
  FiniteAmplification.cost_sum_lower (fun xs => (concatenate G D xs).onlineFlow A) F
    (bad_persists G D F A hgap) (exists_bad_next G D F A hhard)

theorem exists_expected_flow (G : α → PackedInstance) (D F : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedScheduler Ω m)
    (hgap : ∀ x j, (G x).graph.release j + F ≤ D)
    (hhard : ∀ B : DeterministicScheduler m, ∀ P : PackedInstance, ∀ d,
      ∃ x, F ≤ (P.append (G x) d).onlineFlow B) :
    ∃ w : Fin (Fintype.card α) → α,
      (F : ℝ≥0∞) ≤ 2 * A.expectedFlow μ (concatenate G D (List.ofFn w)).graph := by
  apply FiniteAmplification.exists_expected_large μ
    (fun w ω => (concatenate G D (List.ofFn w)).onlineFlow (A.scheduler ω)) F
  · intro w
    exact A.measurableFlow _
  · intro ω
    exact sum_flow_lower G D F (A.scheduler ω) hgap (hhard _)

end InstanceSequence
end Scheduling
