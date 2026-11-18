import Scheduling.Randomized

namespace Scheduling.HardFamily
open Finset MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Amplification of a finite family of regular-release forests. The
output is a single fixed instance, with the same optimum bounds and
release divisibility as its constituent copies. -/
theorem expected_lower {Ω : Type*} [MeasurableSpace Ω]
    {jobs m L b c : ℕ} (hm : 0 < m) (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : RandomizedScheduler Ω m)
    (S : Finset (ForestCode jobs (m * L)))
    (hopt : ∀ P ∈ S, L ≤ (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm ∧
      (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm ≤ b * L)
    (hhard : ∀ B : DeterministicScheduler m, ∀ Q : PackedInstance, ∀ d,
      ∃ P ∈ S, c * L ≤ (Q.graph.append (P.toInstance L (Nat.mul_pos hm hL)) d).maxFlow
        (B.schedule (Q.graph.append (P.toInstance L (Nat.mul_pos hm hL)) d))) :
    ∃ Q : PackedInstance,
      (∀ u v w, Q.graph.edge u w → Q.graph.edge v w → u = v) ∧
      L ≤ Q.graph.optimum m hm ∧ Q.graph.optimum m hm ≤ b * L ∧
      (∀ j, L ∣ Q.graph.release j) ∧ (c * L : ℝ≥0∞) ≤ 2 * A.expectedFlow μ Q.graph := by
  let α := {P // P ∈ S}
  have hΩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨ω⟩ := hΩ
  obtain ⟨P, hP, _⟩ := hhard (A.scheduler ω) PackedInstance.empty 0
  let : Nonempty α := ⟨⟨P, hP⟩⟩
  let G : α → PackedInstance := fun x => ⟨jobs, jobs * (m * L), x.val.toInstance L (Nat.mul_pos hm hL)⟩
  let D := (jobs + b + c) * L
  have hgapB : ∀ x j, (G x).graph.release j + b * L ≤ D := by
    intro x j
    have hj := Nat.mul_le_mul_right L (Nat.le_of_lt j.isLt)
    change j.val * L + b * L ≤ (jobs + b + c) * L
    nlinarith
  have hgapC : ∀ x j, (G x).graph.release j + c * L ≤ D := by
    intro x j
    have hj := Nat.mul_le_mul_right L (Nat.le_of_lt j.isLt)
    change j.val * L + c * L ≤ (jobs + b + c) * L
    nlinarith
  have hoff : ∀ x, ∃ O, (G x).graph.Valid m O ∧ (G x).graph.FlowBound O (b * L) := by
    intro x
    obtain ⟨O, hO, hf⟩ := (G x).graph.optimum_attained hm
    refine ⟨O, hO, ?_⟩
    intro v
    exact (hf v).trans_le (Nat.add_le_add_left (hopt x.val x.property).2 _)
  have hnext : ∀ B : DeterministicScheduler m, ∀ Q : PackedInstance, ∀ d,
      ∃ x, c * L ≤ (Q.append (G x) d).onlineFlow B := by
    intro B Q d
    obtain ⟨P, hP, hf⟩ := hhard B Q d
    exact ⟨⟨P, hP⟩, hf⟩
  obtain ⟨w, hw⟩ := InstanceSequence.exists_expected_flow G D (c * L) μ A hgapC hnext
  have hne : List.ofFn w ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    exact (Nat.ne_of_gt (Fintype.card_pos (α := α))) hh
  let Q := InstanceSequence.concatenate G D (List.ofFn w)
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · exact InstanceSequence.outForest G D (fun x _ _ _ hu hv => x.val.outForest L (Nat.mul_pos hm hL) hu hv) _
  · exact InstanceSequence.optimum_ge G D L hm (fun x => (hopt x.val x.property).1) _ hne
  · obtain ⟨O, hO, hf⟩ := InstanceSequence.offline G D (b * L) m hoff hgapB (List.ofFn w)
    exact Q.graph.optimum_le hm hO hf
  · exact InstanceSequence.batched_releases G D L (dvd_mul_left L _) (fun x j => dvd_mul_left L j.val) _
  · simpa only [Nat.cast_mul] using hw

end Scheduling.HardFamily
