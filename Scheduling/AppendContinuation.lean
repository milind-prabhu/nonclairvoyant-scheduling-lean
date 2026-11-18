import Scheduling.AppendBefore

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

theorem right_executionPrefix {a b d t : ℕ} (U : Assignment (vertices := a + b))
    (hstart : ∀ v, d ≤ U (Fin.natAdd a v)) (ht : d ≤ t) :
    shiftedDone a (executionPrefix U t) = executionPrefix (Instance.rightSchedule U d) (t - d) := by
  ext n
  rw [mem_shiftedDone]
  by_cases hn : n < b
  · let v : Fin b := ⟨n, hn⟩
    change (Fin.natAdd a v).val ∈ executionPrefix U t ↔
      v.val ∈ executionPrefix (Instance.rightSchedule U d) (t - d)
    rw [val_mem_executionPrefix, val_mem_executionPrefix]
    have hh := hstart v
    dsimp only [Instance.rightSchedule]
    omega
  · constructor
    · intro h
      obtain ⟨v, _, hv⟩ := mem_image.mp h
      have hl := v.isLt
      omega
    · intro h
      obtain ⟨v, _, hv⟩ := mem_image.mp h
      have hl := v.isLt
      omega

theorem right_executionSlot {a b d : ℕ} (U : Assignment (vertices := a + b))
    (hstart : ∀ v, d ≤ U (Fin.natAdd a v)) (t : ℕ) :
    shiftedDone a (executionSlot U (d + t)) = executionSlot (Instance.rightSchedule U d) t := by
  ext n
  rw [mem_shiftedDone]
  by_cases hn : n < b
  · let v : Fin b := ⟨n, hn⟩
    change (Fin.natAdd a v).val ∈ executionSlot U (d + t) ↔
      v.val ∈ executionSlot (Instance.rightSchedule U d) t
    rw [val_mem_executionSlot, val_mem_executionSlot]
    have hh := hstart v
    dsimp only [Instance.rightSchedule]
    omega
  · constructor
    · intro h
      obtain ⟨v, _, hv⟩ := mem_image.mp h
      have hl := v.isLt
      omega
    · intro h
      obtain ⟨v, _, hv⟩ := mem_image.mp h
      have hl := v.isLt
      omega

namespace DeterministicScheduler
variable {m jobs vertices : ℕ} (A : DeterministicScheduler m)

/-- Restricting to an appended instance preserves full revealed-graph
causality, even if old jobs remain unfinished when the new copy starts. -/
theorem continuation_causal (I : Instance jobs vertices) (d : ℕ)
    {jobs₁ jobs₂ vertices₁ vertices₂ : ℕ}
    (J : Instance jobs₁ vertices₁) (K : Instance jobs₂ vertices₂) (t : ℕ)
    (hobs : ∀ u ≤ t,
      J.graphObservation (executionPrefix (Instance.rightSchedule (A.schedule (I.append J d)) d) u) u =
      K.graphObservation (executionPrefix (Instance.rightSchedule (A.schedule (I.append K d)) d) u) u) :
    executionSlot (Instance.rightSchedule (A.schedule (I.append J d)) d) t =
      executionSlot (Instance.rightSchedule (A.schedule (I.append K d)) d) t := by
  let U := A.schedule (I.append J d)
  let V := A.schedule (I.append K d)
  have hU : ∀ v, d ≤ U (Fin.natAdd vertices v) := I.append_right_time J (A.valid _) 
  have hV : ∀ v, d ≤ V (Fin.natAdd vertices v) := I.append_right_time K (A.valid _)
  have hslots : ∀ s ≤ d + t, executionSlot U s = executionSlot V s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro hs
      apply A.causal (I.append J d) (I.append K d) s
      intro u hu
      have hp : executionPrefix U u = executionPrefix V u :=
        executionPrefix_eq_of_slots (fun v hv => ih v (by omega) (by omega))
      change (I.append J d).graphObservation (executionPrefix U u) u =
        (I.append K d).graphObservation (executionPrefix V u) u
      by_cases hud : u < d
      · rw [I.append_graphObservation_before J d u _ hud,
          I.append_graphObservation_before K d u _ hud, hp]
      · have hdu : d ≤ u := by omega
        rw [I.append_graphObservation J d u _ hdu, I.append_graphObservation K d u _ hdu]
        have hnew := hobs (u - d) (by omega)
        change J.graphObservation (executionPrefix (Instance.rightSchedule U d) (u - d)) (u - d) =
          K.graphObservation (executionPrefix (Instance.rightSchedule V d) (u - d)) (u - d) at hnew
        rw [← right_executionPrefix U hU hdu, ← right_executionPrefix V hV hdu] at hnew
        rw [hp] at hnew
        rw [hp, hnew]
  rw [← right_executionSlot U hU t, ← right_executionSlot V hV t]
  rw [hslots (d + t) le_rfl]

noncomputable def continuation (I : Instance jobs vertices) (d : ℕ) : DeterministicScheduler m where
  schedule J := Instance.rightSchedule (A.schedule (I.append J d)) d
  valid J := I.rightSchedule_valid J (A.valid _)
  causal := A.continuation_causal I d

theorem continuation_flow_le (I : Instance jobs vertices) (d : ℕ)
    {jobs₂ vertices₂ : ℕ} (J : Instance jobs₂ vertices₂) :
    J.maxFlow ((A.continuation I d).schedule J) ≤
      (I.append J d).maxFlow (A.schedule (I.append J d)) :=
  I.maxFlow_right_le J (A.valid _)

end DeterministicScheduler
end Scheduling
