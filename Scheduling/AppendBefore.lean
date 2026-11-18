import Scheduling.AppendObservation

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

namespace Instance
variable {jobs₁ jobs₂ vertices₁ vertices₂ : ℕ}

theorem append_revealed_before (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : t < d) {v : Fin (vertices₁ + vertices₂)}
    (hv : v ∈ (I.append J d).revealedVertices done t) :
    ∃ u, v = Fin.castAdd vertices₂ u ∧ u ∈ I.revealedVertices done t := by
  rcases fin_add_cases v with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact ⟨u, rfl, (I.append_revealed_left J d t done u).mp hv⟩
  · exact False.elim (I.append_revealed_right_before J d t done hd u hv)

theorem append_graphObservation_before (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : t < d) :
    (I.append J d).graphObservation done t = I.graphObservation done t := by
  apply GraphObservation.ext_fields
  · change (univ.filter (fun j => (I.append J d).release j ≤ t)).image
      (fun j => (j.val, (I.append J d).release j)) =
      (univ.filter (fun j => I.release j ≤ t)).image (fun j => (j.val, I.release j))
    ext x
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, hx⟩
      rcases fin_add_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨j, by simpa only [append, Fin.addCases_left] using hj,
          by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
      · simp only [append, Fin.addCases_right] at hj
        omega
    · rintro ⟨j, hj, hx⟩
      exact ⟨Fin.castAdd jobs₂ j, by simpa only [append, Fin.addCases_left] using hj,
        by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
  · change ((I.append J d).revealedVertices done t).image _ = (I.revealedVertices done t).image _
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨v, hv, hx⟩
      obtain ⟨u, rfl, hu⟩ := I.append_revealed_before J d t done hd hv
      exact ⟨u, hu, by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
    · rintro ⟨v, hv, hx⟩
      exact ⟨Fin.castAdd vertices₂ v, (I.append_revealed_left J d t done v).mpr hv,
        by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
  · ext x
    simp only [mem_graphObservation_edges]
    constructor
    · rintro ⟨u, v, hu, hv, he, hx⟩
      obtain ⟨u, rfl, hleftU⟩ := I.append_revealed_before J d t done hd hu
      obtain ⟨v, rfl, hleftV⟩ := I.append_revealed_before J d t done hd hv
      exact ⟨u, v, hleftU, hleftV, by simpa only [append, Fin.addCases_left] using he,
        by simpa only [Fin.val_castAdd] using hx⟩
    · rintro ⟨u, v, hu, hv, he, hx⟩
      exact ⟨Fin.castAdd vertices₂ u, Fin.castAdd vertices₂ v,
        (I.append_revealed_left J d t done u).mpr hu,
        (I.append_revealed_left J d t done v).mpr hv,
        by simpa only [append, Fin.addCases_left] using he,
        by simpa only [Fin.val_castAdd] using hx⟩
  · change (((I.append J d).revealedVertices done t).filter (fun v => v.val ∉ done)).image Fin.val =
      ((I.revealedVertices done t).filter (fun v => v.val ∉ done)).image Fin.val
    ext x
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨v, ⟨hv, hn⟩, hx⟩
      obtain ⟨v, rfl, hleft⟩ := I.append_revealed_before J d t done hd hv
      exact ⟨v, ⟨hleft, hn⟩, hx⟩
    · rintro ⟨v, ⟨hv, hn⟩, hx⟩
      exact ⟨Fin.castAdd vertices₂ v, ⟨(I.append_revealed_left J d t done v).mpr hv, hn⟩, hx⟩

end Instance

namespace DeterministicScheduler
variable {m jobs₁ jobs₂ vertices₁ vertices₂ : ℕ} (A : DeterministicScheduler m)

theorem append_slots_before (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {d t : ℕ} (ht : t < d) :
    executionSlot (A.schedule (I.append J d)) t = executionSlot (A.schedule I) t := by
  symm
  apply A.transfer_slots I (I.append J d) (T := t) ?_ t le_rfl
  intro u hu
  exact (I.append_graphObservation_before J d u _ (by omega)).symm

theorem append_time_before (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {d t : ℕ} (ht : t < d) (v : Fin vertices₁) :
    A.schedule (I.append J d) (Fin.castAdd vertices₂ v) = t ↔ A.schedule I v = t := by
  have he := A.append_slots_before I J ht
  have hm : (Fin.castAdd vertices₂ v).val ∈ executionSlot (A.schedule (I.append J d)) t ↔
      v.val ∈ executionSlot (A.schedule I) t := by
    rw [he]
    rfl
  simpa only [val_mem_executionSlot] using hm

/-- A later copy cannot erase a flow lower bound whose deadline falls
before its release. The earlier schedule need not have completed. -/
theorem append_flow_lower (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {d F : ℕ} (hbad : F ≤ I.maxFlow (A.schedule I))
    (hgap : ∀ j, I.release j + F ≤ d) :
    F ≤ (I.append J d).maxFlow (A.schedule (I.append J d)) := by
  let U := A.schedule (I.append J d)
  let B := (I.append J d).maxFlow U
  by_contra hn
  have hBF : B < F := by change ¬ F ≤ B at hn; omega
  have hflow : (I.append J d).FlowBound U B :=
    ((I.append J d).flowBound_iff_maxFlow_le U B).mpr le_rfl
  have hlocal : I.FlowBound (A.schedule I) B := by
    intro v
    have hf := hflow (Fin.castAdd vertices₂ v)
    simp only [Instance.append, Fin.addCases_left] at hf
    have htime : U (Fin.castAdd vertices₂ v) < d := by have := hgap (I.owner v); omega
    have he := (A.append_time_before I J htime v).mp rfl
    rw [he]
    exact hf
  have hh := (I.flowBound_iff_maxFlow_le _ _).mp hlocal
  omega

end DeterministicScheduler
end Scheduling
