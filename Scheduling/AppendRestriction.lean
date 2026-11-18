import Scheduling.AppendInstance

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs₁ jobs₂ vertices₁ vertices₂ m d : ℕ}

def leftSchedule (U : Assignment (vertices := vertices₁ + vertices₂)) : Assignment (vertices := vertices₁) :=
  fun v => U (Fin.castAdd vertices₂ v)

def rightSchedule (U : Assignment (vertices := vertices₁ + vertices₂)) (d : ℕ) : Assignment (vertices := vertices₂) :=
  fun v => U (Fin.natAdd vertices₁ v) - d

theorem append_right_time (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {U : Assignment (vertices := vertices₁ + vertices₂)} (hU : (I.append J d).Valid m U)
    (v : Fin vertices₂) : d ≤ U (Fin.natAdd vertices₁ v) := by
  have hr := hU.release (Fin.natAdd vertices₁ v)
  simp only [append, Fin.addCases_right] at hr
  omega

theorem leftSchedule_valid (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {U : Assignment (vertices := vertices₁ + vertices₂)} (hU : (I.append J d).Valid m U) :
    I.Valid m (leftSchedule U) := by
  constructor
  · intro v
    simpa only [append, Fin.addCases_left, leftSchedule] using hU.release (Fin.castAdd vertices₂ v)
  · intro u v he
    exact hU.precedence (by simpa only [append, Fin.addCases_left] using he)
  · intro t
    have hh := card_le_card_of_injOn (Fin.castAdd vertices₂)
      (s := univ.filter (fun v => leftSchedule U v = t))
      (t := univ.filter (fun v => U v = t))
      (by intro v hv; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩)
      (by
        intro u _ v _ he
        have hh := congrArg (fun v : Fin (vertices₁ + vertices₂) => v.val) he
        exact Fin.ext hh)
    exact hh.trans (hU.capacity t)

theorem rightSchedule_valid (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {U : Assignment (vertices := vertices₁ + vertices₂)} (hU : (I.append J d).Valid m U) :
    J.Valid m (rightSchedule U d) := by
  constructor
  · intro v
    have hr := hU.release (Fin.natAdd vertices₁ v)
    simp only [append, Fin.addCases_right] at hr
    dsimp only [rightSchedule]
    omega
  · intro u v he
    have hp := hU.precedence
      (show (I.append J d).edge (Fin.natAdd vertices₁ u) (Fin.natAdd vertices₁ v) from by
        simpa only [append, Fin.addCases_right] using he)
    have hu := I.append_right_time J hU u
    dsimp only [rightSchedule]
    omega
  · intro t
    have hh := card_le_card_of_injOn (Fin.natAdd vertices₁)
      (s := univ.filter (fun v => rightSchedule U d v = t))
      (t := univ.filter (fun v => U v = d + t))
      (by
        intro v hv
        have ht := (mem_filter.mp hv).2
        have hr := I.append_right_time J hU v
        dsimp only [rightSchedule] at ht
        exact mem_filter.mpr ⟨mem_univ _, by omega⟩)
      (by
        intro u _ v _ he
        apply Fin.ext
        have hh := congrArg Fin.val he
        change vertices₁ + u.val = vertices₁ + v.val at hh
        omega)
    exact hh.trans (hU.capacity (d + t))

theorem leftSchedule_flowBound (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {U : Assignment (vertices := vertices₁ + vertices₂)} {B : ℕ}
    (hflow : (I.append J d).FlowBound U B) : I.FlowBound (leftSchedule U) B := by
  intro v
  simpa only [append, Fin.addCases_left, leftSchedule] using hflow (Fin.castAdd vertices₂ v)

theorem rightSchedule_flowBound (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {U : Assignment (vertices := vertices₁ + vertices₂)} {B : ℕ}
    (hU : (I.append J d).Valid m U) (hflow : (I.append J d).FlowBound U B) :
    J.FlowBound (rightSchedule U d) B := by
  intro v
  have hf := hflow (Fin.natAdd vertices₁ v)
  have hr := I.append_right_time J hU v
  simp only [append, Fin.addCases_right] at hf
  dsimp only [rightSchedule]
  omega

theorem maxFlow_left_le (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (U : Assignment (vertices := vertices₁ + vertices₂)) :
    I.maxFlow (leftSchedule U) ≤ (I.append J d).maxFlow U := by
  apply (I.flowBound_iff_maxFlow_le _ _).mp
  exact I.leftSchedule_flowBound J (((I.append J d).flowBound_iff_maxFlow_le U _).mpr le_rfl)

theorem maxFlow_right_le (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {U : Assignment (vertices := vertices₁ + vertices₂)} (hU : (I.append J d).Valid m U) :
    J.maxFlow (rightSchedule U d) ≤ (I.append J d).maxFlow U := by
  apply (J.flowBound_iff_maxFlow_le _ _).mp
  exact I.rightSchedule_flowBound J hU (((I.append J d).flowBound_iff_maxFlow_le U _).mpr le_rfl)

theorem append_optimum_ge_left (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (hm : 0 < m) (d : ℕ) : I.optimum m hm ≤ (I.append J d).optimum m hm := by
  obtain ⟨U, hU, hf⟩ := (I.append J d).optimum_attained hm
  exact I.optimum_le hm (I.leftSchedule_valid J hU) (I.leftSchedule_flowBound J hf)

theorem append_optimum_ge_right (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (hm : 0 < m) (d : ℕ) : J.optimum m hm ≤ (I.append J d).optimum m hm := by
  obtain ⟨U, hU, hf⟩ := (I.append J d).optimum_attained hm
  exact J.optimum_le hm (I.rightSchedule_valid J hU) (I.rightSchedule_flowBound J hU hf)

theorem append_optimum_le (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (hm : 0 < m) {B d : ℕ} (hI : I.optimum m hm ≤ B) (hJ : J.optimum m hm ≤ B)
    (hgap : ∀ j, I.release j + B ≤ d) : (I.append J d).optimum m hm ≤ B := by
  obtain ⟨S, hS, hfS⟩ := I.optimum_attained hm
  obtain ⟨T, hT, hfT⟩ := J.optimum_attained hm
  obtain ⟨U, hU, hfU⟩ := I.append_offline J
    ⟨S, hS, fun v => (hfS v).trans_le (Nat.add_le_add_left hI _)⟩
    ⟨T, hT, fun v => (hfT v).trans_le (Nat.add_le_add_left hJ _)⟩ hgap
  exact (I.append J d).optimum_le hm hU hfU

theorem append_optimum_eq (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (hm : 0 < m) {B d : ℕ} (hI : I.optimum m hm = B) (hJ : J.optimum m hm ≤ B)
    (hgap : ∀ j, I.release j + B ≤ d) : (I.append J d).optimum m hm = B := by
  apply Nat.le_antisymm (I.append_optimum_le J hm hI.le hJ hgap)
  rw [← hI]
  exact I.append_optimum_ge_left J hm d

theorem append_batched_releases (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {L d : ℕ} (hI : ∀ j, L ∣ I.release j) (hJ : ∀ j, L ∣ J.release j) (hd : L ∣ d) :
    ∀ j, L ∣ (I.append J d).release j := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro j
  · simpa only [append, Fin.addCases_left] using hI j
  · simpa only [append, Fin.addCases_right] using dvd_add hd (hJ j)

theorem append_outForest (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂) (d : ℕ)
    (hI : ∀ u v w, I.edge u w → I.edge v w → u = v)
    (hJ : ∀ u v w, J.edge u w → J.edge v w → u = v) :
    ∀ u v w, (I.append J d).edge u w → (I.append J d).edge v w → u = v := by
  intro u v w
  refine Fin.addCases ?_ ?_ w <;> intro w
  all_goals
    refine Fin.addCases ?_ ?_ u <;> intro u
  all_goals
    refine Fin.addCases ?_ ?_ v <;> intro v
  all_goals simp only [append, Fin.addCases_left, Fin.addCases_right, false_implies, implies_true]
  · intro hu hv
    exact congrArg (Fin.castAdd vertices₂) (hI u v w hu hv)
  · intro hu hv
    exact congrArg (Fin.natAdd vertices₁) (hJ u v w hu hv)

end Scheduling.Instance
