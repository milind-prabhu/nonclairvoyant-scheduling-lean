import Scheduling.HardFamilies
import Mathlib.Algebra.BigOperators.Fin

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs₁ jobs₂ vertices₁ vertices₂ : ℕ}

/-- Disjoint union of two instances, delaying the second instance by
`d` slots and giving its jobs and vertices fresh labels. -/
def append (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂) (d : ℕ) :
    Instance (jobs₁ + jobs₂) (vertices₁ + vertices₂) where
  owner := Fin.addCases (fun v => Fin.castAdd jobs₂ (I.owner v)) (fun v => Fin.natAdd jobs₁ (J.owner v))
  release := Fin.addCases I.release (fun j => d + J.release j)
  edge u v := Fin.addCases
    (fun u => Fin.addCases (fun v => I.edge u v) (fun _ => False) v)
    (fun u => Fin.addCases (fun _ => False) (fun v => J.edge u v) v) u
  same_job := by
    intro u v
    refine Fin.addCases ?_ ?_ u <;> intro u
    · refine Fin.addCases ?_ ?_ v <;> intro v <;> simp only [Fin.addCases_left, Fin.addCases_right]
      · intro h; exact congrArg (Fin.castAdd jobs₂) (I.same_job h)
      · simp
    · refine Fin.addCases ?_ ?_ v <;> intro v <;> simp only [Fin.addCases_left, Fin.addCases_right]
      · simp
      · intro h; exact congrArg (Fin.natAdd jobs₁) (J.same_job h)
  rank := Fin.addCases I.rank J.rank
  rank_increases := by
    intro u v
    refine Fin.addCases ?_ ?_ u <;> intro u
    · refine Fin.addCases ?_ ?_ v <;> intro v <;> simp only [Fin.addCases_left, Fin.addCases_right]
      · exact I.rank_increases
      · simp
    · refine Fin.addCases ?_ ?_ v <;> intro v <;> simp only [Fin.addCases_left, Fin.addCases_right]
      · simp
      · exact J.rank_increases
  nonempty_job := by
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro j
    · obtain ⟨v, hv⟩ := I.nonempty_job j
      exact ⟨Fin.castAdd vertices₂ v, by simp only [Fin.addCases_left, hv]⟩
    · obtain ⟨v, hv⟩ := J.nonempty_job j
      exact ⟨Fin.natAdd vertices₁ v, by simp only [Fin.addCases_right, hv]⟩

def appendSchedule (S : Assignment (vertices := vertices₁))
    (T : Assignment (vertices := vertices₂)) (d : ℕ) : Assignment (vertices := vertices₁ + vertices₂) :=
  Fin.addCases S (fun v => d + T v)

@[simp] theorem appendSchedule_left (S : Assignment (vertices := vertices₁))
    (T : Assignment (vertices := vertices₂)) (d : ℕ) (v : Fin vertices₁) :
    appendSchedule S T d (Fin.castAdd vertices₂ v) = S v := by
  simp only [appendSchedule, Fin.addCases_left]

@[simp] theorem appendSchedule_right (S : Assignment (vertices := vertices₁))
    (T : Assignment (vertices := vertices₂)) (d : ℕ) (v : Fin vertices₂) :
    appendSchedule S T d (Fin.natAdd vertices₁ v) = d + T v := by
  simp only [appendSchedule, Fin.addCases_right]

theorem appendSchedule_slot_card (S : Assignment (vertices := vertices₁))
    (T : Assignment (vertices := vertices₂)) (d t : ℕ) :
    (univ.filter (fun v => appendSchedule S T d v = t)).card =
      (univ.filter (fun v => S v = t)).card + (univ.filter (fun v => d + T v = t)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [Fin.sum_univ_add]
  simp only [appendSchedule_left, appendSchedule_right]

theorem append_valid (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {m d : ℕ} {S : Assignment (vertices := vertices₁)} {T : Assignment (vertices := vertices₂)}
    (hS : I.Valid m S) (hT : J.Valid m T) (hfinish : ∀ v, S v < d) :
    (I.append J d).Valid m (appendSchedule S T d) := by
  constructor
  · intro v
    refine Fin.addCases ?_ ?_ v <;> intro v
    · simpa only [append, Fin.addCases_left, appendSchedule_left] using hS.release v
    · simpa only [append, Fin.addCases_right, appendSchedule_right] using Nat.add_le_add_left (hT.release v) d
  · intro u v
    refine Fin.addCases ?_ ?_ u <;> intro u
    · refine Fin.addCases ?_ ?_ v <;> intro v <;>
        simp only [append, Fin.addCases_left, Fin.addCases_right, appendSchedule_left, appendSchedule_right]
      · exact hS.precedence
      · simp
    · refine Fin.addCases ?_ ?_ v <;> intro v <;>
        simp only [append, Fin.addCases_left, Fin.addCases_right, appendSchedule_left, appendSchedule_right]
      · simp
      · intro h; exact Nat.add_lt_add_left (hT.precedence h) d
  · intro t
    rw [appendSchedule_slot_card]
    by_cases ht : t < d
    · have hz : (univ.filter (fun v => d + T v = t)).card = 0 := by
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hh := (mem_filter.mp hv).2
        omega
      rw [hz, Nat.add_zero]
      exact hS.capacity t
    · have hz : (univ.filter (fun v => S v = t)).card = 0 := by
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hh := (mem_filter.mp hv).2
        have hf := hfinish v
        omega
      have he : univ.filter (fun v => d + T v = t) = univ.filter (fun v => T v = t - d) := by
        ext v
        simp only [mem_filter, mem_univ, true_and]
        omega
      rw [hz, Nat.zero_add, he]
      exact hT.capacity (t - d)

theorem append_flowBound (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {d B : ℕ} {S : Assignment (vertices := vertices₁)} {T : Assignment (vertices := vertices₂)}
    (hS : I.FlowBound S B) (hT : J.FlowBound T B) :
    (I.append J d).FlowBound (appendSchedule S T d) B := by
  intro v
  refine Fin.addCases ?_ ?_ v <;> intro v
  · simpa only [append, Fin.addCases_left, appendSchedule_left] using hS v
  · simpa only [append, Fin.addCases_right, appendSchedule_right, Nat.add_assoc] using
      Nat.add_lt_add_left (hT v) d

theorem append_offline (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    {m B d : ℕ} (hI : ∃ S, I.Valid m S ∧ I.FlowBound S B)
    (hJ : ∃ T, J.Valid m T ∧ J.FlowBound T B)
    (hgap : ∀ j, I.release j + B ≤ d) :
    ∃ U, (I.append J d).Valid m U ∧ (I.append J d).FlowBound U B := by
  obtain ⟨S, hS, hfS⟩ := hI
  obtain ⟨T, hT, hfT⟩ := hJ
  exact ⟨appendSchedule S T d, I.append_valid J hS hT (fun v => (hfS v).trans_le (hgap _)),
    I.append_flowBound J hfS hfT⟩

end Scheduling.Instance
