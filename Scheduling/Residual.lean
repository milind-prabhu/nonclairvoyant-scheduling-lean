import Scheduling.Optimum
import Mathlib.Data.Finset.Sort

/-! Restricting to unfinished vertices and shifting releases preserves offline
feasibility and flow. This is the schedule-transport step in Section 4.3.
No assumption about the completion guarantee of SFF is made here. -/
namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Reindex in the original identifier order, so restricting hidden work
cannot arbitrarily permute the exposed vertices used for tie-breaking. -/
noncomputable def residualVertex (_I : Instance jobs vertices) (R : Finset (Fin vertices)) (v : Fin R.card) : Fin vertices :=
  ((R.orderIsoOfFin rfl) v).val

noncomputable def residualJob (R : Finset (Fin vertices))
    (j : Fin (R.image I.owner).card) : Fin jobs :=
  (((R.image I.owner).orderIsoOfFin rfl) j).val

noncomputable def residualOwner (R : Finset (Fin vertices))
    (v : Fin R.card) : Fin (R.image I.owner).card :=
  ((R.image I.owner).orderIsoOfFin rfl).symm ⟨I.owner (I.residualVertex R v),
    mem_image.mpr ⟨I.residualVertex R v, ((R.orderIsoOfFin rfl) v).property, rfl⟩⟩

theorem residualVertex_injective (R : Finset (Fin vertices)) :
    Function.Injective (I.residualVertex R) := by
  intro u v h
  apply (R.orderIsoOfFin rfl).injective
  exact Subtype.ext h

theorem residualVertex_strictMono (R : Finset (Fin vertices)) :
    StrictMono (I.residualVertex R) := by
  intro u v huv
  exact (R.orderIsoOfFin rfl).strictMono huv

theorem residualJob_injective (R : Finset (Fin vertices)) :
    Function.Injective (I.residualJob R) := by
  intro u v h
  apply ((R.image I.owner).orderIsoOfFin rfl).injective
  exact Subtype.ext h

@[simp] theorem residualJob_owner (R : Finset (Fin vertices)) (v : Fin R.card) :
    I.residualJob R (I.residualOwner R v) = I.owner (I.residualVertex R v) := by
  simp [residualJob, residualOwner]

/-- The induced DAGs on any chosen set of surviving vertices, with all
release times shifted by D. Jobs with no surviving vertex are removed. -/
noncomputable def residualInstance (R : Finset (Fin vertices)) (D : ℕ) :
    Instance (R.image I.owner).card R.card where
  owner := I.residualOwner R
  release := fun j => I.release (I.residualJob R j) + D
  edge := fun u v => I.edge (I.residualVertex R u) (I.residualVertex R v)
  same_job := by
    intro u v he
    apply I.residualJob_injective R
    simpa using I.same_job he
  rank := fun v => I.rank (I.residualVertex R v)
  rank_increases := by intro u v he; exact I.rank_increases he
  nonempty_job := by
    intro j
    have hj : I.residualJob R j ∈ R.image I.owner :=
      (((R.image I.owner).orderIsoOfFin rfl) j).property
    obtain ⟨v, hv, ho⟩ := mem_image.mp hj
    refine ⟨(R.orderIsoOfFin rfl).symm ⟨v, hv⟩, ?_⟩
    apply I.residualJob_injective R
    simpa [residualVertex] using ho

noncomputable def residualSchedule (R : Finset (Fin vertices)) (D : ℕ)
    (O : Assignment (vertices := vertices)) : Assignment (vertices := R.card) :=
  fun v => O (I.residualVertex R v) + D

theorem residualSchedule_valid {m : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (R : Finset (Fin vertices)) (D : ℕ) :
    (I.residualInstance R D).Valid m (I.residualSchedule R D O) := by
  classical
  constructor
  · intro v
    have h := hO.release (I.residualVertex R v)
    simpa [residualInstance, residualSchedule] using Nat.add_le_add_right h D
  · intro u v he
    have h := hO.precedence he
    simpa [residualSchedule] using Nat.add_lt_add_right h D
  · intro t
    let A := univ.filter (fun v => I.residualSchedule R D O v = t)
    have hinj := I.residualVertex_injective R
    have him : (A.image (I.residualVertex R)).card = A.card := card_image_of_injective A hinj
    have hsub : A.image (I.residualVertex R) ⊆ univ.filter (fun v => O v = t - D) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      have ht := (mem_filter.mp hv).2
      dsimp [residualSchedule] at ht
      exact mem_filter.mpr ⟨mem_univ _, by omega⟩
    have hc := (card_le_card hsub).trans (hO.capacity (t - D))
    rw [him] at hc
    exact hc

theorem residualSchedule_flowBound {L : ℕ} {O : Assignment (vertices := vertices)}
    (hL : I.FlowBound O L) (R : Finset (Fin vertices)) (D : ℕ) :
    (I.residualInstance R D).FlowBound (I.residualSchedule R D O) L := by
  intro v
  have h := hL (I.residualVertex R v)
  simpa [residualInstance, residualSchedule, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using Nat.add_lt_add_right h D

/-- The artificial residual instance's optimum is no larger than the original
optimum. The result holds for every vertex restriction and every common shift. -/
theorem residual_optimum_le {m : ℕ} (hm : 0 < m)
    (R : Finset (Fin vertices)) (D : ℕ) :
    (I.residualInstance R D).optimum m hm ≤ I.optimum m hm := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  exact (I.residualInstance R D).optimum_le hm
    (I.residualSchedule_valid hO R D) (I.residualSchedule_flowBound hL R D)

end Scheduling.Instance
