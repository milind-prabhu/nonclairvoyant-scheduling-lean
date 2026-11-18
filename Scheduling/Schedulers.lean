import Scheduling.PublicGraph
import Scheduling.PublicCombined
import Scheduling.FIFOLower

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

namespace Instance
variable {jobs vertices otherJobs otherVertices : ℕ}
    (I : Instance jobs vertices) (J : Instance otherJobs otherVertices)

theorem mem_graph_ready (S : Assignment (vertices := vertices)) (t n : ℕ) :
    n ∈ (I.graphObservation (executionPrefix S t) t).ready ↔
      ∃ v, I.Ready S t v ∧ v.val = n := by
  simp only [graphObservation, mem_image, mem_filter, mem_univ, true_and,
    revealedVertices, val_mem_executionPrefix, not_lt, Ready]
  aesop

/-- The frontier interface of the executable algorithms is determined
by the full revealed-graph observation used in the lower bounds. -/
theorem readyObservation_subset_of_graphObservation_eq
    [DecidableRel I.edge] [DecidableRel J.edge]
    (S : Assignment (vertices := vertices)) (T : Assignment (vertices := otherVertices)) (t : ℕ)
    (h : I.graphObservation (executionPrefix S t) t = J.graphObservation (executionPrefix T t) t) :
    I.readyObservation S t ⊆ J.readyObservation T t := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (I.mem_readyObservation S t x).mp hx
  have hr : v.val ∈ (J.graphObservation (executionPrefix T t) t).ready := by
    rw [← h]
    exact (I.mem_graph_ready S t v.val).mpr ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hval⟩ := (J.mem_graph_ready T t v.val).mp hr
  have hvrevealed : v ∈ I.revealedVertices (executionPrefix S t) t := by
    simp only [revealedVertices, mem_filter, mem_univ, true_and, val_mem_executionPrefix]
    exact ⟨hv.1, hv.2.2⟩
  have hvis : (v.val, (I.owner v).val) ∈ (J.graphObservation (executionPrefix T t) t).visible := by
    rw [← h]
    exact mem_image.mpr ⟨v, hvrevealed, rfl⟩
  obtain ⟨z, _, hz⟩ := mem_image.mp hvis
  have hzw : z = w := Fin.ext ((congrArg Prod.fst hz).trans hval.symm)
  subst z
  have howner : (J.owner w).val = (I.owner v).val := congrArg Prod.snd hz
  have ha : ((I.owner v).val, I.release (I.owner v)) ∈
      (J.graphObservation (executionPrefix T t) t).arrivals := by
    rw [← h]
    exact mem_image.mpr ⟨I.owner v, mem_filter.mpr ⟨mem_univ _, hv.1⟩, rfl⟩
  obtain ⟨j, _, hj⟩ := mem_image.mp ha
  have hjw : j = J.owner w := Fin.ext ((congrArg Prod.fst hj).trans howner.symm)
  subst j
  have hrelease : J.release (J.owner w) = I.release (I.owner v) := congrArg Prod.snd hj
  apply (J.mem_readyObservation T t _).mpr
  exact ⟨w, hw, by simp only [fifoPriority, hrelease, hval]⟩

theorem readyObservation_eq_of_graphObservation_eq
    [DecidableRel I.edge] [DecidableRel J.edge]
    (S : Assignment (vertices := vertices)) (T : Assignment (vertices := otherVertices)) (t : ℕ)
    (h : I.graphObservation (executionPrefix S t) t = J.graphObservation (executionPrefix T t) t) :
    I.readyObservation S t = J.readyObservation T t :=
  subset_antisymm (I.readyObservation_subset_of_graphObservation_eq J S T t h)
    (J.readyObservation_subset_of_graphObservation_eq I T S t h.symm)

end Instance

/-- Executable FIFO, packaged in the same causal scheduler model used
by all the quantified lower bounds. -/
noncomputable def fifoScheduler (m : ℕ) (hm : 0 < m) : DeterministicScheduler m where
  schedule I := I.fifoSchedule m hm
  valid I := I.fifoSchedule_valid hm
  causal I J t h := by
    change (univ.filter (fun v => I.fifoSchedule m hm v = t)).image Fin.val =
      (univ.filter (fun v => J.fifoSchedule m hm v = t)).image Fin.val
    rw [I.fifoSchedule_publicPolicy hm, J.fifoSchedule_publicPolicy hm]
    rw [I.readyObservation_eq_of_graphObservation_eq J _ _ t (h t le_rfl)]

/-- The combined upper-bound algorithm, in the shared scheduler model. -/
noncomputable def combinedScheduler (m : ℕ) (hm : 0 < m) : DeterministicScheduler m where
  schedule I := I.combinedSchedule m hm
  valid := by
    intro jobs vertices I
    by_cases hj : 0 < jobs
    · exact (I.combinedSchedule_spec hm hj).1
    · have hzero : jobs = 0 := by omega
      have hv : ∀ v : Fin vertices, False := by intro v; have := (I.owner v).isLt; omega
      refine ⟨fun v => (hv v).elim, fun {u} {_} _ => (hv u).elim, ?_⟩
      intro t
      have he : (univ.filter (fun v => I.combinedSchedule m hm v = t)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v _
        exact hv v
      simp only [he, card_empty, Nat.zero_le]
  causal I J t h := by
    apply I.combinedSchedule_nonclairvoyant J hm
    intro u hu
    exact I.readyObservation_eq_of_graphObservation_eq J _ _ u (h u hu)

theorem fifoScheduler_isFIFO {m : ℕ} (hm : 0 < m) {jobs vertices : ℕ}
    (I : Instance jobs vertices) : I.IsFIFO m ((fifoScheduler m hm).schedule I) :=
  I.fifoSchedule_isFIFO hm

/-- Theorem 2 as a single existence statement about a causal algorithm. -/
theorem exists_optimal_order_scheduler {m : ℕ} (hm : 0 < m) :
    ∃ A : DeterministicScheduler m, ∀ {jobs vertices} (I : Instance jobs vertices),
      I.maxFlow (A.schedule I) ≤ 352 * I.optimum m hm * min m (I.optimum m hm) := by
  refine ⟨combinedScheduler m hm, ?_⟩
  intro jobs vertices I
  by_cases hj : 0 < jobs
  · exact (I.combinedSchedule_spec hm hj).2
  · have hz : jobs = 0 := by omega
    subst jobs
    simp [Instance.maxFlow]

/-- The constant-optimum lower bound applies to the constructed FIFO
algorithm as well as to the abstract class of causal FIFO schedulers. -/
theorem fifoSchedule_constant_optimum_lower {m : ℕ} (hm : 2 ≤ m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) ≤ 6 ∧
      3 * (m - 1) ≤ I.maxFlow (I.fifoSchedule m (by omega)) :=
  fifo_constant_optimum_lower hm (fifoScheduler m (by omega)) (fun I => fifoScheduler_isFIFO (by omega) I)

end Scheduling
