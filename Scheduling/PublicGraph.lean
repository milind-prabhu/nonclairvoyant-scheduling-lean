import Scheduling.Optimum

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

/-- The lower-bound interface gives the algorithm all released job labels,
all revealed vertices with their owners, every edge between revealed vertices,
and the current ready set. Hidden vertices and incident edges are omitted. -/
structure GraphObservation where
  arrivals : Finset (ℕ × ℕ)
  visible : Finset (ℕ × ℕ)
  edges : Finset (ℕ × ℕ)
  ready : Finset ℕ
  deriving DecidableEq

noncomputable def executionPrefix {vertices : ℕ}
    (S : Assignment (vertices := vertices)) (t : ℕ) : Finset ℕ :=
  (univ.filter (fun v => S v < t)).image Fin.val

noncomputable def executionSlot {vertices : ℕ}
    (S : Assignment (vertices := vertices)) (t : ℕ) : Finset ℕ :=
  (univ.filter (fun v => S v = t)).image Fin.val

@[simp] theorem val_mem_executionPrefix {vertices t : ℕ}
    {S : Assignment (vertices := vertices)} (v : Fin vertices) :
    v.val ∈ executionPrefix S t ↔ S v < t := by
  simp only [executionPrefix, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hval⟩
    have : w = v := Fin.ext hval
    subst w
    exact hw
  · intro h; exact ⟨v, h, rfl⟩

@[simp] theorem val_mem_executionSlot {vertices t : ℕ}
    {S : Assignment (vertices := vertices)} (v : Fin vertices) :
    v.val ∈ executionSlot S t ↔ S v = t := by
  simp only [executionSlot, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hval⟩
    have : w = v := Fin.ext hval
    subst w
    exact hw
  · intro h; exact ⟨v, h, rfl⟩

theorem mem_executionPrefix {vertices n t : ℕ} {S : Assignment (vertices := vertices)} :
    n ∈ executionPrefix S t ↔ ∃ u < t, n ∈ executionSlot S u := by
  simp only [executionPrefix, executionSlot, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, hn⟩
    exact ⟨S v, hv, v, rfl, hn⟩
  · rintro ⟨u, hu, v, hv, hn⟩
    exact ⟨v, by omega, hn⟩

theorem executionPrefix_eq_of_slots {vertices otherVertices t : ℕ}
    {S : Assignment (vertices := vertices)} {T : Assignment (vertices := otherVertices)}
    (h : ∀ u < t, executionSlot S u = executionSlot T u) :
    executionPrefix S t = executionPrefix T t := by
  ext n
  simp only [mem_executionPrefix]
  constructor <;> rintro ⟨u, hu, hn⟩
  · exact ⟨u, hu, by rwa [← h u hu]⟩
  · exact ⟨u, hu, by rwa [h u hu]⟩

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

noncomputable def revealedVertices (done : Finset ℕ) (t : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => I.release (I.owner v) ≤ t ∧ ∀ u, I.edge u v → u.val ∈ done)

noncomputable def graphObservation (done : Finset ℕ) (t : ℕ) : GraphObservation where
  arrivals := (univ.filter (fun j => I.release j ≤ t)).image (fun j => (j.val, I.release j))
  visible := (I.revealedVertices done t).image (fun v => (v.val, (I.owner v).val))
  edges := ((I.revealedVertices done t).product (I.revealedVertices done t)).filter
    (fun e => I.edge e.1 e.2) |>.image (fun e => (e.1.val, e.2.val))
  ready := ((I.revealedVertices done t).filter (fun v => v.val ∉ done)).image Fin.val

theorem graphObservation_congr (J : Instance jobs vertices) (done : Finset ℕ) (t : ℕ)
    (ho : I.owner = J.owner) (hr : I.release = J.release)
    (hv : I.revealedVertices done t = J.revealedVertices done t)
    (he : ∀ u ∈ I.revealedVertices done t, ∀ v ∈ I.revealedVertices done t,
      I.edge u v ↔ J.edge u v) : I.graphObservation done t = J.graphObservation done t := by
  have hedges :
      ((I.revealedVertices done t).product (I.revealedVertices done t)).filter (fun e => I.edge e.1 e.2) =
      ((I.revealedVertices done t).product (I.revealedVertices done t)).filter (fun e => J.edge e.1 e.2) := by
    apply filter_congr
    intro e he'
    exact he _ (mem_product.mp he').1 _ (mem_product.mp he').2
  unfold graphObservation
  rw [hedges, ho, hr, hv]

theorem hidden_graphObservation_congr (J : Instance jobs vertices)
    (hidden : Finset (Fin vertices)) (done : Finset ℕ) (t : ℕ)
    (ho : I.owner = J.owner) (hr : I.release = J.release)
    (he : ∀ u v, v ∉ hidden → (I.edge u v ↔ J.edge u v))
    (hI : ∀ v ∈ hidden, ∃ u, I.edge u v ∧ u.val ∉ done)
    (hJ : ∀ v ∈ hidden, ∃ u, J.edge u v ∧ u.val ∉ done) :
    I.graphObservation done t = J.graphObservation done t := by
  have houtside : ∀ v ∈ I.revealedVertices done t, v ∉ hidden := by
    intro v hv hhidden
    obtain ⟨u, hu, hn⟩ := hI v hhidden
    exact hn ((mem_filter.mp hv).2.2 u hu)
  apply I.graphObservation_congr J done t ho hr
  · ext v
    simp only [revealedVertices, mem_filter, mem_univ, true_and]
    by_cases hv : v ∈ hidden
    · obtain ⟨u, hu, hn⟩ := hI v hv
      obtain ⟨w, hw, hm⟩ := hJ v hv
      constructor
      · intro h; exact False.elim (hn (h.2 u hu))
      · intro h; exact False.elim (hm (h.2 w hw))
    · simp only [ho, hr]
      constructor
      · intro h
        exact ⟨h.1, fun u hu => h.2 u ((he u v hv).mpr hu)⟩
      · intro h
        exact ⟨h.1, fun u hu => h.2 u ((he u v hv).mp hu)⟩
  · intro u _ v hv
    exact he u v (houtside v hv)

end Instance

/-- Extensional formulation of a deterministic online scheduler. Total
assignments suffice for lower bounds against algorithms with finite flow.
The causality field uses the full revealed graph, not just ready labels. -/
structure DeterministicScheduler (m : ℕ) where
  schedule : {jobs vertices : ℕ} → Instance jobs vertices → Assignment (vertices := vertices)
  valid : ∀ {jobs vertices} (I : Instance jobs vertices), I.Valid m (schedule I)
  causal : ∀ {jobs vertices otherJobs otherVertices}
    (I : Instance jobs vertices) (J : Instance otherJobs otherVertices) (t : ℕ),
    (∀ u ≤ t, I.graphObservation (executionPrefix (schedule I) u) u =
      J.graphObservation (executionPrefix (schedule J) u) u) →
    executionSlot (schedule I) t = executionSlot (schedule J) t

namespace DeterministicScheduler
variable {m : ℕ} (A : DeterministicScheduler m)

/-- An adaptive replacement can be checked along the old execution alone.
If it changes no observations through `T`, the new instance reproduces
every old decision through `T`. This removes the apparent circularity in
changing hidden edges while preserving a scheduler's past behavior. -/
theorem transfer_slots {jobs vertices otherJobs otherVertices T : ℕ}
    (I : Instance jobs vertices) (J : Instance otherJobs otherVertices)
    (h : ∀ u ≤ T, I.graphObservation (executionPrefix (A.schedule I) u) u =
      J.graphObservation (executionPrefix (A.schedule I) u) u) :
    ∀ t ≤ T, executionSlot (A.schedule I) t = executionSlot (A.schedule J) t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    apply A.causal I J t
    intro u hu
    have hp : executionPrefix (A.schedule I) u = executionPrefix (A.schedule J) u :=
      executionPrefix_eq_of_slots (by
        intro k hk
        exact ih k (by omega) (by omega))
    rw [← hp]
    exact h u (by omega)

theorem transfer_prefix {jobs vertices otherJobs otherVertices T : ℕ}
    (I : Instance jobs vertices) (J : Instance otherJobs otherVertices)
    (h : ∀ u ≤ T, I.graphObservation (executionPrefix (A.schedule I) u) u =
      J.graphObservation (executionPrefix (A.schedule I) u) u) :
    executionPrefix (A.schedule I) (T + 1) = executionPrefix (A.schedule J) (T + 1) :=
  executionPrefix_eq_of_slots (by intro u hu; exact A.transfer_slots I J h u (by omega))

theorem transfer_time {jobs vertices T : ℕ}
    (I J : Instance jobs vertices)
    (h : ∀ u ≤ T, I.graphObservation (executionPrefix (A.schedule I) u) u =
      J.graphObservation (executionPrefix (A.schedule I) u) u)
    (v : Fin vertices) (ht : A.schedule I v ≤ T) : A.schedule J v = A.schedule I v := by
  have he := A.transfer_slots I J h (A.schedule I v) ht
  have hm : v.val ∈ executionSlot (A.schedule I) (A.schedule I v) :=
    mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩
  rw [he] at hm
  obtain ⟨w, hw, hv⟩ := mem_image.mp hm
  have heq : w = v := Fin.ext hv
  subst w
  exact (mem_filter.mp hw).2

theorem hidden_replacement {jobs vertices T : ℕ}
    (I J : Instance jobs vertices) (hidden : Finset (Fin vertices))
    (ho : I.owner = J.owner) (hr : I.release = J.release)
    (he : ∀ u v, v ∉ hidden → (I.edge u v ↔ J.edge u v))
    (hI : ∀ v ∈ hidden, ∃ u, I.edge u v ∧ T ≤ A.schedule I u)
    (hJ : ∀ v ∈ hidden, ∃ u, J.edge u v ∧ T ≤ A.schedule I u) :
    (∀ t ≤ T, executionSlot (A.schedule I) t = executionSlot (A.schedule J) t) ∧
      (∀ v, A.schedule I v ≤ T → A.schedule J v = A.schedule I v) := by
  have hobs : ∀ t ≤ T, I.graphObservation (executionPrefix (A.schedule I) t) t =
      J.graphObservation (executionPrefix (A.schedule I) t) t := by
    intro t ht
    apply I.hidden_graphObservation_congr J hidden _ t ho hr he
    · intro v hv
      obtain ⟨u, hu, htime⟩ := hI v hv
      refine ⟨u, hu, ?_⟩
      simp only [executionPrefix, mem_image, mem_filter, mem_univ, true_and]
      rintro ⟨w, hw, hwu⟩
      have : w = u := Fin.ext hwu
      subst w
      omega
    · intro v hv
      obtain ⟨u, hu, htime⟩ := hJ v hv
      refine ⟨u, hu, ?_⟩
      simp only [executionPrefix, mem_image, mem_filter, mem_univ, true_and]
      rintro ⟨w, hw, hwu⟩
      have : w = u := Fin.ext hwu
      subst w
      omega
  exact ⟨A.transfer_slots I J hobs, A.transfer_time I J hobs⟩

end DeterministicScheduler
end Scheduling
