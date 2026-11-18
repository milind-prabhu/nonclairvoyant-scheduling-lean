import Scheduling.AppendRestriction

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

theorem GraphObservation.ext_fields {O P : GraphObservation}
    (ha : O.arrivals = P.arrivals) (hv : O.visible = P.visible)
    (he : O.edges = P.edges) (hr : O.ready = P.ready) : O = P := by
  cases O
  cases P
  cases ha
  cases hv
  cases he
  cases hr
  rfl

def GraphObservation.merge (O P : GraphObservation) : GraphObservation where
  arrivals := O.arrivals ∪ P.arrivals
  visible := O.visible ∪ P.visible
  edges := O.edges ∪ P.edges
  ready := O.ready ∪ P.ready

def GraphObservation.shift (O : GraphObservation) (jobs vertices d : ℕ) : GraphObservation where
  arrivals := O.arrivals.image (fun p => (jobs + p.1, d + p.2))
  visible := O.visible.image (fun p => (vertices + p.1, jobs + p.2))
  edges := O.edges.image (fun p => (vertices + p.1, vertices + p.2))
  ready := O.ready.image (fun v => vertices + v)

def shiftedDone (vertices : ℕ) (done : Finset ℕ) : Finset ℕ :=
  (done.filter (vertices ≤ ·)).image (· - vertices)

@[simp] theorem mem_shiftedDone (vertices n : ℕ) (done : Finset ℕ) :
    n ∈ shiftedDone vertices done ↔ vertices + n ∈ done := by
  simp only [shiftedDone, mem_image, mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, hlo⟩, he⟩
    have hh : vertices + n = v := by omega
    rwa [hh]
  · intro h
    exact ⟨vertices + n, ⟨h, by omega⟩, by omega⟩

theorem fin_add_cases {a b : ℕ} (v : Fin (a + b)) :
    (∃ u : Fin a, v = Fin.castAdd b u) ∨ ∃ u : Fin b, v = Fin.natAdd a u := by
  exact Fin.addCases (fun u => Or.inl ⟨u, rfl⟩) (fun u => Or.inr ⟨u, rfl⟩) v

namespace Instance
variable {jobs₁ jobs₂ vertices₁ vertices₂ : ℕ}

theorem append_revealed_left (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (v : Fin vertices₁) :
    Fin.castAdd vertices₂ v ∈ (I.append J d).revealedVertices done t ↔ v ∈ I.revealedVertices done t := by
  constructor
  · intro hv
    obtain ⟨hr, hp⟩ := (mem_filter.mp hv).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · simpa only [append, Fin.addCases_left] using hr
    · intro u hu
      exact hp (Fin.castAdd vertices₂ u) (by simpa only [append, Fin.addCases_left] using hu)
  · intro hv
    obtain ⟨hr, hp⟩ := (mem_filter.mp hv).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · simpa only [append, Fin.addCases_left] using hr
    · intro u
      refine Fin.addCases ?_ ?_ u <;> intro u
      · simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hp u
      · simp only [append, Fin.addCases_right, Fin.addCases_left, false_implies]

theorem append_revealed_right (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : d ≤ t) (v : Fin vertices₂) :
    Fin.natAdd vertices₁ v ∈ (I.append J d).revealedVertices done t ↔
      v ∈ J.revealedVertices (shiftedDone vertices₁ done) (t - d) := by
  constructor
  · intro hv
    obtain ⟨hr, hp⟩ := (mem_filter.mp hv).2
    simp only [append, Fin.addCases_right] at hr
    apply mem_filter.mpr
    refine ⟨mem_univ _, by omega, ?_⟩
    intro u hu
    apply (mem_shiftedDone vertices₁ u.val done).mpr
    exact hp (Fin.natAdd vertices₁ u) (by simpa only [append, Fin.addCases_right] using hu)
  · intro hv
    obtain ⟨hr, hp⟩ := (mem_filter.mp hv).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · simp only [append, Fin.addCases_right]
      omega
    · intro u
      refine Fin.addCases ?_ ?_ u <;> intro u
      · simp only [append, Fin.addCases_left, Fin.addCases_right, false_implies]
      · intro hu
        exact (mem_shiftedDone vertices₁ u.val done).mp
          (hp u (by simpa only [append, Fin.addCases_right] using hu))

theorem append_revealed_right_before (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : t < d) (v : Fin vertices₂) :
    Fin.natAdd vertices₁ v ∉ (I.append J d).revealedVertices done t := by
  intro hv
  have hr := (mem_filter.mp hv).2.1
  simp only [append, Fin.addCases_right] at hr
  omega

theorem append_observation_arrivals (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : d ≤ t) :
    ((I.append J d).graphObservation done t).arrivals =
      (I.graphObservation done t).arrivals ∪
      (J.graphObservation (shiftedDone vertices₁ done) (t - d)).arrivals.image
        (fun p => (jobs₁ + p.1, d + p.2)) := by
  change (univ.filter (fun j => (I.append J d).release j ≤ t)).image
    (fun j => (j.val, (I.append J d).release j)) =
    (univ.filter (fun j => I.release j ≤ t)).image (fun j => (j.val, I.release j)) ∪
      ((univ.filter (fun j => J.release j ≤ t - d)).image (fun j => (j.val, J.release j))).image
        (fun p => (jobs₁ + p.1, d + p.2))
  ext x
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hx⟩
    rcases fin_add_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨j, by simpa only [append, Fin.addCases_left] using hj,
        by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
    · have hr : J.release j ≤ t - d := by
        simp only [append, Fin.addCases_right] at hj
        omega
      exact Or.inr ⟨(j.val, J.release j), ⟨j, hr, rfl⟩,
        by simpa only [append, Fin.addCases_right, Fin.val_natAdd] using hx⟩
  · rintro (⟨j, hj, hx⟩ | ⟨p, ⟨j, hj, hp⟩, hx⟩)
    · exact ⟨Fin.castAdd jobs₂ j, by simpa only [append, Fin.addCases_left] using hj,
        by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
    · subst p
      refine ⟨Fin.natAdd jobs₁ j, ?_, ?_⟩
      · simp only [append, Fin.addCases_right]; omega
      · simpa only [append, Fin.addCases_right, Fin.val_natAdd] using hx

theorem append_observation_visible (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : d ≤ t) :
    ((I.append J d).graphObservation done t).visible =
      (I.graphObservation done t).visible ∪
      (J.graphObservation (shiftedDone vertices₁ done) (t - d)).visible.image
        (fun p => (vertices₁ + p.1, jobs₁ + p.2)) := by
  change ((I.append J d).revealedVertices done t).image _ =
    (I.revealedVertices done t).image _ ∪
      ((J.revealedVertices (shiftedDone vertices₁ done) (t - d)).image _).image _
  ext x
  simp only [mem_union, mem_image]
  constructor
  · rintro ⟨v, hv, hx⟩
    revert hv hx
    refine Fin.addCases ?_ ?_ v <;> intro v hv hx
    · exact Or.inl ⟨v, (I.append_revealed_left J d t done v).mp hv,
        by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
    · exact Or.inr ⟨(v.val, (J.owner v).val), ⟨v, (I.append_revealed_right J d t done hd v).mp hv, rfl⟩,
        by simpa only [append, Fin.addCases_right, Fin.val_natAdd] using hx⟩
  · rintro (⟨v, hv, hx⟩ | ⟨p, ⟨v, hv, hp⟩, hx⟩)
    · exact ⟨Fin.castAdd vertices₂ v, (I.append_revealed_left J d t done v).mpr hv,
        by simpa only [append, Fin.addCases_left, Fin.val_castAdd] using hx⟩
    · subst p
      exact ⟨Fin.natAdd vertices₁ v, (I.append_revealed_right J d t done hd v).mpr hv,
        by simpa only [append, Fin.addCases_right, Fin.val_natAdd] using hx⟩

theorem append_observation_ready (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : d ≤ t) :
    ((I.append J d).graphObservation done t).ready =
      (I.graphObservation done t).ready ∪
      (J.graphObservation (shiftedDone vertices₁ done) (t - d)).ready.image (vertices₁ + ·) := by
  change (((I.append J d).revealedVertices done t).filter (fun v => v.val ∉ done)).image Fin.val =
    ((I.revealedVertices done t).filter (fun v => v.val ∉ done)).image Fin.val ∪
      (((J.revealedVertices (shiftedDone vertices₁ done) (t - d)).filter
        (fun v => v.val ∉ shiftedDone vertices₁ done)).image Fin.val).image (vertices₁ + ·)
  ext x
  simp only [mem_union, mem_image, mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, hn⟩, hx⟩
    revert hx
    revert hn
    revert hv
    refine Fin.addCases ?_ ?_ v <;> intro v hv hn hx
    · exact Or.inl ⟨v, ⟨(I.append_revealed_left J d t done v).mp hv, hn⟩, hx⟩
    · exact Or.inr ⟨v.val, ⟨v, ⟨(I.append_revealed_right J d t done hd v).mp hv,
        by simpa only [mem_shiftedDone, Fin.val_natAdd] using hn⟩, rfl⟩, hx⟩
  · rintro (⟨v, ⟨hv, hn⟩, hx⟩ | ⟨p, ⟨v, ⟨hv, hn⟩, hp⟩, hx⟩)
    · exact ⟨Fin.castAdd vertices₂ v, ⟨(I.append_revealed_left J d t done v).mpr hv, hn⟩, hx⟩
    · subst p
      exact ⟨Fin.natAdd vertices₁ v, ⟨(I.append_revealed_right J d t done hd v).mpr hv,
        by simpa only [mem_shiftedDone, Fin.val_natAdd] using hn⟩, hx⟩

theorem mem_graphObservation_edges {jobs vertices : ℕ} (I : Instance jobs vertices)
    (done : Finset ℕ) (t : ℕ) (x : ℕ × ℕ) :
    x ∈ (I.graphObservation done t).edges ↔
      ∃ u v, u ∈ I.revealedVertices done t ∧ v ∈ I.revealedVertices done t ∧
        I.edge u v ∧ (u.val, v.val) = x := by
  change x ∈ (((I.revealedVertices done t).product (I.revealedVertices done t)).filter
    (fun e => I.edge e.1 e.2)).image (fun e => (e.1.val, e.2.val)) ↔ _
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨huv, he⟩, hx⟩
    exact ⟨u, v, (mem_product.mp huv).1, (mem_product.mp huv).2, he, hx⟩
  · rintro ⟨u, v, hu, hv, he, hx⟩
    exact ⟨(u, v), ⟨mem_product.mpr ⟨hu, hv⟩, he⟩, hx⟩

theorem append_observation_edges (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : d ≤ t) :
    ((I.append J d).graphObservation done t).edges =
      (I.graphObservation done t).edges ∪
      (J.graphObservation (shiftedDone vertices₁ done) (t - d)).edges.image
        (fun p => (vertices₁ + p.1, vertices₁ + p.2)) := by
  ext x
  simp only [mem_union, mem_image, mem_graphObservation_edges]
  constructor
  · rintro ⟨u, v, hu, hv, he, hx⟩
    rcases fin_add_cases u with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
      rcases fin_add_cases v with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨u, v, (I.append_revealed_left J d t done u).mp hu,
        (I.append_revealed_left J d t done v).mp hv,
        by simpa only [append, Fin.addCases_left] using he,
        by simpa only [Fin.val_castAdd] using hx⟩
    · simp only [append, Fin.addCases_left, Fin.addCases_right] at he
    · simp only [append, Fin.addCases_left, Fin.addCases_right] at he
    · exact Or.inr ⟨(u.val, v.val),
        ⟨u, v, (I.append_revealed_right J d t done hd u).mp hu,
          (I.append_revealed_right J d t done hd v).mp hv,
          by simpa only [append, Fin.addCases_right] using he, rfl⟩,
        by simpa only [Fin.val_natAdd] using hx⟩
  · rintro (⟨u, v, hu, hv, he, hx⟩ | ⟨p, ⟨u, v, hu, hv, he, hp⟩, hx⟩)
    · exact ⟨Fin.castAdd vertices₂ u, Fin.castAdd vertices₂ v,
        (I.append_revealed_left J d t done u).mpr hu,
        (I.append_revealed_left J d t done v).mpr hv,
        by simpa only [append, Fin.addCases_left] using he,
        by simpa only [Fin.val_castAdd] using hx⟩
    · subst p
      exact ⟨Fin.natAdd vertices₁ u, Fin.natAdd vertices₁ v,
        (I.append_revealed_right J d t done hd u).mpr hu,
        (I.append_revealed_right J d t done hd v).mpr hv,
        by simpa only [append, Fin.addCases_right] using he,
        by simpa only [Fin.val_natAdd] using hx⟩

theorem append_graphObservation (I : Instance jobs₁ vertices₁) (J : Instance jobs₂ vertices₂)
    (d t : ℕ) (done : Finset ℕ) (hd : d ≤ t) :
    (I.append J d).graphObservation done t =
      (I.graphObservation done t).merge
        ((J.graphObservation (shiftedDone vertices₁ done) (t - d)).shift jobs₁ vertices₁ d) := by
  apply GraphObservation.ext_fields
  · exact I.append_observation_arrivals J d t done hd
  · exact I.append_observation_visible J d t done hd
  · exact I.append_observation_edges J d t done hd
  · exact I.append_observation_ready J d t done hd

end Instance
end Scheduling
