import Scheduling.PhaseInformation
import Scheduling.Renaming

namespace Scheduling
open Finset

/-- Artificially delay releases and express them in a phase-local clock.
The raw ready observation still uses the original public vertex identifiers. -/
def delayObservation (D s t : ℕ) (Q : FIFOObservation) : FIFOObservation :=
  (Q.filter (fun x => (ofLex x).1 + D ≤ t)).image
    (fun x => toLex ((ofLex x).1 + D - s, (ofLex x).2))

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Extend the increasing residual reindexing to a total increasing map on
public labels. Values outside the residual domain are never observed. -/
noncomputable def residualLabel (R : Finset (Fin vertices)) (n : ℕ) : ℕ :=
  if hn : n < R.card then (I.residualVertex R ⟨n, hn⟩).val else vertices + n

theorem residualLabel_strictMono (R : Finset (Fin vertices)) : StrictMono (I.residualLabel R) := by
  intro a b hab
  unfold residualLabel
  split_ifs with ha hb hb
  · exact I.residualVertex_strictMono R hab
  · have hh := (I.residualVertex R ⟨a, ha⟩).isLt
    omega
  · omega
  · omega

@[simp] theorem residualLabel_apply (R : Finset (Fin vertices)) (v : Fin R.card) :
    I.residualLabel R v.val = (I.residualVertex R v).val := by
  simp [residualLabel]

theorem residualVertex_mem (R : Finset (Fin vertices)) (v : Fin R.card) :
    I.residualVertex R v ∈ R := (R.orderIsoOfFin rfl v).property

@[simp] theorem survivorIndex_residualVertex {S : Assignment (vertices := vertices)} {s : ℕ}
    (v : Fin (I.survivors S s).card) :
    I.survivorIndex (I.residualVertex (I.survivors S s) v)
      (I.residualVertex_mem _ v) = v := by
  exact ((I.survivors S s).orderIsoOfFin rfl).symm_apply_apply v

@[simp] theorem splice_residualVertex {S : Assignment (vertices := vertices)} {s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) (v : Fin (I.survivors S s).card) :
    I.splice S s T (I.residualVertex (I.survivors S s) v) = s + T v := by
  simp only [splice, dif_pos (I.residualVertex_mem _ v), I.survivorIndex_residualVertex]

@[simp] theorem phase_release_owner (R : Finset (Fin vertices)) (D s : ℕ) (v : Fin R.card) :
    (I.phaseInstance R D s).release ((I.phaseInstance R D s).owner v) =
      I.release (I.owner (I.residualVertex R v)) + D - s := by
  simp [phaseInstance, rebase, residualInstance]

/-- Local readiness is precisely global readiness of a survivor, together
with its artificial-release eligibility. Removed predecessors have already
finished before the restart. -/
theorem phase_ready_iff {S : Assignment (vertices := vertices)} {D s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card))
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + D)
    (u : ℕ) (v : Fin (I.survivors S s).card) :
    (I.phaseInstance (I.survivors S s) D s).Ready T u v ↔
      I.Ready (I.splice S s T) (s + u) (I.residualVertex (I.survivors S s) v) ∧
        I.release (I.owner (I.residualVertex (I.survivors S s) v)) + D ≤ s + u := by
  classical
  have hstart := hs _ (I.residualVertex_mem _ v)
  constructor
  · rintro ⟨hr, hv, hp⟩
    rw [I.phase_release_owner] at hr
    refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
    · rw [I.splice_residualVertex]
      omega
    · intro w hw
      by_cases hsur : w ∈ I.survivors S s
      · have hedge : (I.phaseInstance (I.survivors S s) D s).edge (I.survivorIndex w hsur) v := by
          simpa only [phaseInstance, rebase, residualInstance, I.residualVertex_survivorIndex] using hw
        have ht := hp _ hedge
        simp only [splice, dif_pos hsur]
        omega
      · have ht : S w < s := by simpa [survivors] using hsur
        rw [I.splice_preserves_prefix T ht]
        omega
  · rintro ⟨⟨_, hv, hp⟩, hr⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [I.phase_release_owner]
      omega
    · rw [I.splice_residualVertex] at hv
      omega
    · intro w hw
      have ht := hp (I.residualVertex (I.survivors S s) w) hw
      rw [I.splice_residualVertex] at ht
      omega

theorem phase_readyObservation {S : Assignment (vertices := vertices)} {D s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card))
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + D)
    [DecidableRel I.edge] [DecidableRel (I.phaseInstance (I.survivors S s) D s).edge]
    (u : ℕ) :
    renameObservation (I.residualLabel (I.survivors S s))
      ((I.phaseInstance (I.survivors S s) D s).readyObservation T u) =
      delayObservation D s (s + u) (I.readyObservation (I.splice S s T) (s + u)) := by
  classical
  let R := I.survivors S s
  let J := I.phaseInstance R D s
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := (J.mem_readyObservation _ _ _).mp hy
    have hg := (I.phase_ready_iff T hs u v).mp hv
    refine mem_image.mpr ⟨I.fifoPriority (I.residualVertex R v), ?_, ?_⟩
    · exact mem_filter.mpr ⟨(I.mem_readyObservation _ _ _).mpr ⟨_, hg.1, rfl⟩, hg.2⟩
    · simp [renameKey, fifoPriority, J, R]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := (I.mem_readyObservation _ _ _).mp (mem_filter.mp hy).1
    have hvtime := hv.2.1
    have hdelay : I.release (I.owner v) + D ≤ s + u := (mem_filter.mp hy).2
    have hsur : v ∈ R := by
      have hh := (I.splice_survives T v).mp (show s ≤ I.splice S s T v by omega)
      exact mem_filter.mpr ⟨mem_univ _, hh⟩
    let w := I.survivorIndex v hsur
    have hw : I.residualVertex (I.survivors S s) w = v := I.residualVertex_survivorIndex v hsur
    have hlocal : J.Ready T u w := (I.phase_ready_iff T hs u w).mpr
      ⟨by simpa only [hw] using hv, by simpa only [hw] using hdelay⟩
    refine mem_image.mpr ⟨J.fifoPriority w, (J.mem_readyObservation _ _ _).mpr ⟨w, hlocal, rfl⟩, ?_⟩
    simp [renameKey, fifoPriority, J, R, hw]


theorem splice_execution_set {S : Assignment (vertices := vertices)} {s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) (u : ℕ) :
    univ.filter (fun v => I.splice S s T v = s + u) =
      (univ.filter (fun v => T v = u)).image (I.residualVertex (I.survivors S s)) := by
  classical
  ext v
  constructor
  · intro hv
    have he := (mem_filter.mp hv).2
    have hsur : v ∈ I.survivors S s :=
      mem_filter.mpr ⟨mem_univ _, (I.splice_survives T v).mp (by omega)⟩
    refine mem_image.mpr ⟨I.survivorIndex v hsur, ?_, I.residualVertex_survivorIndex v hsur⟩
    simp only [splice, dif_pos hsur] at he
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨mem_univ _, by rw [I.splice_residualVertex, (mem_filter.mp hw).2]⟩

theorem splice_execution_public {S : Assignment (vertices := vertices)} {s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) (u : ℕ) :
    (univ.filter (fun v => I.splice S s T v = s + u)).image Fin.val =
      ((univ.filter (fun v => T v = u)).image Fin.val).image (I.residualLabel (I.survivors S s)) := by
  classical
  rw [I.splice_execution_set, image_image, image_image]
  apply image_congr
  intro v _
  exact (I.residualLabel_apply _ v).symm

variable [DecidableRel I.edge]

/-- An SFF phase, after restoring the original identifiers, realizes the
public SFF policy on delayed observations. This includes residual graphs
with fewer vertices and jobs than the original instance. -/
theorem sffPhase_publicPolicy {m B s : ℕ} (hm : 0 < m) (hB : 0 < B)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (u : ℕ) :
    (univ.filter (fun v => I.sffPhase m B hB S s v = s + u)).image Fin.val =
      (sffRawPolicy m B).decision
        (fun a => delayObservation (44 * B ^ 2) s (s + a)
          (I.readyObservation (I.sffPhase m B hB S s) (s + a))) u := by
  classical
  let R := I.survivors S s
  let J := I.phaseInstance R (44 * B ^ 2) s
  let T := J.sffSchedule m B hB
  have hobs : (fun a => renameObservation (I.residualLabel R) (J.readyObservation T a)) =
      fun a => delayObservation (44 * B ^ 2) s (s + a)
        (I.readyObservation (I.sffPhase m B hB S s) (s + a)) := by
    funext a
    exact I.phase_readyObservation T hs a
  change (univ.filter (fun v => I.splice S s T v = s + u)).image Fin.val = _
  rw [I.splice_execution_public]
  have he := J.sffSchedule_publicPolicy hm hB u
  change (univ.filter (fun v => T v = u)).image Fin.val = _ at he
  rw [he, ← sffRawPolicy_decision_rename (I.residualLabel_strictMono R), hobs]

/-- The permanent FIFO phase likewise uses only delayed ready observations
and the original public identifiers. -/
theorem fifoPhase_publicPolicy {m B s : ℕ} (hm : 0 < m)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (u : ℕ) :
    (univ.filter (fun v => I.fifoPhase m hm B S s v = s + u)).image Fin.val =
      fifoPolicy m (delayObservation (44 * B ^ 2) s (s + u)
        (I.readyObservation (I.fifoPhase m hm B S s) (s + u))) := by
  classical
  let R := I.survivors S s
  let J := I.phaseInstance R (44 * B ^ 2) s
  let T := J.fifoSchedule m hm
  change (univ.filter (fun v => I.splice S s T v = s + u)).image Fin.val = _
  rw [I.splice_execution_public]
  have he := J.fifoSchedule_publicPolicy hm u
  change (univ.filter (fun v => T v = u)).image Fin.val = _ at he
  rw [he, ← fifoPolicy_rename (I.residualLabel_strictMono R)]
  congr 1
  exact I.phase_readyObservation T hs u

end Instance
end Scheduling
