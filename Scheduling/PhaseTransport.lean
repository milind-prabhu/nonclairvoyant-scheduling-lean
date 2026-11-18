import Scheduling.Residual
import Scheduling.SFFConstruction
import Scheduling.FIFOConstruction

/-! The restart operation in Section 4.3: translate the surviving instance
to the new phase's clock, and join its schedule to the completed prefix. -/
namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Rebase an instance to a clock whose zero is global time `s`. The
feasibility theorem requires that every release is at or after `s`. -/
def rebase (s : ℕ) : Instance jobs vertices :=
  { I with release := fun j => I.release j - s }

def rebaseSchedule (_I : Instance jobs vertices) (O : Assignment (vertices := vertices)) (s : ℕ) :
    Assignment (vertices := vertices) := fun v => O v - s

theorem rebaseSchedule_valid {m s : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hs : ∀ j, s ≤ I.release j) :
    (I.rebase s).Valid m (I.rebaseSchedule O s) := by
  classical
  constructor
  · intro v
    exact Nat.sub_le_sub_right (hO.release v) s
  · intro u v he
    have hp := hO.precedence he
    have hu := (hs (I.owner u)).trans (hO.release u)
    change O u - s < O v - s
    omega
  · intro t
    have hsub : univ.filter (fun v => I.rebaseSchedule O s v = t) ⊆
        univ.filter (fun v => O v = t + s) := by
      intro v hv
      have he := (mem_filter.mp hv).2
      have hl := (hs (I.owner v)).trans (hO.release v)
      dsimp [rebaseSchedule] at he
      exact mem_filter.mpr ⟨mem_univ _, by omega⟩
    exact (card_le_card hsub).trans (hO.capacity _)

theorem rebaseSchedule_flowBound {m L s : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) (hs : ∀ j, s ≤ I.release j) :
    (I.rebase s).FlowBound (I.rebaseSchedule O s) L := by
  intro v
  have h := hL v
  have ho := hO.release v
  have hr := hs (I.owner v)
  change O v - s < I.release (I.owner v) - s + L
  omega

/-- The phase instance retains exactly `R`, delays releases by `D`, then
sets its clock to zero at global time `s`. -/
noncomputable def phaseInstance (R : Finset (Fin vertices)) (D s : ℕ) :
    Instance (R.image I.owner).card R.card := (I.residualInstance R D).rebase s

theorem phase_releases_after_start {R : Finset (Fin vertices)} {D s : ℕ}
    (hs : ∀ v ∈ R, s ≤ I.release (I.owner v) + D) :
    ∀ j, s ≤ (I.residualInstance R D).release j := by
  intro j
  obtain ⟨v, hv⟩ := (I.residualInstance R D).nonempty_job j
  have h := hs (I.residualVertex R v) ((R.orderIsoOfFin rfl) v).property
  have he : I.residualJob R j = I.owner (I.residualVertex R v) := by
    rw [← hv]
    exact I.residualJob_owner R v
  simpa [residualInstance, he] using h

theorem phase_offline_bound {m L : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L)
    (R : Finset (Fin vertices)) (D s : ℕ)
    (hs : ∀ v ∈ R, s ≤ I.release (I.owner v) + D) :
    ∃ T, (I.phaseInstance R D s).Valid m T ∧ (I.phaseInstance R D s).FlowBound T L := by
  let J := I.residualInstance R D
  refine ⟨J.rebaseSchedule (I.residualSchedule R D O) s, ?_, ?_⟩
  · exact J.rebaseSchedule_valid (I.residualSchedule_valid hO R D)
      (I.phase_releases_after_start hs)
  · exact J.rebaseSchedule_flowBound (I.residualSchedule_valid hO R D)
      (I.residualSchedule_flowBound hL R D)
      (I.phase_releases_after_start hs)

theorem phase_optimum_le {m : ℕ} (hm : 0 < m)
    (R : Finset (Fin vertices)) (D s : ℕ)
    (hs : ∀ v ∈ R, s ≤ I.release (I.owner v) + D) :
    (I.phaseInstance R D s).optimum m hm ≤ I.optimum m hm := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  obtain ⟨T, hT, hTL⟩ := I.phase_offline_bound hO hL R D s hs
  exact (I.phaseInstance R D s).optimum_le hm hT hTL

/-- Vertices not yet executed at the start, including future arrivals. -/
noncomputable def survivors (_I : Instance jobs vertices) (S : Assignment (vertices := vertices)) (s : ℕ) :
    Finset (Fin vertices) := univ.filter (fun v => s ≤ S v)

noncomputable def survivorIndex {S : Assignment (vertices := vertices)} {s : ℕ}
    (v : Fin vertices) (hv : v ∈ I.survivors S s) : Fin (I.survivors S s).card :=
  ((I.survivors S s).orderIsoOfFin rfl).symm ⟨v, hv⟩

@[simp] theorem residualVertex_survivorIndex {S : Assignment (vertices := vertices)} {s : ℕ}
    (v : Fin vertices) (hv : v ∈ I.survivors S s) :
    I.residualVertex (I.survivors S s) (I.survivorIndex v hv) = v := by
  simp [residualVertex, survivorIndex]

/-- Keep the executed prefix and use a phase-local schedule for every
survivor. This operation does not reschedule any completed vertex. -/
noncomputable def splice (S : Assignment (vertices := vertices)) (s : ℕ)
    (T : Assignment (vertices := (I.survivors S s).card)) : Assignment (vertices := vertices) :=
  fun v => if hv : v ∈ I.survivors S s then s + T (I.survivorIndex v hv) else S v

theorem splice_valid {m D s : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (T : Assignment (vertices := (I.survivors S s).card))
    (hT : (I.phaseInstance (I.survivors S s) D s).Valid m T) :
    I.Valid m (I.splice S s T) := by
  classical
  constructor
  · intro v
    by_cases hv : v ∈ I.survivors S s
    · have hr := hT.release (I.survivorIndex v hv)
      simp only [phaseInstance, rebase, residualInstance, residualJob_owner,
        I.residualVertex_survivorIndex] at hr
      simp only [splice, dif_pos hv]
      omega
    · simpa only [splice, dif_neg hv] using hS.release v
  · intro u v he
    by_cases hu : u ∈ I.survivors S s
    · have hv : v ∈ I.survivors S s := by
        have hh := (mem_filter.mp hu).2
        have hp := hS.precedence he
        exact mem_filter.mpr ⟨mem_univ _, by omega⟩
      have hedge : (I.phaseInstance (I.survivors S s) D s).edge
          (I.survivorIndex u hu) (I.survivorIndex v hv) := by
        simpa [phaseInstance, rebase, residualInstance] using he
      have hp := hT.precedence hedge
      simpa only [splice, dif_pos hu, dif_pos hv, Nat.add_lt_add_iff_left] using hp
    · have hus : S u < s := by
        simpa [survivors] using hu
      by_cases hv : v ∈ I.survivors S s
      · simp only [splice, dif_neg hu, dif_pos hv]
        omega
      · simpa only [splice, dif_neg hu, dif_neg hv] using hS.precedence he
  · intro t
    by_cases ht : t < s
    · apply (card_le_card (t := univ.filter (fun v => S v = t)) ?_).trans (hS.capacity t)
      intro v hv
      have he := (mem_filter.mp hv).2
      by_cases hsur : v ∈ I.survivors S s
      · simp only [splice, dif_pos hsur] at he
        omega
      · exact mem_filter.mpr ⟨mem_univ _, by simpa only [splice, dif_neg hsur] using he⟩
    · let A := univ.filter (fun v => T v = t - s)
      have hsub : univ.filter (fun v => I.splice S s T v = t) ⊆
          A.image (I.residualVertex (I.survivors S s)) := by
        intro v hv
        have he := (mem_filter.mp hv).2
        have hsur : v ∈ I.survivors S s := by
          by_contra hn
          simp only [splice, dif_neg hn] at he
          have hlt : S v < s := by simpa [survivors] using hn
          omega
        refine mem_image.mpr ⟨I.survivorIndex v hsur, ?_, I.residualVertex_survivorIndex v hsur⟩
        simp only [splice, dif_pos hsur] at he
        exact mem_filter.mpr ⟨mem_univ _, by omega⟩
      exact (card_le_card hsub).trans (card_image_le.trans (hT.capacity (t - s)))


/-- A phase's local flow bound gives a global bound for its survivors. -/
theorem splice_survivor_bound {D s K : ℕ} {S : Assignment (vertices := vertices)}
    {T : Assignment (vertices := (I.survivors S s).card)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + D)
    (hT : (I.phaseInstance (I.survivors S s) D s).FlowBound T K)
    (v : Fin vertices) (hv : v ∈ I.survivors S s) :
    I.splice S s T v < I.release (I.owner v) + D + K := by
  have ht := hT (I.survivorIndex v hv)
  simp only [phaseInstance, rebase, residualInstance, residualJob_owner,
    I.residualVertex_survivorIndex] at ht
  have hr := hs v hv
  simp only [splice, dif_pos hv]
  omega

theorem splice_preserves_prefix {S : Assignment (vertices := vertices)} {s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) {v : Fin vertices}
    (hv : S v < s) : I.splice S s T v = S v := by
  have hn : v ∉ I.survivors S s := by simpa [survivors] using hv
  simp only [splice, dif_neg hn]

theorem splice_survives {S : Assignment (vertices := vertices)} {s : ℕ}
    (T : Assignment (vertices := (I.survivors S s).card)) (v : Fin vertices) :
    s ≤ I.splice S s T v ↔ s ≤ S v := by
  classical
  by_cases hv : v ∈ I.survivors S s
  · have hs := (mem_filter.mp hv).2
    simp only [splice, dif_pos hv]
    omega
  · simp only [splice, dif_neg hv]

/-- A fresh SFF phase with artificial delay `44 B²`, expressed as a global
assignment by splicing its local run into the completed prefix. -/
noncomputable def sffPhase (m B : ℕ) (hB : 0 < B)
    (S : Assignment (vertices := vertices)) (s : ℕ) : Assignment (vertices := vertices) := by
  classical
  exact I.splice S s ((I.phaseInstance (I.survivors S s) (44 * B ^ 2) s).sffSchedule m B hB)

noncomputable def fifoPhase (m : ℕ) (hm : 0 < m) (B : ℕ)
    (S : Assignment (vertices := vertices)) (s : ℕ) : Assignment (vertices := vertices) := by
  classical
  exact I.splice S s ((I.phaseInstance (I.survivors S s) (44 * B ^ 2) s).fifoSchedule m hm)

theorem sffPhase_valid {m B s : ℕ} (hm : 0 < m) (hB : 0 < B)
    {S : Assignment (vertices := vertices)} (hS : I.Valid m S) :
    I.Valid m (I.sffPhase m B hB S s) := by
  classical
  exact I.splice_valid hS _ ((I.phaseInstance _ _ _).sffSchedule_valid hm hB)

theorem fifoPhase_valid {m B s : ℕ} (hm : 0 < m)
    {S : Assignment (vertices := vertices)} (hS : I.Valid m S) :
    I.Valid m (I.fifoPhase m hm B S s) := by
  classical
  exact I.splice_valid hS _ ((I.phaseInstance _ _ _).fifoSchedule_valid hm)

theorem sffPhase_survivor_bound {m B s : ℕ} (hm : 0 < m) (hB : 0 < B)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (hguess : I.optimum m hm ≤ B) (v : Fin vertices) (hv : v ∈ I.survivors S s) :
    I.sffPhase m B hB S s v < I.release (I.owner v) + 88 * B ^ 2 := by
  classical
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  obtain ⟨T, hT, hTL⟩ := I.phase_offline_bound hO hL (I.survivors S s) (44 * B ^ 2) s hs
  have hTB : (I.phaseInstance (I.survivors S s) (44 * B ^ 2) s).FlowBound T B := by
    intro w; exact (hTL w).trans_le (Nat.add_le_add_left hguess _)
  have hb := (I.phaseInstance _ _ _).sffSchedule_bound hm hB hT hTB
  have hf := ((I.phaseInstance _ _ _).flowBound_iff_maxFlow_le _ _).mpr hb
  have hg := I.splice_survivor_bound hs hf v hv
  change I.sffPhase m B hB S s v < _ at hg
  nlinarith

theorem fifoPhase_survivor_bound {m B s : ℕ} (hm : 0 < m)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (v : Fin vertices) (hv : v ∈ I.survivors S s) :
    I.fifoPhase m hm B S s v <
      I.release (I.owner v) + 44 * B ^ 2 + 44 * m * I.optimum m hm := by
  classical
  let J := I.phaseInstance (I.survivors S s) (44 * B ^ 2) s
  have ho := I.phase_optimum_le hm (I.survivors S s) (44 * B ^ 2) s hs
  change J.optimum m hm ≤ I.optimum m hm at ho
  have hb := J.fifoSchedule_competitive hm
  have hflow : J.maxFlow (J.fifoSchedule m hm) ≤ 44 * m * I.optimum m hm := by
    have hc : m * m + m - 1 ≤ 44 * m * m := by
      have hsq := Nat.mul_le_mul_left m (show 1 ≤ m by omega)
      have hsub := Nat.sub_le (m * m + m) 1
      nlinarith
    have hcomp := Nat.mul_le_mul hc ho
    nlinarith
  exact I.splice_survivor_bound hs ((J.flowBound_iff_maxFlow_le _ _).mpr hflow) v hv

end Scheduling.Instance
