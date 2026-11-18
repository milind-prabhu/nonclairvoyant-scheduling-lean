import Scheduling.PhaseObservations

namespace Scheduling
open Finset

def phaseHistory (B s : ℕ) (history : ℕ → FIFOObservation) (u : ℕ) : FIFOObservation :=
  delayObservation (44 * B ^ 2) s (s + u) (history (s + u))

/-- Only failures observed by the queried time are searched. In particular,
the public controller never tests whether a phase will fail in the future. -/
def publicFailures (B s : ℕ) (history : ℕ → FIFOObservation) (t : ℕ) : Finset ℕ :=
  (Icc s t).filter (fun u => deadlineVisible B u (history u) = true)

def publicCombined (m : ℕ) : ℕ → ℕ → ℕ → (ℕ → FIFOObservation) → ℕ → Finset ℕ
  | 0, B, s, history, t => fifoPolicy m (delayObservation (44 * B ^ 2) s t (history t))
  | fuel + 1, B, s, history, t =>
    if B < m then
      if hf : (publicFailures B s history t).Nonempty then
        publicCombined m fuel (2 * B) ((publicFailures B s history t).min' hf) history t
      else (sffRawPolicy m B).decision (phaseHistory B s history) (t - s)
    else fifoPolicy m (delayObservation (44 * B ^ 2) s t (history t))

theorem publicFailures_congr (B s t : ℕ) (a b : ℕ → FIFOObservation)
    (h : ∀ u ≤ t, a u = b u) : publicFailures B s a t = publicFailures B s b t := by
  apply filter_congr
  intro u hu
  rw [h u (mem_Icc.mp hu).2]

/-- Causality of the public controller, independently of any scheduling
instance: equal observation prefixes give equal decisions. -/
theorem publicCombined_causal (m fuel B s t : ℕ) (hst : s ≤ t)
    (a b : ℕ → FIFOObservation) (h : ∀ u ≤ t, a u = b u) :
    publicCombined m fuel B s a t = publicCombined m fuel B s b t := by
  induction fuel generalizing B s with
  | zero => simp only [publicCombined, h t le_rfl]
  | succ fuel ih =>
    by_cases hswitch : B < m
    · simp only [publicCombined, if_pos hswitch, publicFailures_congr B s t a b h]
      by_cases hf : (publicFailures B s b t).Nonempty
      · simp only [dif_pos hf]
        have ht := (mem_Icc.mp (mem_filter.mp (min'_mem _ hf)).1).2
        exact ih (2 * B) _ ht
      · simp only [dif_neg hf]
        apply (sffRawPolicy m B).decision_eq_of_history_eq
        intro u hu
        have hle : s + u ≤ t := by omega
        simp only [phaseHistory, h (s + u) hle]
    · simp only [publicCombined, if_neg hswitch, h t le_rfl]

theorem publicFailures_empty {B s t : ℕ} {history : ℕ → FIFOObservation}
    (h : ∀ u, s ≤ u → u ≤ t → deadlineVisible B u (history u) = false) :
    publicFailures B s history t = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hh := mem_filter.mp hu
  have ht := mem_Icc.mp hh.1
  have he := h u ht.1 ht.2
  simp [he] at hh

theorem publicFailures_min_eq {B s t f : ℕ} {history : ℕ → FIFOObservation}
    (hs : s ≤ f) (ht : f ≤ t)
    (hvisible : deadlineVisible B f (history f) = true)
    (hbefore : ∀ u, s ≤ u → u < f → deadlineVisible B u (history u) = false)
    (hne : (publicFailures B s history t).Nonempty) :
    (publicFailures B s history t).min' hne = f := by
  have hmem : f ∈ publicFailures B s history t :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨hs, ht⟩, hvisible⟩
  apply le_antisymm (min'_le _ _ hmem)
  by_contra hn
  have hx := mem_filter.mp (min'_mem _ hne)
  have hh := hbefore _ (mem_Icc.mp hx.1).1 (by omega)
  simp [hh] at hx

theorem phaseDecision_congr (m B s t : ℕ) (hst : s ≤ t)
    (a b : ℕ → FIFOObservation) (h : ∀ u ≤ t, a u = b u) :
    (sffRawPolicy m B).decision (phaseHistory B s a) (t - s) =
      (sffRawPolicy m B).decision (phaseHistory B s b) (t - s) := by
  apply (sffRawPolicy m B).decision_eq_of_history_eq
  intro u hu
  have ht : s + u ≤ t := by omega
  simp only [phaseHistory, h (s + u) ht]

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

theorem combinedAux_execution_prefix {m : ℕ} (hm : 0 < m)
    (fuel B : ℕ) (hB : 0 < B) (S : Assignment (vertices := vertices)) (s t : ℕ)
    (ht : t < s) :
    univ.filter (fun v => I.combinedAux m hm fuel B hB S s v = t) =
      univ.filter (fun v => S v = t) := by
  classical
  ext v
  simp only [mem_filter, mem_univ, true_and]
  have h₀ := I.combinedAux_prefix_time hm fuel B hB S s t ht.le v
  have h₁ := I.combinedAux_prefix_time hm fuel B hB S s (t + 1) (by omega) v
  omega

variable [DecidableRel I.edge]

theorem sffPhase_publicPolicy_at {m B s t : ℕ} (hm : 0 < m) (hB : 0 < B)
    {S : Assignment (vertices := vertices)} (hst : s ≤ t)
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2) :
    (univ.filter (fun v => I.sffPhase m B hB S s v = t)).image Fin.val =
      (sffRawPolicy m B).decision (phaseHistory B s (I.readyObservation (I.sffPhase m B hB S s)))
        (t - s) := by
  have h := I.sffPhase_publicPolicy hm hB hs (t - s)
  rw [Nat.add_sub_of_le hst] at h
  exact h

theorem fifoPhase_publicPolicy_at {m B s t : ℕ} (hm : 0 < m)
    {S : Assignment (vertices := vertices)} (hst : s ≤ t)
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2) :
    (univ.filter (fun v => I.fifoPhase m hm B S s v = t)).image Fin.val =
      fifoPolicy m (delayObservation (44 * B ^ 2) s t (I.readyObservation (I.fifoPhase m hm B S s) t)) := by
  have h := I.fifoPhase_publicPolicy hm hs (t - s)
  rw [Nat.add_sub_of_le hst] at h
  exact h

/-- The finite phase construction realizes the causal public-history
controller. This proof uses no optimum or performance bound. -/
theorem combinedAux_publicPolicy {m : ℕ} (hm : 0 < m)
    (fuel B : ℕ) (hB : 0 < B) (S : Assignment (vertices := vertices)) (s t : ℕ)
    (hst : s ≤ t)
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2) :
    (univ.filter (fun v => I.combinedAux m hm fuel B hB S s v = t)).image Fin.val =
      publicCombined m fuel B s (I.readyObservation (I.combinedAux m hm fuel B hB S s)) t := by
  classical
  induction fuel generalizing B S s with
  | zero => exact I.fifoPhase_publicPolicy_at hm hst hs
  | succ fuel ih =>
    by_cases hswitch : B < m
    · simp only [combinedAux, if_pos hswitch]
      by_cases hf : I.PhaseFails (I.sffPhase m B hB S s) s B
      · rw [dif_pos hf]
        let C := I.sffPhase m B hB S s
        let f := I.failureTime hf
        let A := I.combinedAux m hm fuel (2 * B) (by omega) C f
        have hsf : s ≤ f := (I.failureTime_spec hf).1
        have hobs : ∀ u ≤ f, I.readyObservation A u = I.readyObservation C u := by
          intro u hu
          exact I.combinedAux_readyObservation hm fuel (2 * B) (by omega) C f u hu
        have hstart := I.sffPhase_start_bound (m := m) hB hs
        have hbefore : ∀ u, s ≤ u → u < f →
            deadlineVisible B u (I.readyObservation A u) = false := by
          intro u hsu huf
          rw [hobs u huf.le]
          exact I.before_failure_not_visible hf hstart hsu huf
        change (univ.filter (fun v => A v = t)).image Fin.val =
          publicCombined m (fuel + 1) B s (I.readyObservation A) t
        by_cases htf : t < f
        · have he : publicFailures B s (I.readyObservation A) t = ∅ :=
            publicFailures_empty (by intro u hsu hut; exact hbefore u hsu (by omega))
          have hn : ¬ (publicFailures B s (I.readyObservation A) t).Nonempty := by
            rw [he]
            exact Finset.not_nonempty_empty
          rw [publicCombined, if_pos hswitch, dif_neg hn]
          have hexec := I.combinedAux_execution_prefix hm fuel (2 * B) (by omega) C f t htf
          change univ.filter (fun v => A v = t) = univ.filter (fun v => C v = t) at hexec
          rw [hexec]
          exact (I.sffPhase_publicPolicy_at hm hB hst hs).trans
            (phaseDecision_congr m B s t hst _ _ (by intro u hu; exact (hobs u (by omega)).symm))
        · have hft : f ≤ t := by omega
          have hv : deadlineVisible B f (I.readyObservation A f) = true := by
            rw [hobs f le_rfl]
            exact I.failureTime_visible hf
          have hne : (publicFailures B s (I.readyObservation A) t).Nonempty :=
            ⟨f, mem_filter.mpr ⟨mem_Icc.mpr ⟨hsf, hft⟩, hv⟩⟩
          rw [publicCombined, if_pos hswitch, dif_pos hne,
            publicFailures_min_eq hsf hft hv hbefore hne]
          exact ih (2 * B) (by omega) C f hft (I.doubled_phase_start hB hs hf)
      · rw [dif_neg hf]
        have hstart := I.sffPhase_start_bound (m := m) hB hs
        have he : publicFailures B s (I.readyObservation (I.sffPhase m B hB S s)) t = ∅ :=
          publicFailures_empty (by intro u hsu _; exact I.no_failure_not_visible hf hstart hsu)
        have hn : ¬ (publicFailures B s (I.readyObservation (I.sffPhase m B hB S s)) t).Nonempty := by
          rw [he]
          exact Finset.not_nonempty_empty
        rw [publicCombined, if_pos hswitch, dif_neg hn]
        exact I.sffPhase_publicPolicy_at hm hB hst hs
    · simp only [combinedAux, if_neg hswitch, publicCombined]
      exact I.fifoPhase_publicPolicy_at hm hst hs

theorem combinedSchedule_publicPolicy {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (univ.filter (fun v => I.combinedSchedule m hm v = t)).image Fin.val =
      publicCombined m m 1 0 (I.readyObservation (I.combinedSchedule m hm)) t :=
  I.combinedAux_publicPolicy hm m 1 (by omega) I.serialSchedule 0 t (by omega) (by intros; omega)

/-- Full cross-instance non-clairvoyance of the combined scheduler. Its
guesses, restarts, and execution decisions require only observed history. -/
theorem combinedSchedule_nonclairvoyant {otherJobs otherVertices m : ℕ}
    (J : Instance otherJobs otherVertices) [DecidableRel J.edge]
    (hm : 0 < m) (t : ℕ)
    (h : ∀ u ≤ t, I.readyObservation (I.combinedSchedule m hm) u =
      J.readyObservation (J.combinedSchedule m hm) u) :
    (univ.filter (fun v => I.combinedSchedule m hm v = t)).image Fin.val =
      (univ.filter (fun v => J.combinedSchedule m hm v = t)).image Fin.val := by
  rw [I.combinedSchedule_publicPolicy hm, J.combinedSchedule_publicPolicy hm]
  exact publicCombined_causal m m 1 0 t (by omega) _ _ h

end Instance
end Scheduling
