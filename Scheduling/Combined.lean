import Scheduling.PhaseFailure

/-! A finite construction of the paper's doubling controller. Each candidate
schedule is run until its first failed deadline; its completed prefix is
preserved when the next phase is spliced in. `fuel` bounds the number of
doublings before switching permanently to FIFO. -/
namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

noncomputable def combinedAux (m : ℕ) (hm : 0 < m) :
    (fuel B : ℕ) → (0 < B) → Assignment (vertices := vertices) → ℕ → Assignment (vertices := vertices)
  | 0, B, _, S, s => I.fifoPhase m hm B S s
  | fuel + 1, B, hB, S, s => by
    classical
    exact if B < m then
      let C := I.sffPhase m B hB S s
      if hf : I.PhaseFails C s B then
        combinedAux m hm fuel (2 * B) (by omega) C (I.failureTime hf)
      else C
    else I.fifoPhase m hm B S s

theorem fifo_final_phase {m B s K : ℕ} (hm : 0 < m)
    {S : Assignment (vertices := vertices)} (hS : I.Valid m S)
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (hprefix : ∀ v, S v < s → S v < I.release (I.owner v) + K)
    (hbudget : 44 * B ^ 2 + 44 * m * I.optimum m hm ≤ K) :
    I.Valid m (I.fifoPhase m hm B S s) ∧ I.FlowBound (I.fifoPhase m hm B S s) K ∧
      ∀ v, S v < s → I.fifoPhase m hm B S s v = S v := by
  classical
  refine ⟨I.fifoPhase_valid hm hS, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ I.survivors S s
    · have hb := I.fifoPhase_survivor_bound hm hs v hv
      omega
    · have hvs : S v < s := by simpa [survivors] using hv
      have he := I.splice_preserves_prefix
        ((I.phaseInstance (I.survivors S s) (44 * B ^ 2) s).fifoSchedule m hm) hvs
      change I.fifoPhase m hm B S s v = S v at he
      rw [he]
      exact hprefix v hvs
  · intro v hv
    exact I.splice_preserves_prefix _ hv

/-- The controller's invariant includes feasibility, the final flow bound,
and preservation of the already executed prefix. No performance property
of a phase is supplied as a hypothesis. -/
theorem combinedAux_spec {m : ℕ} (hm : 0 < m) (fuel B : ℕ) (hB : 0 < B)
    (S : Assignment (vertices := vertices)) (s : ℕ)
    (hfuel : m ≤ 2 ^ fuel * B)
    (hBO : B ≤ 2 * I.optimum m hm) (hBm : B < 2 * m)
    (hS : I.Valid m S)
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (hprefix : ∀ v, S v < s →
      S v < I.release (I.owner v) + 352 * I.optimum m hm * min m (I.optimum m hm)) :
    I.Valid m (I.combinedAux m hm fuel B hB S s) ∧
      I.FlowBound (I.combinedAux m hm fuel B hB S s)
        (352 * I.optimum m hm * min m (I.optimum m hm)) ∧
      ∀ v, S v < s → I.combinedAux m hm fuel B hB S s v = S v := by
  classical
  induction fuel generalizing B S s with
  | zero =>
    have hswitch : m ≤ B := by simpa using hfuel
    exact I.fifo_final_phase hm hS hs hprefix
      (Accounting.combined_fifo_budget hBO hBm hswitch)
  | succ fuel ih =>
    by_cases hswitch : B < m
    · simp only [combinedAux, if_pos hswitch]
      let C := I.sffPhase m B hB S s
      have hC : I.Valid m C := I.sffPhase_valid hm hB hS
      have hstart : ∀ v, s ≤ C v → s ≤ I.release (I.owner v) + 88 * B ^ 2 :=
        I.sffPhase_start_bound hB hs
      have hbudget := Accounting.combined_sff_budget hBO hBm
      have hagree : ∀ v, S v < s → C v = S v := by
        intro v hv
        exact I.splice_preserves_prefix _ hv
      have hold : ∀ v, C v < s →
          C v < I.release (I.owner v) + 352 * I.optimum m hm * min m (I.optimum m hm) := by
        intro v hv
        have hvs : S v < s := by
          have he := I.splice_survives (S := S) (s := s)
            ((I.phaseInstance (I.survivors S s) (44 * B ^ 2) s).sffSchedule m B hB) v
          change (s ≤ C v ↔ s ≤ S v) at he
          omega
        rw [hagree v hvs]
        exact hprefix v hvs
      by_cases hf : I.PhaseFails C s B
      · change I.PhaseFails (I.sffPhase m B hB S s) s B at hf
        rw [dif_pos hf]
        have hsmall := I.failed_guess_lt hm hB hs hf
        have hnextfuel : m ≤ 2 ^ fuel * (2 * B) := by
          simpa [pow_succ, Nat.mul_assoc] using hfuel
        have hnextprefix : ∀ v, C v < I.failureTime hf →
            C v < I.release (I.owner v) + 352 * I.optimum m hm * min m (I.optimum m hm) := by
          intro v hv
          by_cases hvs : C v < s
          · exact hold v hvs
          · have ha := I.failure_completed_age hf hstart v (show s ≤ C v by omega) hv
            change C v < I.release (I.owner v) + 88 * B ^ 2 at ha
            omega
        have hrec := ih (2 * B) (by omega) C (I.failureTime hf) hnextfuel
          (by omega) (by omega) hC (I.doubled_phase_start hB hs hf) hnextprefix
        refine ⟨hrec.1, hrec.2.1, ?_⟩
        intro v hv
        have he := hagree v hv
        have ht := (I.failureTime_spec hf).1
        exact (hrec.2.2 v (by omega)).trans he
      · change ¬ I.PhaseFails (I.sffPhase m B hB S s) s B at hf
        rw [dif_neg hf]
        refine ⟨hC, ?_, hagree⟩
        intro v
        by_cases hvs : C v < s
        · exact hold v hvs
        · have ha := I.no_failure_flow hf hstart v (show s ≤ C v by omega)
          change C v < I.release (I.owner v) + 88 * B ^ 2 at ha
          exact ha.trans_le (Nat.add_le_add_left hbudget _)
    · simp only [combinedAux, if_neg hswitch]
      exact I.fifo_final_phase hm hS hs hprefix
        (Accounting.combined_fifo_budget hBO hBm (by omega))

/-- The initial comparison assignment supplies an empty prefix at time zero;
none of its slots are used by the controller. -/
noncomputable def combinedSchedule (m : ℕ) (hm : 0 < m) : Assignment (vertices := vertices) :=
  I.combinedAux m hm m 1 (by omega) I.serialSchedule 0

theorem combinedSchedule_spec {m : ℕ} (hm : 0 < m) (hj : 0 < jobs) :
    I.Valid m (I.combinedSchedule m hm) ∧
      I.maxFlow (I.combinedSchedule m hm) ≤
        352 * I.optimum m hm * min m (I.optimum m hm) := by
  have hp : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0 < 2 ^ n := by positivity
      rw [pow_succ]
      omega
  have hopt := I.optimum_pos hm hj
  have h := I.combinedAux_spec hm m 1 (by omega) I.serialSchedule 0
    (by simpa using hp m) (by omega) (by omega) (I.serialSchedule_valid hm)
    (by intros; omega) (by intros; omega)
  exact ⟨h.1, (I.flowBound_iff_maxFlow_le _ _).mp h.2.1⟩

end Scheduling.Instance
