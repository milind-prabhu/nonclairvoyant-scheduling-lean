import Scheduling.PhaseTransport

namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- A phase fails at a deadline if a vertex remains unprocessed there.
Completions are recorded first: a vertex executed at `t - 1` is already
finished at `t`, whereas one assigned slot `t` is still unfinished. -/
def PhaseFails (S : Assignment (vertices := vertices)) (s B : ℕ) : Prop :=
  ∃ t, s ≤ t ∧ ∃ v, t = I.release (I.owner v) + 88 * B ^ 2 ∧ t ≤ S v

noncomputable def failureTime {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : I.PhaseFails S s B) : ℕ := Nat.find hf

theorem failureTime_spec {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : I.PhaseFails S s B) :
    s ≤ I.failureTime hf ∧ ∃ v,
      I.failureTime hf = I.release (I.owner v) + 88 * B ^ 2 ∧ I.failureTime hf ≤ S v :=
  Nat.find_spec hf

theorem failureTime_le {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : I.PhaseFails S s B) (v : Fin vertices)
    (hs : s ≤ I.release (I.owner v) + 88 * B ^ 2)
    (hv : I.release (I.owner v) + 88 * B ^ 2 ≤ S v) :
    I.failureTime hf ≤ I.release (I.owner v) + 88 * B ^ 2 :=
  Nat.find_min' hf ⟨hs, v, rfl, hv⟩

theorem failure_remaining_age {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : I.PhaseFails S s B)
    (hs : ∀ v, s ≤ S v → s ≤ I.release (I.owner v) + 88 * B ^ 2)
    (v : Fin vertices) (hv : I.failureTime hf ≤ S v) :
    I.failureTime hf ≤ I.release (I.owner v) + 88 * B ^ 2 := by
  by_contra hn
  have hstart := hs v ((I.failureTime_spec hf).1.trans hv)
  have hle := I.failureTime_le hf v hstart (by omega)
  omega

theorem failure_completed_age {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : I.PhaseFails S s B)
    (hs : ∀ v, s ≤ S v → s ≤ I.release (I.owner v) + 88 * B ^ 2)
    (v : Fin vertices) (hsv : s ≤ S v) (hv : S v < I.failureTime hf) :
    S v < I.release (I.owner v) + 88 * B ^ 2 := by
  by_contra hn
  have hle := I.failureTime_le hf v (hs v hsv) (by omega)
  omega

theorem no_failure_flow {S : Assignment (vertices := vertices)} {s B : ℕ}
    (hf : ¬ I.PhaseFails S s B)
    (hs : ∀ v, s ≤ S v → s ≤ I.release (I.owner v) + 88 * B ^ 2)
    (v : Fin vertices) (hsv : s ≤ S v) :
    S v < I.release (I.owner v) + 88 * B ^ 2 := by
  by_contra hn
  exact hf ⟨I.release (I.owner v) + 88 * B ^ 2, hs v hsv, v, rfl, by omega⟩

theorem sffPhase_start_bound {m B s : ℕ} (hB : 0 < B)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2) :
    ∀ v, s ≤ I.sffPhase m B hB S s v → s ≤ I.release (I.owner v) + 88 * B ^ 2 := by
  classical
  intro v hv
  have hsur := (I.splice_survives _ v).mp hv
  have h := hs v (mem_filter.mpr ⟨mem_univ _, hsur⟩)
  nlinarith

/-- A failed SFF phase certifies that its guess was too small. -/
theorem failed_guess_lt {m B s : ℕ} (hm : 0 < m) (hB : 0 < B)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (hf : I.PhaseFails (I.sffPhase m B hB S s) s B) : B < I.optimum m hm := by
  classical
  by_contra hn
  obtain ⟨ht, v, he, hv⟩ := I.failureTime_spec hf
  have hsur : v ∈ I.survivors S s :=
    mem_filter.mpr ⟨mem_univ _, (I.splice_survives _ v).mp (ht.trans hv)⟩
  have hbound := I.sffPhase_survivor_bound hm hB hs (by omega) v hsur
  omega

/-- At a restart every survivor's new artificial release is after the new
phase start. This is the invariant needed for local-clock transport. -/
theorem doubled_phase_start {m B s : ℕ} (hB : 0 < B)
    {S : Assignment (vertices := vertices)}
    (hs : ∀ v ∈ I.survivors S s, s ≤ I.release (I.owner v) + 44 * B ^ 2)
    (hf : I.PhaseFails (I.sffPhase m B hB S s) s B) :
    ∀ v ∈ I.survivors (I.sffPhase m B hB S s) (I.failureTime hf),
      I.failureTime hf ≤ I.release (I.owner v) + 44 * (2 * B) ^ 2 := by
  intro v hv
  have h := I.failure_remaining_age hf (I.sffPhase_start_bound hB hs) v (mem_filter.mp hv).2
  nlinarith

end Scheduling.Instance

namespace Scheduling.Accounting

theorem combined_sff_budget {B m O : ℕ} (hO : B ≤ 2 * O) (hm : B < 2 * m) :
    88 * B ^ 2 ≤ 352 * O * min m O := by
  rcases le_total m O with h | h
  · rw [min_eq_left h]
    have hp := Nat.mul_le_mul hO (le_of_lt hm)
    nlinarith
  · rw [min_eq_right h]
    have hp := Nat.mul_le_mul hO hO
    nlinarith

theorem combined_fifo_budget {B m O : ℕ} (hO : B ≤ 2 * O) (hm : B < 2 * m)
    (hswitch : m ≤ B) : 44 * B ^ 2 + 44 * m * O ≤ 352 * O * min m O := by
  rcases le_total m O with h | h
  · rw [min_eq_left h]
    have hp := Nat.mul_le_mul hO (le_of_lt hm)
    nlinarith
  · rw [min_eq_right h]
    have hp := Nat.mul_le_mul hO hO
    have hmo := Nat.mul_le_mul_right O (hswitch.trans hO)
    nlinarith

end Scheduling.Accounting
