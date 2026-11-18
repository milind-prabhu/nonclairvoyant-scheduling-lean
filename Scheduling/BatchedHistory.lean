import Scheduling.BatchedAdversaryOffline

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

def PastAgreement {vertices : ℕ} (S T : Assignment (vertices := vertices)) (t : ℕ) : Prop :=
  ∀ u < t, ∀ v, S v = u ↔ T v = u

theorem pastAgreement_of_slots {vertices t : ℕ} {S T : Assignment (vertices := vertices)}
    (h : ∀ u < t, executionSlot S u = executionSlot T u) : PastAgreement S T t := by
  intro u hu v
  have he := h u hu
  simpa only [val_mem_executionSlot] using
    (show v.val ∈ executionSlot S u ↔ v.val ∈ executionSlot T u from by rw [he])

namespace PastAgreement
variable {vertices t : ℕ} {S T : Assignment (vertices := vertices)}

theorem time_eq (h : PastAgreement S T t) (v : Fin vertices) (hv : S v < t) : T v = S v :=
  (h _ hv v).mp rfl

theorem symm (h : PastAgreement S T t) : PastAgreement T S t := fun u hu v => (h u hu v).symm

theorem interval (h : PastAgreement S T t) (a : ℕ) (v : Fin vertices) :
    (a ≤ S v ∧ S v < t) ↔ (a ≤ T v ∧ T v < t) := by
  constructor
  · intro hv
    rw [h.time_eq v hv.2]
    exact hv
  · intro hv
    rw [h.symm.time_eq v hv.2]
    exact hv

theorem slot_card (h : PastAgreement S T t) (u : ℕ) (hu : u < t) :
    (univ.filter (fun v => S v = u)).card = (univ.filter (fun v => T v = u)).card := by
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  exact h u hu v

end PastAgreement

namespace LayeredPrefix
variable {jobs work m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}

theorem HistoryRun.past_agreement {rule : HistoryLayerRule jobs work}
    {history records : List (LayerRecord jobs work)} {P Q : LayeredPrefix jobs work}
    (h : HistoryRun hw A L rule history P Q records) (t : ℕ)
    (hbefore : ∀ i, P.closed i < work → t ≤ P.finishTime (L := L) hw A i) :
    PastAgreement (A.schedule (P.toInstance L hw)) (A.schedule (Q.toInstance L hw)) (t + 1) := by
  obtain ⟨staticRule, hr⟩ := h.flexible.recorded
  exact pastAgreement_of_slots (fun u hu => hr.completion.preserves_slots t hbefore u (by omega))

theorem RecordedRun.start_width {rule : LayerSizeRule jobs work}
    {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ r ∈ records, r.start = P.closed r.owner → r.stop - r.start = P.width r.owner := by
  induction h with
  | done P hd => simp
  | step P Q j key hk hmax hearliest records tail ih =>
    intro r hr ha
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [record, boundary, Nat.add_sub_cancel_left]
    · by_cases ho : r.owner = j
      · have hs := tail.start_lower r hr
        rw [ho, advance_closed] at hs
        rw [ho] at ha
        omega
      · have he := ih r hr (by simpa only [advance, if_neg ho] using ha)
        simpa only [advance, if_neg ho] using he

end LayeredPrefix

namespace BatchedAdversary
open LayeredPrefix
variable {jobs work m L : ℕ}

theorem epochWideWork_congr (m L : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) {S T : Assignment (vertices := jobs * work)} {t : ℕ}
    (h : PastAgreement S T t) : epochWideWork m L history j S t = epochWideWork m L history j T t := by
  unfold epochWideWork
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, h.interval ((t / L) * L) v]

theorem idleEarlier_congr (m L : ℕ) {S T : Assignment (vertices := jobs * work)} {t : ℕ}
    (h : PastAgreement S T t) : IdleEarlier m L S t ↔ IdleEarlier m L T t := by
  constructor
  · rintro ⟨u, hlo, hhi, hc⟩
    exact ⟨u, hlo, hhi, by rwa [← h.slot_card u hhi]⟩
  · rintro ⟨u, hlo, hhi, hc⟩
    exact ⟨u, hlo, hhi, by rwa [h.slot_card u hhi]⟩

theorem chooseWide_congr (m L : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) {S T : Assignment (vertices := jobs * work)} {t : ℕ}
    (h : PastAgreement S T t) : ChooseWide m L history j S t ↔ ChooseWide m L history j T t := by
  unfold ChooseWide
  rw [epochWideWork_congr m L history j h, idleEarlier_congr m L h]

/-- The rule evaluated directly on a fixed execution, without a partial
graph or a scheduler call hidden inside its definition. -/
noncomputable def finalWidth (m L : ℕ) (history : List (LayerRecord jobs work)) (j : Fin jobs)
    (p : ℕ) (S : Assignment (vertices := jobs * work)) (t : ℕ) : ℕ :=
  min (work - p) (if ChooseWide m L history j S t then 2 * m - 1 else 1)

/-- Each actual layer choice agrees with its evaluation on the final
fixed execution. The premise identifies the immediately following layer
of the same job by its starting position. -/
theorem history_rule_in_final (hm : 2 ≤ m) (hL : 0 < L) (A : DeterministicScheduler m)
    {history records : List (LayerRecord jobs (m * L))} {P Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) history P Q records) :
    ∀ before r after, records = before ++ r :: after →
      ∀ s ∈ after, s.owner = r.owner → s.start = r.stop →
        s.stop - s.start = finalWidth m L (history ++ before ++ [r]) r.owner r.stop
          (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) (r.time + 1) := by
  induction h with
  | done history P hd =>
    intro before r after he
    have hl := congrArg List.length he
    simp only [List.length_nil, List.length_append, List.length_cons] at hl
    omega
  | step history P Q j key hk hmax hearliest records tail ih =>
    intro before r after he s hs ho ha
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨heq, htail⟩ := he
      subst r
      subst after
      obtain ⟨staticRule, hr⟩ := tail.flexible.recorded
      have hwidth := hr.start_width s hs (by
        rw [ho]
        simpa only [record, advance_closed] using ha)
      have hfull := HistoryRun.step history P Q j key hk hmax hearliest records tail
      have hpast := hfull.past_agreement _ hearliest
      have hc := chooseWide_congr m L (history ++ [P.record (L := L) (Nat.mul_pos (show 0 < m by omega) hL) A j key]) j hpast
      simp only [advance, ho, record, if_true] at hwidth
      change s.stop - s.start = min (m * L - P.boundary j)
        (if ChooseWide m L (history ++ [P.record (L := L) (Nat.mul_pos (show 0 < m by omega) hL) A j key]) j
          (A.schedule (P.toInstance L (Nat.mul_pos (show 0 < m by omega) hL)))
          (A.schedule (P.toInstance L (Nat.mul_pos (show 0 < m by omega) hL)) (finProdFinEquiv (j, key)) + 1) then 2 * m - 1 else 1) at hwidth
      dsimp only [record] at hc hwidth
      simp only [finalWidth, List.append_nil, record]
      rw [← hc]
      exact hwidth
    | cons a before =>
      simp only [List.cons_append, List.cons.injEq] at he
      have hh := ih before r after he.2 s hs ho ha
      rw [← he.1]
      simpa only [List.append_assoc, List.singleton_append] using hh

end BatchedAdversary
end Scheduling
