import Scheduling.BatchedLayerRule

namespace Scheduling.BatchedAdversary
open Finset
open LayeredPrefix
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ}

theorem wideCount_append_record (m : ℕ) (history : List (LayerRecord jobs work))
    (P : LayeredPrefix jobs work) (hw : 0 < work) (A : DeterministicScheduler m)
    (L : ℕ) (j i : Fin jobs) (key : Fin work) :
    wideCount m (history ++ [P.record (L := L) hw A j key]) i = wideCount m history i +
      if j = i ∧ P.width j = 2 * m - 1 then 1 else 0 := by
  by_cases ho : j = i
  · subst i
    by_cases hw : P.width j = 2 * m - 1 <;>
      simp [wideCount, List.filter_append, record, boundary, hw]
  · simp [wideCount, List.filter_append, record, boundary, ho]

theorem narrowCount_append_record (history : List (LayerRecord jobs work))
    (P : LayeredPrefix jobs work) (hw : 0 < work) (A : DeterministicScheduler m)
    (L : ℕ) (j i : Fin jobs) (key : Fin work) :
    narrowCount (history ++ [P.record (L := L) hw A j key]) i = narrowCount history i +
      if j = i ∧ P.width j = 1 then 1 else 0 := by
  by_cases ho : j = i
  · subst i
    by_cases hw : P.width j = 1 <;>
      simp [narrowCount, List.filter_append, record, boundary, hw]
  · simp [narrowCount, List.filter_append, record, boundary, ho]

/-- Counts of committed layers, together with the budget reserved for
the currently revealed frontier. -/
def Budget (m L : ℕ) (history : List (LayerRecord jobs (m * L)))
    (P : LayeredPrefix jobs (m * L)) : Prop := ∀ j,
  wideCount m history j ≤ L / 2 ∧
  narrowCount history j ≤ wideCount m history j ∧
  P.closed j = (2 * m - 1) * wideCount m history j + narrowCount history j ∧
  ((P.width j = 0 ∧ P.closed j = m * L) ∨
    (P.width j = 2 * m - 1 ∧ wideCount m history j < L / 2) ∨
    (P.width j = 1 ∧ narrowCount history j < wideCount m history j))

theorem initial_budget (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L) :
    Budget m L [] (initial jobs m L hm) := by
  have hL2 : 2 ≤ L := by omega
  have hmul := Nat.mul_le_mul_left m hL2
  have hb : 2 * m - 1 ≤ m * L := by omega
  intro j
  simp [wideCount, narrowCount, initial, min_eq_left hb, show 0 < L / 2 by omega]

theorem budget_advance (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) (history : List (LayerRecord jobs (m * L)))
    (P : LayeredPrefix jobs (m * L)) (hbudget : Budget m L history P)
    (j : Fin jobs) (key : Fin (m * L))
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j) :
    let hw : 0 < m * L := Nat.mul_pos (by omega) hL
    let next := history ++ [P.record (L := L) hw A j key]
    let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1
    Budget m L next (P.advance j key hk ((rule jobs m L hm hL A).size next P j t)
      ((rule jobs m L hm hL A).fits _ _ _ _) ((rule jobs m L hm hL A).positive _ _ _ _)) := by
  dsimp only
  let hw : 0 < m * L := Nat.mul_pos (by omega) hL
  let next := history ++ [P.record (L := L) hw A j key]
  let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1
  have hb1 : 2 * m - 1 ≠ 1 := by omega
  have hcounts : wideCount m next j ≤ L / 2 ∧ narrowCount next j ≤ wideCount m next j ∧
      P.boundary j = (2 * m - 1) * wideCount m next j + narrowCount next j := by
    obtain ⟨hwc, hnc, hp, hs⟩ := hbudget j
    rcases hs with ⟨hz, _⟩ | ⟨hwide, hspace⟩ | ⟨hnarrow, hspace⟩
    · have hbd : P.boundary j = P.closed j := by simp only [boundary, hz, Nat.add_zero]
      omega
    · dsimp only [next]
      rw [wideCount_append_record, narrowCount_append_record]
      simp only [hwide, true_and, if_true, hb1, if_false, Nat.add_zero]
      refine ⟨by omega, by omega, ?_⟩
      dsimp only [boundary]
      rw [hp, hwide]
      ring
    · dsimp only [next]
      rw [wideCount_append_record, narrowCount_append_record]
      simp only [hnarrow, true_and, if_true, Ne.symm hb1, if_false, Nat.add_zero]
      refine ⟨hwc, by omega, ?_⟩
      dsimp only [boundary]
      rw [hp, hnarrow]
      omega
  intro i
  by_cases hi : i = j
  · subst i
    have hs := rule_width_shape hm hL heven A next P j t hcounts.1 hcounts.2.1 hcounts.2.2
    refine ⟨hcounts.1, hcounts.2.1, ?_, ?_⟩
    · simpa only [advance_closed] using hcounts.2.2
    · simpa only [advance, if_pos rfl, if_true, next, t] using hs
  · have hwc : wideCount m next i = wideCount m history i := by
      dsimp only [next]
      rw [wideCount_append_record]
      simp only [Ne.symm hi, false_and, if_false, Nat.add_zero]
    have hnc : narrowCount next i = narrowCount history i := by
      dsimp only [next]
      rw [narrowCount_append_record]
      simp only [Ne.symm hi, false_and, if_false, Nat.add_zero]
    dsimp only [next] at hwc hnc
    simpa only [advance, if_neg hi, hwc, hnc] using hbudget i

theorem history_budget_end (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {history records : List (LayerRecord jobs (m * L))}
    {P Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) history P Q records)
    (hb : Budget m L history P) : Budget m L (history ++ records) Q := by
  induction h with
  | done history P hd => simpa only [List.append_nil] using hb
  | step history P Q j key hk hmax hearliest records tail ih =>
    have hn := budget_advance hm hL heven A history P hb j key hk
    have hh := ih hn
    simpa only [List.append_assoc, List.singleton_append] using hh

theorem final_layer_counts (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) :
    ∀ j, wideCount m records j = L / 2 ∧ narrowCount records j = L / 2 := by
  have hb := history_budget_end hm hL heven A h (initial_budget hm hL heven)
  simp only [List.nil_append] at hb
  obtain ⟨staticRule, hr⟩ := h.flexible.recorded
  intro j
  obtain ⟨hwc, hnc, hp, _⟩ := hb j
  rw [hr.completion.finished] at hp
  have ht : (2 * m - 1) * (L / 2) + L / 2 = m * L := by
    have hm1 : 2 * m - 1 + 1 = 2 * m := by omega
    nlinarith
  have hnle := hnc.trans hwc
  have hmul := Nat.mul_le_mul_left (2 * m - 1) hwc
  have hw : wideCount m records j = L / 2 := by
    by_contra hh
    have hlt : wideCount m records j + 1 ≤ L / 2 := by omega
    have hm' := Nat.mul_le_mul_left (2 * m - 1) hlt
    nlinarith
  exact ⟨hw, by rw [hw] at hp; omega⟩

theorem history_prefix_counts (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {history records : List (LayerRecord jobs (m * L))}
    {P Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) history P Q records)
    (hb : Budget m L history P) (n : ℕ) :
    ∀ j, narrowCount (history ++ records.take n) j ≤ wideCount m (history ++ records.take n) j := by
  induction h generalizing n with
  | done history P hd =>
    intro j
    simpa only [List.take_nil, List.append_nil] using (hb j).2.1
  | step history P Q j key hk hmax hearliest records tail ih =>
    cases n with
    | zero =>
      intro i
      simpa only [List.take_zero, List.append_nil] using (hb i).2.1
    | succ n =>
      have hn := budget_advance hm hL heven A history P hb j key hk
      have hh := ih hn n
      simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using hh

theorem history_widths (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {history records : List (LayerRecord jobs (m * L))}
    {P Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) history P Q records)
    (hb : Budget m L history P) :
    ∀ r ∈ records, r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1 := by
  induction h with
  | done history P hd => simp
  | step history P Q j key hk hmax hearliest records tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hs := (hb j).2.2.2
      rcases hs with ⟨hz, _⟩ | ⟨hw, _⟩ | ⟨hn, _⟩
      · have he : P.boundary j = P.closed j := by simp only [boundary, hz, Nat.add_zero]
        omega
      · left
        simpa only [record, boundary, Nat.add_sub_cancel_left] using hw
      · right
        simpa only [record, boundary, Nat.add_sub_cancel_left] using hn
    · exact ih (budget_advance hm hL heven A history P hb j key hk) r hr

theorem job_count_eq (hm : 2 ≤ m) (history : List (LayerRecord jobs work))
    (hwidth : ∀ r ∈ history, r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1)
    (j : Fin jobs) :
    (history.filter (fun r => r.owner = j)).length = wideCount m history j + narrowCount history j := by
  have hb1 : 2 * m - 1 ≠ 1 := by omega
  induction history with
  | nil => simp [wideCount, narrowCount]
  | cons r rs ih =>
    have ht := ih (fun s hs => hwidth s (List.mem_cons_of_mem _ hs))
    have hr := hwidth r List.mem_cons_self
    by_cases ho : r.owner = j
    · rcases hr with hw | hn
      · simp only [wideCount, narrowCount] at ht ⊢
        simp [ho, hw, hb1] at ht ⊢
        omega
      · simp only [wideCount, narrowCount] at ht ⊢
        simp [ho, hn, Ne.symm hb1] at ht ⊢
        omega
    · simp only [wideCount, narrowCount] at ht ⊢
      simpa [List.filter_cons, ho] using ht

theorem final_job_length (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) (j : Fin jobs) :
    (records.filter (fun r => r.owner = j)).length = L := by
  have hc := final_layer_counts hm hL heven A h j
  rw [job_count_eq hm records (history_widths hm hL heven A h (initial_budget hm hL heven)) j,
    hc.1, hc.2]
  omega

/-- The actual threshold construction has exactly the required layer
counts and a balanced prefix at every commitment. Causality and key-last
timing are supplied by the associated recorded run. -/
theorem exists_balanced_layer_run (jobs m L : ℕ) (hm : 2 ≤ m) (hL : 0 < L)
    (heven : 2 * (L / 2) = L) (A : DeterministicScheduler m) :
    ∃ Q records,
      HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
        (initial jobs m L hm) Q records ∧
      (∃ staticRule, RecordedRun (L := L) (Nat.mul_pos (by omega) hL) A staticRule
        (initial jobs m L hm) Q records) ∧
      (∀ r ∈ records, r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1) ∧
      (∀ j, wideCount m records j = L / 2 ∧ narrowCount records j = L / 2) ∧
      (∀ n j, narrowCount (records.take n) j ≤ wideCount m (records.take n) j) := by
  obtain ⟨Q, records, hh, hr, _⟩ := exists_candidate jobs m L hm hL A
  have hb := initial_budget (jobs := jobs) hm hL heven
  refine ⟨Q, records, hh, hr, history_widths hm hL heven A hh hb,
    final_layer_counts hm hL heven A hh, ?_⟩
  intro n j
  simpa only [List.nil_append] using history_prefix_counts hm hL heven A hh hb n j

end Scheduling.BatchedAdversary
