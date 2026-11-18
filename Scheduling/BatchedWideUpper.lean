import Scheduling.BatchedRevealTimes

namespace Scheduling.BatchedAdversary
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ}

noncomputable def jobWideService (m : ℕ) (records : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (a b : ℕ) : ℕ :=
  (univ.filter (fun v => WideRecorded m records j v ∧ a ≤ S v ∧ S v < b)).card

theorem jobWideService_zero_before (m : ℕ) (records : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (a b e : ℕ)
    (hea : e ≤ a) (hclosed : ∀ v, WideRecorded m records j v → S v < e) :
    jobWideService m records j S a b = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hv' := (mem_filter.mp hv).2
  have ht := hclosed v hv'.1
  omega

theorem jobWideService_zero_after (m : ℕ) (records : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (a b : ℕ)
    (hfuture : ∀ v, WideRecorded m records j v → b ≤ S v) :
    jobWideService m records j S a b = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hv' := (mem_filter.mp hv).2
  have ht := hfuture v hv'.1
  omega

/-- After the last wide layer revealed before the interval ends, only
that one layer can add service beyond the already completed prefix. -/
theorem jobWideService_cut_le (m : ℕ) (before after : List (LayerRecord jobs work))
    (r : LayerRecord jobs work) (j : Fin jobs) (S : Assignment (vertices := jobs * work))
    (a b e : ℕ)
    (hclosed : ∀ v, WideRecorded m before j v → S v < e)
    (hfuture : ∀ v, WideRecorded m after j v → b ≤ S v) :
    jobWideService m (before ++ r :: after) j S a b ≤
      jobWideService m before j S a e + (r.stop - r.start) := by
  let old := univ.filter (fun v => WideRecorded m before j v ∧ a ≤ S v ∧ S v < e)
  let layer := univ.filter (fun v : Fin (jobs * work) => job v = j ∧
    r.start ≤ (position v).val ∧ (position v).val < r.stop)
  have hs : univ.filter (fun v => WideRecorded m (before ++ r :: after) j v ∧ a ≤ S v ∧ S v < b)
      ⊆ old ∪ layer := by
    intro v hv
    obtain ⟨⟨ho, s, hmem, hsowner, hswidth, hlo, hhi⟩, htime⟩ := (mem_filter.mp hv).2
    rcases List.mem_append.mp hmem with hpast | htail
    · have hw : WideRecorded m before j v := ⟨ho, s, hpast, hsowner, hswidth, hlo, hhi⟩
      exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hw, htime.1, hclosed v hw⟩)
    · rcases List.mem_cons.mp htail with he | hafter
      · subst s
        exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, ho, hlo, hhi⟩)
      · have ht := hfuture v ⟨ho, s, hafter, hsowner, hswidth, hlo, hhi⟩
        omega
  have hc := (card_le_card hs).trans (card_union_le old layer)
  exact hc.trans (Nat.add_le_add_left (owner_interval_card_le j r.start r.stop) old.card)

private theorem exists_last_satisfying {α : Type*} (p : α → Prop) (xs : List α) :
    (∀ x ∈ xs, ¬ p x) ∨ ∃ before x after, xs = before ++ x :: after ∧ p x ∧ ∀ y ∈ after, ¬ p y := by
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons x xs ih =>
    rcases ih with hn | ⟨before, y, after, he, hy, hafter⟩
    · by_cases hx : p x
      · exact Or.inr ⟨[], x, xs, rfl, hx, hn⟩
      · left
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hn y hy
    · exact Or.inr ⟨x :: before, y, after, by simp only [List.cons_append, he], hy, hafter⟩

theorem CertifiedReveals.future_wide {records after : List (LayerRecord jobs (m * L))}
    {S : Assignment (vertices := jobs * (m * L))} {E : LayerRecord jobs (m * L) → ℕ}
    (h : CertifiedReveals m L records S E) (j : Fin jobs) (b : ℕ)
    (hsub : ∀ r ∈ after, r ∈ records)
    (hlast : ∀ r ∈ after, ¬ (r.owner = j ∧ r.stop - r.start = 2 * m - 1 ∧ E r < b)) :
    ∀ v, WideRecorded m after j v → b ≤ S v := by
  rintro v ⟨ho, r, hr, hrj, hrw, hlo, hhi⟩
  have hn := hlast r hr
  have ht := h.layer_after r (hsub r hr) v (ho.trans hrj.symm) hlo hhi
  omega

/-- Each job admits a cutoff in the epoch: its total wide service is
bounded by the remaining epoch length at that cutoff, and its suffix
service after the cutoff is at most one wide layer. -/
theorem CertifiedReveals.job_wide_cutoff (hm : 2 ≤ m) (hL : 0 < L)
    {records : List (LayerRecord jobs (m * L))}
    {S : Assignment (vertices := jobs * (m * L))} {E : LayerRecord jobs (m * L) → ℕ}
    (h : CertifiedReveals m L records S E) (j : Fin jobs) (i : ℕ)
    (hfull : ∀ t, i * L ≤ t → t < (i + 1) * L → ¬ IdleEarlier m L S t) :
    ∃ t, i * L ≤ t ∧ t ≤ (i + 1) * L ∧
      jobWideService m records j S (i * L) ((i + 1) * L) ≤
        (2 * m - 1) * ((i + 1) * L - t + 1) ∧
      ∀ u, t ≤ u → jobWideService m records j S u ((i + 1) * L) ≤ 2 * m - 1 := by
  have hend : (i + 1) * L = i * L + L := by ring
  rcases exists_last_satisfying
      (fun r : LayerRecord jobs (m * L) => r.owner = j ∧ r.stop - r.start = 2 * m - 1 ∧ E r < (i + 1) * L)
      records with hnone | ⟨before, r, after, heq, ⟨hrj, hrw, hre⟩, hlast⟩
  · have hf := h.future_wide j ((i + 1) * L) (fun _ hr => hr) hnone
    refine ⟨(i + 1) * L, by omega, le_rfl, ?_, ?_⟩
    · rw [jobWideService_zero_after m records j S _ _ hf]
      omega
    · intro u _
      rw [jobWideService_zero_after m records j S _ _ hf]
      omega
  · have hc := h before r after heq
    have hclosed : ∀ v, WideRecorded m before j v → S v < E r := by
      simpa only [hrj] using hc.reveal.closed_before
    have hf := h.future_wide j ((i + 1) * L)
      (fun s hs => heq ▸ List.mem_append_right before (List.mem_cons_of_mem r hs)) hlast
    have hcut : ∀ a, jobWideService m records j S a ((i + 1) * L) ≤
        jobWideService m before j S a (E r) + (2 * m - 1) := by
      intro a
      rw [heq]
      simpa only [hrw] using jobWideService_cut_le m before after r j S a ((i + 1) * L) (E r) hclosed hf
    by_cases hstart : i * L ≤ E r
    · have hep : E r / L = i := by
        apply Nat.div_eq_of_lt_le hstart
        exact hre
      have hx := hc.wide_below hm hL hrw (hfull _ hstart hre)
      rw [hrj] at hx
      have hxeq : epochWideWork m L before j S (E r) = jobWideService m before j S (i * L) (E r) := by
        simp only [epochWideWork, jobWideService, hep]
      rw [hxeq] at hx
      have hmod := Nat.div_add_mod (E r) L
      rw [hep] at hmod
      have hmod' : i * L + E r % L = E r := by nlinarith
      have hd : L - E r % L = (i + 1) * L - E r := by
        have := Nat.mod_lt (E r) hL
        omega
      rw [hd] at hx
      refine ⟨E r, hstart, hre.le, ?_, ?_⟩
      · have hh := hcut (i * L)
        nlinarith
      · intro u hu
        have hh := hcut u
        rw [jobWideService_zero_before m before j S u (E r) (E r) hu hclosed] at hh
        simpa only [Nat.zero_add] using hh
    · have hzero := jobWideService_zero_before m before j S (i * L) (E r) (E r) (by omega) hclosed
      have htotal := hcut (i * L)
      rw [hzero, Nat.zero_add] at htotal
      refine ⟨(i + 1) * L, by omega, le_rfl, by simpa only [Nat.sub_self, Nat.zero_add, Nat.mul_one] using htotal, ?_⟩
      intro u hu
      have hh := hcut u
      rw [jobWideService_zero_before m before j S u (E r) (E r) (by omega) hclosed] at hh
      simpa only [Nat.zero_add] using hh

def JobCutoffs (m L : ℕ) (records : List (LayerRecord jobs (m * L)))
    (S : Assignment (vertices := jobs * (m * L))) (i : ℕ) (T : Fin jobs → ℕ) : Prop :=
  ∀ j, i * L ≤ T j ∧ T j ≤ (i + 1) * L ∧
    jobWideService m records j S (i * L) ((i + 1) * L) ≤
      (2 * m - 1) * ((i + 1) * L - T j + 1) ∧
    ∀ u, T j ≤ u → jobWideService m records j S u ((i + 1) * L) ≤ 2 * m - 1

theorem noIdleEarlier_of_full_epoch (S : Assignment (vertices := jobs * work))
    (i t : ℕ) (hlo : i * L ≤ t) (hhi : t < (i + 1) * L)
    (hfull : ∀ u, i * L ≤ u → u < (i + 1) * L → (univ.filter (fun v => S v = u)).card = m) :
    ¬ IdleEarlier m L S t := by
  have hep : t / L = i := Nat.div_eq_of_lt_le hlo hhi
  rintro ⟨u, hu, hut, hc⟩
  rw [hep] at hu
  have he := hfull u hu (hut.trans hhi)
  omega

/-- The actual adaptive construction supplies all per-job cutoffs in
any full epoch. No passivity times or service bounds are assumed. -/
theorem full_epoch_job_cutoffs (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : LayeredPrefix.HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) (i : ℕ)
    (hfull : ∀ u, i * L ≤ u → u < (i + 1) * L →
      (univ.filter (fun v => A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)) v = u)).card = m) :
    ∃ T, JobCutoffs m L records (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) i T := by
  obtain ⟨E, hE⟩ := exists_record_reveal_times hm hL heven A h
  have hc := fun j => hE.job_wide_cutoff hm hL j i
    (fun t hlo hhi => noIdleEarlier_of_full_epoch _ i t hlo hhi hfull)
  choose T hT using hc
  exact ⟨T, hT⟩

end Scheduling.BatchedAdversary
