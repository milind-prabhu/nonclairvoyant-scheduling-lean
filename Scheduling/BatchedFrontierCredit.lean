import Scheduling.BatchedChoice

namespace Scheduling.BatchedAdversary
open Finset LayeredPrefix
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs m L : ℕ}

/-- A revealed layer carries a credit certificate in the final execution.
The credit is needed only before the first idle slot of its epoch and
while another wide layer remains in the budget. -/
structure RevealCredit (m L : ℕ) (history : List (LayerRecord jobs (m * L)))
    (j : Fin jobs) (S : Assignment (vertices := jobs * (m * L))) (e width : ℕ) : Prop where
  closed_before : ∀ v, WideRecorded m history j v → S v < e
  credit : ¬ IdleEarlier m L S e → wideCount m history j < L / 2 →
    BatchedForcing.ThresholdCredit (2 * m - 1) (L - e % L)
      (wideCount m history j) (narrowCount history j) (epochWideWork m L history j S e)
  wide_choice : width = 2 * m - 1 → wideCount m history j ≤ narrowCount history j ∨
    IdleEarlier m L S e ∨ epochWideWork m L history j S e < (2 * m - 1) * (L - e % L)
  narrow_threshold : width = 1 → wideCount m history j < L / 2 →
    (2 * m - 1) * (L - e % L) ≤ epochWideWork m L history j S e

def FrontierCredit (m L : ℕ) (history : List (LayerRecord jobs (m * L)))
    (P : LayeredPrefix jobs (m * L)) (S : Assignment (vertices := jobs * (m * L))) : Prop :=
  ∀ j, ∃ e, (∀ v ∈ P.frontier j, e ≤ S v) ∧ RevealCredit m L history j S e (P.width j)

theorem initial_frontierCredit (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (S : Assignment (vertices := jobs * (m * L)))
    (hrelease : ∀ v, (job v).val * L ≤ S v) :
    FrontierCredit m L [] (initial jobs m L hm) S := by
  have hfit : 2 * m - 1 ≤ m * L := by
    have := Nat.mul_le_mul_left m (show 2 ≤ L by omega)
    omega
  intro j
  refine ⟨j.val * L, ?_, ?_⟩
  · intro v hv
    have ho := (mem_filter.mp hv).2.1
    simpa only [ho] using hrelease v
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨_, r, hr, _⟩ := hv
      simp at hr
    · intro _ _
      left
      simp [epochWideWork, WideRecorded]
    · intro _
      left
      simp [wideCount, narrowCount]
    · intro hn _
      simp only [initial, min_eq_left hfit] at hn
      omega

theorem RevealCredit.after_record (hm : 2 ≤ m) (hL : 0 < L)
    (heven : 2 * (L / 2) = L)
    (history : List (LayerRecord jobs (m * L))) (r : LayerRecord jobs (m * L))
    (j : Fin jobs) (S : Assignment (vertices := jobs * (m * L))) (e width p : ℕ)
    (h : RevealCredit m L history j S e width)
    (ho : r.owner = j) (hw : r.stop - r.start = width) (he : e ≤ r.time)
    (hshape : width = 2 * m - 1 ∨ width = 1)
    (hbalance : narrowCount history j ≤ wideCount m history j)
    (hnewbalance : narrowCount (history ++ [r]) j ≤ wideCount m (history ++ [r]) j)
    (hprefix : p = (2 * m - 1) * wideCount m (history ++ [r]) j + narrowCount (history ++ [r]) j)
    (htimes : ∀ v, job v = j → r.start ≤ (position v).val → (position v).val < r.stop →
      S v ≤ r.time) :
    RevealCredit m L (history ++ [r]) j S (r.time + 1)
      (finalWidth m L (history ++ [r]) j p S (r.time + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases (wideRecorded_append m history r j v).mp hv with hv | hv
    · exact (h.closed_before v hv).trans_le (by omega)
    · have ht := htimes v hv.1 hv.2.2.2.1 hv.2.2.2.2
      omega
  · intro hfull hquota
    have hquota' : wideCount m history j < L / 2 := by
      rw [wideCount_append] at hquota
      omega
    have hfull' : e / L = (r.time + 1) / L → ¬ IdleEarlier m L S e := by
      intro hep hi
      exact hfull (idleEarlier_mono_same_epoch S (by omega) hep hi)
    apply credit_after_record hm hL history r j S e (r.time + 1) ho (by omega)
      (by simpa only [hw] using hshape) hbalance h.closed_before
    · intro hep
      exact h.credit (hfull' hep) hquota'
    · intro hep hr
      rcases h.wide_choice (hw.symm.trans hr) with hg | hi | hx
      · exact Or.inl hg
      · exact False.elim (hfull' hep hi)
      · exact Or.inr hx
    · intro _ hr
      exact h.narrow_threshold (hw.symm.trans hr) hquota'
  · intro hwide
    exact (finalWidth_wide_implies_choose hm _ j p S _ hwide).2
  · intro hn hquota
    exact finalWidth_narrow_threshold hm heven _ j p S _ hnewbalance hprefix hquota hn

theorem RevealCredit.append_other
    (history : List (LayerRecord jobs (m * L))) (r : LayerRecord jobs (m * L))
    (j : Fin jobs) (S : Assignment (vertices := jobs * (m * L))) (e width : ℕ)
    (ho : r.owner ≠ j) (h : RevealCredit m L history j S e width) :
    RevealCredit m L (history ++ [r]) j S e width := by
  have hw : wideCount m (history ++ [r]) j = wideCount m history j := by
    simp only [wideCount_append, ho, false_and, if_false, Nat.add_zero]
  have hn : narrowCount (history ++ [r]) j = narrowCount history j := by
    simp only [narrowCount_append, ho, false_and, if_false, Nat.add_zero]
  have hx := epochWideWork_append_unchanged m L history r j S e (Or.inl ho)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases (wideRecorded_append m history r j v).mp hv with hv | hv
    · exact h.closed_before v hv
    · exact False.elim (ho hv.2.1)
  · simpa only [hw, hn, hx] using h.credit
  · simpa only [hw, hn, hx] using h.wide_choice
  · simpa only [hw, hx] using h.narrow_threshold

theorem frontierCredit_advance (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) (history : List (LayerRecord jobs (m * L)))
    (P Q : LayeredPrefix jobs (m * L)) (j : Fin jobs) (key : Fin (m * L))
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL)) v ≤
      A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL)) (finProdFinEquiv (j, key)))
    (hearliest : ∀ i, P.closed i < m * L →
      A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL)) (finProdFinEquiv (j, key)) ≤
        P.finishTime (L := L) (Nat.mul_pos (by omega) hL) A i)
    (records : List (LayerRecord jobs (m * L)))
    (tail : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A)
      (history ++ [P.record (L := L) (Nat.mul_pos (by omega) hL) A j key])
      (P.advance j key hk
        ((rule jobs m L hm hL A).size
          (history ++ [P.record (L := L) (Nat.mul_pos (by omega) hL) A j key]) P j
          (A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL)) (finProdFinEquiv (j, key)) + 1))
        ((rule jobs m L hm hL A).fits _ _ _ _) ((rule jobs m L hm hL A).positive _ _ _ _))
      Q records)
    (hb : Budget m L history P)
    (hc : FrontierCredit m L history P (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)))) :
    let hw : 0 < m * L := Nat.mul_pos (by omega) hL
    let next := history ++ [P.record (L := L) hw A j key]
    let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1
    FrontierCredit m L next (P.advance j key hk ((rule jobs m L hm hL A).size next P j t)
      ((rule jobs m L hm hL A).fits _ _ _ _) ((rule jobs m L hm hL A).positive _ _ _ _))
      (A.schedule (Q.toInstance L hw)) := by
  dsimp only
  let hw : 0 < m * L := Nat.mul_pos (by omega) hL
  let r := P.record (L := L) hw A j key
  let next := history ++ [r]
  let t := r.time + 1
  let q := (rule jobs m L hm hL A).size next P j t
  let R := P.advance j key hk q ((rule jobs m L hm hL A).fits _ _ _ _)
    ((rule jobs m L hm hL A).positive _ _ _ _)
  let S := A.schedule (Q.toInstance L hw)
  change FrontierCredit m L next R S
  have hfull := HistoryRun.step history P Q j key hk hmax hearliest records tail
  obtain ⟨staticRule, hr⟩ := hfull.flexible.recorded
  have htimes := hr.final_times r List.mem_cons_self
  have hkey : S (finProdFinEquiv (j, key)) = r.time := htimes.2.2.2.1
  have hbnext : Budget m L next R := budget_advance hm hL heven A history P hb j key hk
  have hq : q = finalWidth m L next j (P.boundary j) S t := by
    have hpast := hfull.past_agreement r.time hearliest
    have hchoose := chooseWide_congr m L next j hpast
    change min (m * L - P.boundary j)
      (if ChooseWide m L next j (A.schedule (P.toInstance L hw)) t then 2 * m - 1 else 1) = _
    unfold finalWidth
    rw [hchoose]
  intro i
  by_cases hij : i = j
  · subst i
    obtain ⟨e, he, hcredit⟩ := hc j
    have hekey := he (finProdFinEquiv (j, key)) (by
      apply mem_filter.mpr
      exact ⟨mem_univ _, LayeredForest.job_pair j key, by
        simpa only [LayeredForest.position_pair] using hk⟩)
    change e ≤ S (finProdFinEquiv (j, key)) at hekey
    rw [hkey] at hekey
    refine ⟨t, ?_, ?_⟩
    · intro v hv
      obtain ⟨tailRule, ht⟩ := tail.flexible.recorded
      have hv' := (mem_filter.mp hv).2
      change job v = j ∧ R.closed j ≤ (position v).val ∧ (position v).val < R.boundary j at hv'
      have hp := ht.completion.parent_visible j (position v) hv'.2.2
      have hnew : R.parent j (position v) = some key := by
        have hlo : P.boundary j ≤ (position v).val := by simpa only [R, advance_closed] using hv'.2.1
        have hhi : (position v).val < P.boundary j + q := by simpa only [R, advance_boundary] using hv'.2.2
        exact if_pos ⟨rfl, hlo, hhi⟩
      have hvQ : (position v).val < Q.boundary j := by
        have hf := ht.completion.finished j
        have hpos := (position v).isLt
        dsimp only [boundary]
        omega
      have hedge : (Q.toInstance L hw).edge (finProdFinEquiv (j, key)) v := by
        refine ⟨(LayeredForest.job_pair j key).trans hv'.1.symm, ?_⟩
        simp only [hv'.1, if_pos hvQ, LayeredForest.position_pair]
        exact hp.trans hnew
      have htime := (A.valid (Q.toInstance L hw)).precedence hedge
      change S (finProdFinEquiv (j, key)) < S v at htime
      rw [hkey] at htime
      exact htime
    · have hshape : P.width j = 2 * m - 1 ∨ P.width j = 1 := by
        rcases (hb j).2.2.2 with ⟨hz, _⟩ | ⟨hw', _⟩ | ⟨hn, _⟩
        · have hbound : P.boundary j = P.closed j := by simp only [boundary, hz, Nat.add_zero]
          omega
        · exact Or.inl hw'
        · exact Or.inr hn
      have hstep := hcredit.after_record hm hL heven history r j S e (P.width j) (P.boundary j)
        rfl (by simp only [r, record, boundary, Nat.add_sub_cancel_left]) hekey hshape
        (hb j).2.1 (hbnext j).2.1
        (by simpa only [R, advance_closed] using (hbnext j).2.2.1)
        (fun v ho hlo hhi => htimes.2.2.2.2 v ho hlo hhi)
      simp only [R, advance]
      rw [hq]
      exact hstep
  · obtain ⟨e, he, hcredit⟩ := hc i
    refine ⟨e, ?_, ?_⟩
    · intro v hv
      exact he v (by simpa only [R, P.advance_other_frontier j i hij] using hv)
    · change RevealCredit m L (history ++ [r]) i S e (if i = j then q else P.width i)
      rw [if_neg hij]
      exact hcredit.append_other history r i S e (P.width i) (Ne.symm hij)

end Scheduling.BatchedAdversary
