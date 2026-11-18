import Scheduling.BatchedCounters

namespace Scheduling.BatchedAdversary
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ}

theorem idleEarlier_mono_same_epoch (S : Assignment (vertices := jobs * work))
    {e u : ℕ} (heu : e ≤ u) (hepoch : e / L = u / L)
    (h : IdleEarlier m L S e) : IdleEarlier m L S u := by
  obtain ⟨t, hlo, hhi, hc⟩ := h
  exact ⟨t, by rwa [← hepoch], hhi.trans_le heu, hc⟩

theorem finalWidth_wide_implies_choose (hm : 2 ≤ m)
    (history : List (LayerRecord jobs work)) (j : Fin jobs) (p : ℕ)
    (S : Assignment (vertices := jobs * work)) (t : ℕ)
    (hw : finalWidth m L history j p S t = 2 * m - 1) :
    ChooseWide m L history j S t := by
  by_contra hn
  simp only [finalWidth, if_neg hn] at hw
  have hh := min_le_right (work - p) 1
  omega

/-- With unspent wide-layer budget, a full wide layer fits in the
remaining work. Thus truncation cannot turn a wide choice into a narrow
layer. -/
theorem finalWidth_narrow_implies_not_choose (hm : 2 ≤ m) (heven : 2 * (L / 2) = L)
    (history : List (LayerRecord jobs (m * L))) (j : Fin jobs) (p : ℕ)
    (S : Assignment (vertices := jobs * (m * L))) (t : ℕ)
    (hbalance : narrowCount history j ≤ wideCount m history j)
    (hprefix : p = (2 * m - 1) * wideCount m history j + narrowCount history j)
    (hn : finalWidth m L history j p S t = 1) :
    ¬ ChooseWide m L history j S t := by
  intro hc
  have htotal : (2 * m - 1) * (L / 2) + L / 2 = m * L := by
    have hb : 2 * m - 1 + 1 = 2 * m := by omega
    nlinarith
  have hw := hc.1
  have hmul := Nat.mul_le_mul_left (2 * m - 1)
    (show wideCount m history j + 1 ≤ L / 2 by omega)
  have hfit : 2 * m - 1 ≤ m * L - p := by
    have hs : p + (2 * m - 1) ≤ m * L := by nlinarith
    omega
  simp only [finalWidth, if_pos hc, min_eq_right hfit] at hn
  omega

theorem finalWidth_narrow_threshold (hm : 2 ≤ m) (heven : 2 * (L / 2) = L)
    (history : List (LayerRecord jobs (m * L))) (j : Fin jobs) (p : ℕ)
    (S : Assignment (vertices := jobs * (m * L))) (t : ℕ)
    (hbalance : narrowCount history j ≤ wideCount m history j)
    (hprefix : p = (2 * m - 1) * wideCount m history j + narrowCount history j)
    (hquota : wideCount m history j < L / 2)
    (hn : finalWidth m L history j p S t = 1) :
    (2 * m - 1) * (L - t % L) ≤ epochWideWork m L history j S t := by
  have hc := finalWidth_narrow_implies_not_choose hm heven history j p S t hbalance hprefix hn
  by_contra hh
  exact hc ⟨hquota, Or.inr (Or.inr (by omega))⟩

theorem finalWidth_wide_threshold (hm : 2 ≤ m) (hL : 0 < L)
    (history : List (LayerRecord jobs work)) (j : Fin jobs) (p : ℕ)
    (S : Assignment (vertices := jobs * work)) (t : ℕ)
    (hbalance : narrowCount history j ≤ wideCount m history j)
    (hcredit : BatchedForcing.ThresholdCredit (2 * m - 1) (L - t % L)
      (wideCount m history j) (narrowCount history j) (epochWideWork m L history j S t))
    (hfull : ¬ IdleEarlier m L S t)
    (hw : finalWidth m L history j p S t = 2 * m - 1) :
    epochWideWork m L history j S t < (2 * m - 1) * (L - t % L) := by
  have hc := finalWidth_wide_implies_choose hm history j p S t hw
  apply hcredit.wide_below (by omega) (by have := Nat.mod_lt t hL; omega) hbalance
  rcases hc.2 with hg | hi | hx
  · exact Or.inl hg
  · exact False.elim (hfull hi)
  · exact Or.inr hx

end Scheduling.BatchedAdversary
