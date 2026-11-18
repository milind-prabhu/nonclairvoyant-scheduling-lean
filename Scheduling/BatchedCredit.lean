import Scheduling.BatchedForcingArithmetic

namespace Scheduling.BatchedForcing

/-- Before passivity, completed wide work is covered by the surplus of
wide layers. After passivity, that surplus covers every remaining slot.
Here `d` is the remaining length of the current epoch. -/
def ThresholdCredit (b d w n x : ℕ) : Prop :=
  x ≤ b * (w - n) ∨ (b * d ≤ x ∧ d ≤ w - n)

theorem ThresholdCredit.first_wide {b d w n x : ℕ} (hbalance : n ≤ w) (hx : x ≤ b) :
    ThresholdCredit b d (w + 1) n x := by
  left
  have hs : 1 ≤ w + 1 - n := by omega
  have hh := Nat.mul_le_mul_left b hs
  omega

theorem ThresholdCredit.first_narrow {b d w n : ℕ} : ThresholdCredit b d w n 0 := by
  left
  omega

/-- Even when a wide layer is permitted by the prefix guard, the work
counter is below the passivity threshold. Thus the guard does not restart
wide service after passivity. -/
theorem ThresholdCredit.wide_below {b d w n x : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbalance : n ≤ w) (hcredit : ThresholdCredit b d w n x)
    (hchoose : w ≤ n ∨ x < b * d) : x < b * d := by
  rcases hchoose with hguard | hx
  · have he : w - n = 0 := by omega
    rcases hcredit with ha | hp
    · rw [he, Nat.mul_zero] at ha
      have hbd := Nat.mul_pos hb hd
      omega
    · rw [he] at hp
      omega
  · exact hx

theorem ThresholdCredit.wide_step {b d d' w n x x' : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbalance : n ≤ w) (hcredit : ThresholdCredit b d w n x)
    (hchoose : w ≤ n ∨ x < b * d) (hwork : x' ≤ x + b) :
    ThresholdCredit b d' (w + 1) n x' := by
  have hsmall := hcredit.wide_below hb hd hbalance hchoose
  have ha : x ≤ b * (w - n) := hcredit.resolve_right (by intro h; omega)
  have hs : w + 1 - n = (w - n) + 1 := by omega
  left
  rw [hs, Nat.mul_add, Nat.mul_one]
  omega

theorem ThresholdCredit.narrow_step {b d d' w n x : ℕ} (hb : 0 < b)
    (hbalance : n ≤ w) (hcredit : ThresholdCredit b d w n x)
    (hthreshold : b * d ≤ x) (htime : d' + 1 ≤ d) :
    ThresholdCredit b d' w (n + 1) x := by
  have hsurplus : d ≤ w - n := by
    rcases hcredit with ha | hp
    · exact Nat.le_of_mul_le_mul_left (hthreshold.trans ha) hb
    · exact hp.2
  right
  refine ⟨?_, ?_⟩
  · exact (Nat.mul_le_mul_left b (show d' ≤ d by omega)).trans hthreshold
  · omega

/-- A trace of completed layers within one epoch. The counter can rise
by at most one layer's width at a wide completion and cannot rise at a
narrow completion. Time advances by at least one slot per layer. -/
inductive CreditTrace (b : ℕ) : ℕ → ℕ → ℕ → ℕ → Prop
  | initial (d w n x : ℕ) (hbalance : n ≤ w) (hcredit : ThresholdCredit b d w n x) :
      CreditTrace b d w n x
  | wide {d w n x : ℕ} (prev : CreditTrace b d w n x)
      (d' x' : ℕ) (htime : d' < d) (hchoose : w ≤ n ∨ x < b * d)
      (hwork : x' ≤ x + b) : CreditTrace b d' (w + 1) n x'
  | narrow {d w n x : ℕ} (prev : CreditTrace b d w n x)
      (d' : ℕ) (htime : d' < d) (hthreshold : b * d ≤ x) :
      CreditTrace b d' w (n + 1) x

theorem CreditTrace.credit {b d w n x : ℕ} (hb : 0 < b) (h : CreditTrace b d w n x) :
    n ≤ w ∧ ThresholdCredit b d w n x := by
  induction h with
  | initial d w n x hbalance hcredit => exact ⟨hbalance, hcredit⟩
  | wide prev d' x' htime hchoose hwork ih =>
    exact ⟨by omega, ih.2.wide_step hb (by omega) ih.1 hchoose hwork⟩
  | @narrow d w n x prev d' htime hthreshold ih =>
    have hs : d ≤ w - n := by
      rcases ih.2 with ha | hp
      · exact Nat.le_of_mul_le_mul_left (hthreshold.trans ha) hb
      · exact hp.2
    exact ⟨by omega, ih.2.narrow_step hb ih.1 hthreshold (by omega)⟩

end Scheduling.BatchedForcing
