import Scheduling.FlexibleLayers

namespace Scheduling.BatchedAdversary
open Finset
open LayeredForest (job position)
open LayeredPrefix
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ}

def wideCount (m : ℕ) (history : List (LayerRecord jobs work)) (j : Fin jobs) : ℕ :=
  (history.filter (fun r => r.owner = j ∧ r.stop - r.start = 2 * m - 1)).length

def narrowCount (history : List (LayerRecord jobs work)) (j : Fin jobs) : ℕ :=
  (history.filter (fun r => r.owner = j ∧ r.stop - r.start = 1)).length

/-- All vertices of completed wide layers, identified by their original
local labels. The execution-time filter below counts only service in the
current epoch, even when a layer straddles its boundary. -/
def WideRecorded (m : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) (v : Fin (jobs * work)) : Prop :=
  job v = j ∧ ∃ r ∈ history, r.owner = j ∧ r.stop - r.start = 2 * m - 1 ∧
    r.start ≤ (position v).val ∧ (position v).val < r.stop

noncomputable def epochWideWork (m L : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (t : ℕ) : ℕ :=
  (univ.filter (fun v => WideRecorded m history j v ∧ (t / L) * L ≤ S v ∧ S v < t)).card

def IdleEarlier (m L : ℕ) (S : Assignment (vertices := jobs * work)) (t : ℕ) : Prop :=
  ∃ u, (t / L) * L ≤ u ∧ u < t ∧ (univ.filter (fun v => S v = u)).card < m

/-- The intended threshold rule, with explicit budget and prefix guards.
The guards make the rule total; the forcing analysis must show that the
prefix guard never overrides a passive job during a full epoch. -/
def ChooseWide (m L : ℕ) (history : List (LayerRecord jobs work))
    (j : Fin jobs) (S : Assignment (vertices := jobs * work)) (t : ℕ) : Prop :=
  wideCount m history j < L / 2 ∧
    (wideCount m history j ≤ narrowCount history j ∨ IdleEarlier m L S t ∨
      epochWideWork m L history j S t < (2 * m - 1) * (L - t % L))

noncomputable def rule (jobs m L : ℕ) (hm : 2 ≤ m) (hL : 0 < L)
    (A : DeterministicScheduler m) : HistoryLayerRule jobs (m * L) where
  size history P j t := min (m * L - P.boundary j)
    (if ChooseWide m L history j
      (A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL))) t then 2 * m - 1 else 1)
  fits := by
    intro history P j t
    have hh := min_le_left (m * L - P.boundary j)
      (if ChooseWide m L history j
        (A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL))) t then 2 * m - 1 else 1)
    have hb := P.fits j
    change P.boundary j ≤ m * L at hb
    omega
  positive := by
    intro history P j t hp
    apply lt_min (by omega)
    split_ifs <;> omega

def initial (jobs m L : ℕ) (hm : 2 ≤ m) : LayeredPrefix jobs (m * L) where
  closed _ := 0
  width _ := min (2 * m - 1) (m * L)
  fits _ := by simp
  frontier_pos := by intro j hp; exact lt_min (by omega) hp
  parent _ _ := none
  parent_lt := by intros; contradiction

/-- Once the completed-layer counts respect their budgets, the total
rule never truncates a layer: it chooses a whole wide or narrow layer,
and preserves the prefix condition, or returns zero at the exact end. -/
theorem rule_width_shape (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) (history : List (LayerRecord jobs (m * L)))
    (P : LayeredPrefix jobs (m * L)) (j : Fin jobs) (t : ℕ)
    (hwide : wideCount m history j ≤ L / 2)
    (hnarrow : narrowCount history j ≤ wideCount m history j)
    (hprefix : P.boundary j = (2 * m - 1) * wideCount m history j + narrowCount history j) :
    ((rule jobs m L hm hL A).size history P j t = 0 ∧ P.boundary j = m * L) ∨
    ((rule jobs m L hm hL A).size history P j t = 2 * m - 1 ∧ wideCount m history j < L / 2) ∨
    ((rule jobs m L hm hL A).size history P j t = 1 ∧ narrowCount history j < wideCount m history j) := by
  let W := wideCount m history j
  let N := narrowCount history j
  let S := A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL))
  have htotal : (2 * m - 1) * (L / 2) + L / 2 = m * L := by
    have hb : 2 * m - 1 + 1 = 2 * m := by omega
    nlinarith
  by_cases hend : P.boundary j = m * L
  · exact Or.inl ⟨by simp only [rule, hend, Nat.sub_self, min_eq_left (Nat.zero_le _)], hend⟩
  · have hremaining : P.boundary j < m * L := lt_of_le_of_ne (P.fits j) hend
    by_cases hchoose : ChooseWide m L history j S t
    · have hw : W < L / 2 := hchoose.1
      have hn : N ≤ L / 2 := hnarrow.trans hwide
      have hmul := Nat.mul_le_mul_left (2 * m - 1) (show W + 1 ≤ L / 2 by omega)
      have hfit : 2 * m - 1 ≤ m * L - P.boundary j := by
        change P.boundary j = (2 * m - 1) * W + N at hprefix
        have hsum : P.boundary j + (2 * m - 1) ≤ m * L := by nlinarith
        omega
      refine Or.inr (Or.inl ⟨?_, hw⟩)
      change min (m * L - P.boundary j) (if ChooseWide m L history j S t then 2 * m - 1 else 1) = _
      rw [if_pos hchoose, min_eq_right hfit]
    · have hn : N < W := by
        by_contra hh
        have hsame : N = W := by change N ≤ W at hnarrow; omega
        have hw : W = L / 2 := by
          by_contra hw'
          have hlt : W < L / 2 := by change W ≤ L / 2 at hwide; omega
          exact hchoose ⟨hlt, Or.inl (by change W ≤ N; omega)⟩
        change P.boundary j = (2 * m - 1) * W + N at hprefix
        rw [hsame, hw] at hprefix
        omega
      refine Or.inr (Or.inr ⟨?_, hn⟩)
      change min (m * L - P.boundary j) (if ChooseWide m L history j S t then 2 * m - 1 else 1) = _
      rw [if_neg hchoose, min_eq_right (by omega)]

/-- The threshold construction has a finite fixed outcome, with both
the actual history-dependent choices and the generic key-last trace
available for further analysis. This is not yet the forcing theorem. -/
theorem exists_candidate (jobs m L : ℕ) (hm : 2 ≤ m) (hL : 0 < L)
    (A : DeterministicScheduler m) :
    ∃ Q records,
      HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
        (initial jobs m L hm) Q records ∧
      (∃ staticRule, RecordedRun (L := L) (Nat.mul_pos (by omega) hL) A staticRule
        (initial jobs m L hm) Q records) ∧
      (∀ u v w, (Q.toInstance L (Nat.mul_pos (by omega) hL)).edge u w →
        (Q.toInstance L (Nat.mul_pos (by omega) hL)).edge v w → u = v) := by
  obtain ⟨Q, records, hh, staticRule, hr⟩ :=
    exists_history_certificates (rule jobs m L hm hL A) (initial jobs m L hm)
      (Nat.mul_pos (by omega) hL) A L
  exact ⟨Q, records, hh, ⟨staticRule, hr⟩, fun _ _ _ hu hv => hr.completion.outForest hu hv⟩

end Scheduling.BatchedAdversary
