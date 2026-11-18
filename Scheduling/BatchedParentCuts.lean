import Scheduling.BatchedLayerBudget
import Scheduling.RecordedKeys
import Scheduling.KeyPrefix

namespace Scheduling.BatchedAdversary
open Finset
open LayeredPrefix
attribute [local instance] Classical.propDecidable
variable {jobs m L : ℕ}

theorem budget_prefix_work (hm : 2 ≤ m)
    (history : List (LayerRecord jobs (m * L))) (P : LayeredPrefix jobs (m * L))
    (hb : Budget m L history P)
    (hwidth : ∀ r ∈ history, r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1)
    (j : Fin jobs) : m * (history.filter (fun r => r.owner = j)).length ≤ P.closed j := by
  rw [job_count_eq hm history hwidth j, (hb j).2.2.1]
  have hmul := Nat.mul_le_mul_left (m - 1) (hb j).2.1
  have hbval : 2 * m - 1 = (m - 1) + m := by omega
  have hmval : m = (m - 1) + 1 := by omega
  rw [hbval]
  calc
    m * (wideCount m history j + narrowCount history j) =
        m * wideCount m history j + (m - 1) * narrowCount history j + narrowCount history j := by
          have he := congrArg (fun x : ℕ => x * narrowCount history j) hmval
          nlinarith
    _ ≤ m * wideCount m history j + (m - 1) * wideCount m history j + narrowCount history j := by omega
    _ = _ := by ring

theorem budget_record_width (hm : 2 ≤ m) (hL : 0 < L)
    (A : DeterministicScheduler m) (history : List (LayerRecord jobs (m * L)))
    (P : LayeredPrefix jobs (m * L)) (hb : Budget m L history P)
    (j : Fin jobs) (key : Fin (m * L))
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j) :
    let r := P.record (L := L) (Nat.mul_pos (by omega) hL) A j key
    r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1 := by
  have hs := (hb j).2.2.2
  rcases hs with ⟨hz, _⟩ | ⟨hw, _⟩ | ⟨hn, _⟩
  · have he : P.boundary j = P.closed j := by simp only [boundary, hz, Nat.add_zero]
    omega
  · left; simpa only [record, boundary, Nat.add_sub_cancel_left] using hw
  · right; simpa only [record, boundary, Nat.add_sub_cancel_left] using hn

/-- Every parent edge introduced by the construction crosses a balanced
prefix boundary. Later records have no keys before that boundary. -/
theorem history_parent_cut (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {history records : List (LayerRecord jobs (m * L))}
    {P Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) history P Q records)
    (hb : Budget m L history P)
    (hwidth : ∀ r ∈ history, r.stop - r.start = 2 * m - 1 ∨ r.stop - r.start = 1) :
    ∀ j (v u : Fin (m * L)), Q.parent j v = some u →
      P.parent j v = some u ∨ ∃ p n, u.val < p ∧ p ≤ v.val ∧ m * n ≤ p ∧
        ((recordedKeys (history ++ records) j).filter (fun k => k.val < p)).card ≤ n := by
  induction h with
  | done history P hd => intro j v u hp; exact Or.inl hp
  | step history P Q j key hk hmax hearliest records tail ih =>
    let hw : 0 < m * L := Nat.mul_pos (by omega) hL
    let r := P.record (L := L) hw A j key
    let next := history ++ [r]
    let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1
    let q := (rule jobs m L hm hL A).size next P j t
    let R := P.advance j key hk q ((rule jobs m L hm hL A).fits _ _ _ _)
      ((rule jobs m L hm hL A).positive _ _ _ _)
    have hn : Budget m L next R := budget_advance hm hL heven A history P hb j key hk
    have hnext : ∀ s ∈ next, s.stop - s.start = 2 * m - 1 ∨ s.stop - s.start = 1 := by
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hwidth s hs
      · have he : s = r := List.mem_singleton.mp hs
        subst s
        exact budget_record_width hm hL A history P hb j key hk
    obtain ⟨staticRule, hr⟩ := tail.flexible.recorded
    intro i v u hp
    rcases ih hn hnext i v u hp with hprev | hcut
    · change (if i = j ∧ P.boundary j ≤ v.val ∧ v.val < P.boundary j + q then some key
        else P.parent i v) = some u at hprev
      split_ifs at hprev with hnew
      · have hkey : key = u := Option.some.inj hprev
        obtain ⟨hij, hvlo, hvhi⟩ := hnew
        subst i
        refine Or.inr ⟨P.boundary j, (next.filter (fun r => r.owner = j)).length, ?_, hvlo, ?_, ?_⟩
        · simpa only [hkey] using hk.2
        · have hh := budget_prefix_work hm next R hn hnext j
          simpa only [R, advance_closed] using hh
        · have hh := recordedKeys_prefix_le next records j (by
            intro k hkey
            have hl := hr.keys_lower j k hkey
            simpa only [advance_closed] using hl)
          simpa only [next, r, List.append_assoc, List.singleton_append] using hh
      · exact Or.inl hprev
    · right
      simpa only [next, r, List.append_assoc, List.singleton_append] using hcut

end Scheduling.BatchedAdversary
