import Scheduling.BatchedFrontierCredit

namespace Scheduling.BatchedAdversary
open Finset LayeredPrefix
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs m L : ℕ}

/-- A reveal time for an actual layer, including its prefix budget and
the credit certificate computed from the final schedule. -/
structure RecordCredit (m L : ℕ) (history : List (LayerRecord jobs (m * L)))
    (r : LayerRecord jobs (m * L)) (S : Assignment (vertices := jobs * (m * L))) (e : ℕ) : Prop where
  before_completion : e ≤ r.time
  layer_after : ∀ v, job v = r.owner → r.start ≤ (position v).val →
    (position v).val < r.stop → e ≤ S v
  reveal : RevealCredit m L history r.owner S e (r.stop - r.start)
  balance : narrowCount history r.owner ≤ wideCount m history r.owner
  wide_quota : r.stop - r.start = 2 * m - 1 → wideCount m history r.owner < L / 2

theorem RecordCredit.wide_below (hm : 2 ≤ m) (hL : 0 < L)
    {history : List (LayerRecord jobs (m * L))} {r : LayerRecord jobs (m * L)}
    {S : Assignment (vertices := jobs * (m * L))} {e : ℕ}
    (h : RecordCredit m L history r S e) (hw : r.stop - r.start = 2 * m - 1)
    (hfull : ¬ IdleEarlier m L S e) :
    epochWideWork m L history r.owner S e < (2 * m - 1) * (L - e % L) := by
  have hc := h.reveal.credit hfull (h.wide_quota hw)
  apply hc.wide_below (by omega) (by have := Nat.mod_lt e hL; omega) h.balance
  rcases h.reveal.wide_choice hw with hg | hi | hx
  · exact Or.inl hg
  · exact False.elim (hfull hi)
  · exact Or.inr hx

/-- Every later layer is revealed strictly after the execution of an
earlier wide layer's key. This follows from the concrete completed-work
certificate, even when other jobs' records occur between the layers. -/
theorem RecordCredit.after_wide_key
    {history : List (LayerRecord jobs (m * L))} {r s : LayerRecord jobs (m * L)}
    {S : Assignment (vertices := jobs * (m * L))} {e : ℕ}
    (h : RecordCredit m L history s S e) (hr : r ∈ history) (ho : r.owner = s.owner)
    (hw : r.stop - r.start = 2 * m - 1)
    (hk : r.start ≤ r.key.val ∧ r.key.val < r.stop)
    (ht : S (finProdFinEquiv (r.owner, r.key)) = r.time) : r.time < e := by
  have hh := h.reveal.closed_before (finProdFinEquiv (r.owner, r.key))
    ⟨(LayeredForest.job_pair r.owner r.key).trans ho, r, hr, ho, hw, by
      simpa only [LayeredForest.position_pair] using hk⟩
  rwa [ht] at hh

theorem history_record_credit (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {history records : List (LayerRecord jobs (m * L))}
    {P Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) history P Q records)
    (hb : Budget m L history P)
    (hc : FrontierCredit m L history P (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)))) :
    ∀ before r after, records = before ++ r :: after →
      ∃ e, RecordCredit m L (history ++ before) r
        (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) e := by
  induction h with
  | done history P hd =>
    intro before r after he
    have hh := congrArg List.length he
    simp only [List.length_nil, List.length_append, List.length_cons] at hh
    omega
  | step history P Q j key hk hmax hearliest records tail ih =>
    intro before r after heq
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨hr, ht⟩ := heq
      subst r
      subst after
      simp only [List.append_nil]
      obtain ⟨e, he, hcredit⟩ := hc j
      refine ⟨e, ?_⟩
      have hfull := HistoryRun.step history P Q j key hk hmax hearliest records tail
      obtain ⟨staticRule, hrun⟩ := hfull.flexible.recorded
      have htimes := hrun.final_times _ List.mem_cons_self
      refine ⟨?_, ?_, ?_, (hb j).2.1, ?_⟩
      · have hkey := he (finProdFinEquiv (j, key)) (by
          apply mem_filter.mpr
          exact ⟨mem_univ _, LayeredForest.job_pair j key, by
            simpa only [LayeredForest.position_pair] using hk⟩)
        exact hkey.trans_eq htimes.2.2.2.1
      · intro v ho hlo hhi
        exact he v (mem_filter.mpr ⟨mem_univ _, ho, hlo, hhi⟩)
      · simpa only [record, boundary, Nat.add_sub_cancel_left] using hcredit
      · intro hw
        have hw' : P.width j = 2 * m - 1 := by
          simpa only [record, boundary, Nat.add_sub_cancel_left] using hw
        rcases (hb j).2.2.2 with ⟨hz, _⟩ | ⟨_, hquota⟩ | ⟨hn, _⟩
        · omega
        · exact hquota
        · omega
    | cons a before =>
      simp only [List.cons_append, List.cons.injEq] at heq
      have hb' := budget_advance hm hL heven A history P hb j key hk
      have hc' := frontierCredit_advance hm hL heven A history P Q j key hk hmax hearliest
        records tail hb hc
      obtain ⟨e, he⟩ := ih hb' hc' before r after heq.2
      refine ⟨e, ?_⟩
      rw [← heq.1]
      simpa only [List.append_assoc, List.singleton_append] using he

/-- Every actual layer of the adaptive construction has a reveal-time
credit certificate. In particular, the prefix guard cannot choose a
wide layer above the passivity threshold during a full epoch. -/
theorem initial_record_credit (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) :
    ∀ before r after, records = before ++ r :: after →
      ∃ e, RecordCredit m L before r
        (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) e := by
  have hc := initial_frontierCredit hm hL heven
    (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)))
    (A.valid (Q.toInstance L (Nat.mul_pos (by omega) hL))).release
  simpa only [List.nil_append] using history_record_credit hm hL heven A h
    (initial_budget hm hL heven) hc

end Scheduling.BatchedAdversary
