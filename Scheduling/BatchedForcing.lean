import Scheduling.BatchedAggregate

namespace Scheduling.BatchedAdversary
open Finset LayeredPrefix
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs m L c : ℕ}

theorem full_epoch_passivity (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records)
    (hflow : (Q.toInstance L (Nat.mul_pos (by omega) hL)).FlowBound
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) (c * L)) (i : ℕ)
    (hfull : ∀ t, i * L ≤ t → t < (i + 1) * L →
      (univ.filter (fun v => A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)) v = t)).card = m) :
    ∃ ds : List ℕ, ds.length ≤ c ∧ BatchedForcing.PassivityBounds m c (L :: ds) := by
  let I := Q.toInstance L (Nat.mul_pos (by omega) hL)
  let S := A.schedule I
  obtain ⟨T, hT⟩ := full_epoch_job_cutoffs hm hL heven A h i hfull
  apply cutoffs_passivity records S i c (I.alive S (i * L)) T hT
    (I.regular_alive_card_le hL (by intros; rfl) hflow i)
  · intro v _ hlo hhi
    have hr := I.regular_epoch_no_arrivals (i := i) (A.valid I) hL (by intros; rfl) v hhi
    exact mem_filter.mpr ⟨mem_univ _, hr, v, rfl, hlo⟩
  · intro u hlo _
    exact full_epoch_wide_lower hm hL heven A h hflow hlo le_rfl
      (by intro t ht; exact hfull t (hlo.trans (mem_Ico.mp ht).1) (mem_Ico.mp ht).2)

/-- In the actual threshold construction, the geometric epoch length
forces an idle slot in every epoch under the small-flow hypothesis. -/
theorem forcing_epoch_deficit (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (hc : 0 < c) (hcm : 2 * c ≤ m) (hscale : L = 8 * c * 5 ^ c)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records)
    (hflow : (Q.toInstance L (Nat.mul_pos (by omega) hL)).FlowBound
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) (c * L)) (i : ℕ) :
    (Q.toInstance L (Nat.mul_pos (by omega) hL)).epochWork
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) L i < m * L := by
  let I := Q.toInstance L (Nat.mul_pos (by omega) hL)
  let S := A.schedule I
  by_contra hnot
  have hfull : ∀ t, i * L ≤ t → t < (i + 1) * L →
      (univ.filter (fun v => S v = t)).card = m := by
    intro t hlo hhi
    have hcap := (A.valid I).capacity t
    change (univ.filter (fun v => S v = t)).card ≤ m at hcap
    by_contra hne
    have hidle : (univ.filter (fun v => S v = t)).card < m := by omega
    exact hnot (I.epochWork_lt_of_idle (A.valid I) hL (mem_Ico.mpr ⟨hlo, hhi⟩) hidle)
  obtain ⟨ds, hlen, hb⟩ := full_epoch_passivity hm hL heven A h hflow i hfull
  apply BatchedForcing.no_full_epoch (by omega) hc hcm hlen
  simpa only [← hscale] using hb

theorem flow_lower (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (hc : 0 < c) (hcm : 2 * c ≤ m) (hscale : L = 8 * c * 5 ^ c)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) (hn : jobs = c * (m * L)) :
    c * L ≤ (Q.toInstance L (Nat.mul_pos (by omega) hL)).maxFlow
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) := by
  let I := Q.toInstance L (Nat.mul_pos (by omega) hL)
  apply I.regular_every_epoch_flow_lower (by omega) hL hc hn (A.valid I) (by intros; rfl)
    (fun j => Q.jobVertices_card L _ j)
  intro hflow i _
  exact forcing_epoch_deficit hm hL heven hc hcm hscale A h hflow i

end Scheduling.BatchedAdversary
