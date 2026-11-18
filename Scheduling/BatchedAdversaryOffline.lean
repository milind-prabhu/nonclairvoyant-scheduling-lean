import Scheduling.BatchedParentCuts

namespace Scheduling.BatchedAdversary
open Finset
open LayeredForest (job position)
open LayeredPrefix
attribute [local instance] Classical.propDecidable
variable {jobs m L : ℕ}

/-- The one-epoch offline schedule for the actual fixed graph produced
by the history-dependent threshold construction. -/
theorem offline_schedule (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) :
    ∃ O, (Q.toInstance L (Nat.mul_pos (by omega) hL)).Valid m O ∧
      (Q.toInstance L (Nat.mul_pos (by omega) hL)).FlowBound O L := by
  let hw : 0 < m * L := Nat.mul_pos (by omega) hL
  let I := Q.toInstance L hw
  obtain ⟨staticRule, hr⟩ := h.flexible.recorded
  have hcard : ∀ j, (recordedKeys records j).card = L := by
    intro j
    rw [hr.keys_card]
    exact final_job_length hm hL heven A h j
  have hparent : ∀ u v, I.edge u v → Q.parent (job v) (position v) = some (position u) := by
    intro u v he
    have hpos : (position v).val < Q.boundary (job v) := by
      have hlt := (position v).isLt
      simp only [boundary, hr.completion.finished]
      omega
    have hp := he.2
    rwa [if_pos hpos] at hp
  have hsource : ∀ u v, I.edge u v → position u ∈ recordedKeys records (job v) := by
    intro u v he
    rcases hr.parent_origins _ _ _ (hparent u v he) with hnone | ⟨r, hr', ho, hk⟩
    · simp [initial] at hnone
    · exact mem_image.mpr ⟨r, List.mem_toFinset.mpr
        (List.mem_filter.mpr ⟨hr', decide_eq_true ho⟩), hk⟩
  let pos := fun v : Fin (jobs * (m * L)) => keyFirstPosition (recordedKeys records (job v)) (position v)
  have hpos : ∀ v, pos v < m * L := fun v => keyFirstPosition_lt _ _
  have hinj : Function.Injective (fun v => (I.owner v, pos v)) := by
    intro u v he
    have ho : job u = job v := congrArg (fun p : Fin jobs × ℕ => p.1) he
    have hp : pos u = pos v := congrArg (fun p : Fin jobs × ℕ => p.2) he
    dsimp only [pos] at hp
    rw [ho] at hp
    have hv := keyFirstPosition_injective (recordedKeys records (job v)) hp
    exact LayeredForest.coordinates_injective (Prod.ext ho (congrArg Fin.val hv))
  have hedge : ∀ u v, I.edge u v → pos u < L ∧
      (if pos v < L then pos u < pos v else (pos u + 1) * (m - 1) ≤ pos v - L) := by
    intro u v he
    have ho : job u = job v := he.1
    have hu := hsource u v he
    have hup : pos u < L := by
      dsimp only [pos]
      rw [ho]
      exact (keyFirstPosition_key_lt _ _ hu).trans_eq (hcard (job v))
    refine ⟨hup, ?_⟩
    by_cases hv : pos v < L
    · rw [if_pos hv]
      dsimp only [pos]
      rw [ho]
      exact keyFirstPosition_edge _ hu (I.rank_increases he)
    · rw [if_neg hv]
      have hvkey : position v ∉ recordedKeys records (job v) := by
        intro hh
        have hb := keyFirstPosition_key_lt _ _ hh
        rw [hcard] at hb
        exact hv hb
      have hcut := history_parent_cut hm hL heven A h (initial_budget hm hL heven)
        (by simp) (job v) (position v) (position u) (hparent u v he)
      simp only [List.nil_append] at hcut
      rcases hcut with hnone | ⟨p, n, hpu, hpv, hwork, hkeys⟩
      · simp [initial] at hnone
      · dsimp only [pos]
        rw [ho]
        simpa only [hcard] using
          keyFirstPosition_leaf_after_cut (by omega : 0 < m) _ _ _ hu hvkey hpu hpv hwork hkeys
  refine ⟨fun v => batchedTime m L (I.owner v).val (pos v), ?_, ?_⟩
  · exact I.batched_valid hm pos hpos hinj (by intros; rfl) hedge
  · exact I.batched_flowBound hm pos hpos (by intros; rfl)

theorem optimum_eq (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (hj : 0 < jobs) (A : DeterministicScheduler m)
    {records : List (LayerRecord jobs (m * L))} {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) :
    (Q.toInstance L (Nat.mul_pos (by omega) hL)).optimum m (by omega) = L := by
  let I := Q.toInstance L (Nat.mul_pos (by omega) hL)
  have hm0 : 0 < m := by omega
  obtain ⟨O, hO, hflow⟩ := offline_schedule hm hL heven A h
  apply Nat.le_antisymm (I.optimum_le hm0 hO hflow)
  obtain ⟨P, hP, hp⟩ := I.optimum_attained hm0
  have hwork := I.job_work_bound hP hp ⟨0, hj⟩
  rw [Q.jobVertices_card] at hwork
  exact Nat.le_of_mul_le_mul_left hwork hm0

end Scheduling.BatchedAdversary
