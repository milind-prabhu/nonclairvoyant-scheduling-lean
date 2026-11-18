import Scheduling.LayerCount
import Scheduling.KeyOrder

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

noncomputable def recordedKeys {jobs work : ℕ} (records : List (LayerRecord jobs work))
    (j : Fin jobs) : Finset (Fin work) :=
  (records.filter (fun r => r.owner = j)).toFinset.image LayerRecord.key

theorem recordedKeys_card_le {jobs work : ℕ} (records : List (LayerRecord jobs work)) (j : Fin jobs) :
    (recordedKeys records j).card ≤ (records.filter (fun r => r.owner = j)).length :=
  (card_image_le).trans (List.toFinset_card_le _)

namespace LayeredPrefix
variable {jobs work : ℕ}

theorem jobVertices_card (P : LayeredPrefix jobs work) (L : ℕ) (hw : 0 < work) (j : Fin jobs) :
    ((P.toInstance L hw).jobVertices j).card = work := by
  let F : LayeredForest jobs work := {
    depth := fun _ => 1
    depth_pos := by intros; omega
    depth_le := by intros; omega
    leafLevel := fun _ _ => 0 }
  exact F.jobVertices_card L j

theorem RecordedRun.parent_is_key {m L : ℕ} {hm : 0 < m} {hw : 0 < work}
    {A : DeterministicScheduler m} {rule : LayerSizeRule jobs work}
    {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule (initial m hm) Q records)
    (j : Fin jobs) (v u : Fin work) (hp : Q.parent j v = some u) : u ∈ recordedKeys records j := by
  rcases h.parent_origins j v u hp with hnone | ⟨r, hr, ho, hk⟩
  · simp [initial] at hnone
  · apply mem_image.mpr
    exact ⟨r, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hr, decide_eq_true ho⟩), hk⟩

theorem RecordedRun.edge_from_key {m L : ℕ} {hm : 0 < m} {hw : 0 < work}
    {A : DeterministicScheduler m} {rule : LayerSizeRule jobs work}
    {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule (initial m hm) Q records)
    {u v : Fin (jobs * work)} (he : (Q.toInstance L hw).edge u v) :
    position u ∈ recordedKeys records (job u) := by
  have hv : (position v).val < Q.boundary (job v) := by
    have := (position v).isLt
    simp only [boundary, h.completion.finished]
    omega
  have hp := he.2
  rw [if_pos hv] at hp
  rw [he.1]
  exact h.parent_is_key _ _ _ hp

/-- The extracted adversarial forest has a valid two-epoch offline
schedule. Its key-first ordering is constructed from the actual recorded
keys, rather than supplied as an unproved scheduling witness. -/
theorem RecordedRun.offline_schedule {m L c : ℕ} {hm : 0 < m} {hwpos : 0 < work}
    {A : DeterministicScheduler m} {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hwpos A (forcingLayerRule jobs work m c L hm)
      (initial m hm) Q records)
    (hm2 : 2 ≤ m) (hw : work = m * L) (hhalf : 2 * (L / 2) = L) :
    ∃ O, (Q.toInstance L hwpos).Valid m O ∧ (Q.toInstance L hwpos).FlowBound O (2 * L) := by
  let I := Q.toInstance L hwpos
  let pos := fun v : Fin (jobs * work) => keyFirstPosition (recordedKeys records (job v)) (position v)
  have hpos : ∀ v, pos v < m * L := by
    intro v
    exact (keyFirstPosition_lt _ _).trans_eq hw
  have hinj : Function.Injective (fun v => (I.owner v, pos v)) := by
    intro u v he
    have ho : job u = job v := congrArg (fun p : Fin jobs × ℕ => p.1) he
    have hp : pos u = pos v := congrArg (fun p : Fin jobs × ℕ => p.2) he
    dsimp only [pos] at hp
    rw [ho] at hp
    have hv := keyFirstPosition_injective (recordedKeys records (job v)) hp
    exact LayeredForest.coordinates_injective (Prod.ext ho (congrArg Fin.val hv))
  have hedge : ∀ u v, I.edge u v → pos u < L ∧ pos u < pos v := by
    intro u v he
    have hu := h.edge_from_key he
    have hcard := (recordedKeys_card_le records (job u)).trans (h.forcing_layer_count hw hhalf (job u))
    refine ⟨(keyFirstPosition_key_lt _ _ hu).trans_le hcard, ?_⟩
    have ho := I.same_job he
    change job u = job v at ho
    change keyFirstPosition (recordedKeys records (job u)) (position u) <
      keyFirstPosition (recordedKeys records (job v)) (position v)
    rw [← ho]
    exact keyFirstPosition_edge _ hu (I.rank_increases he)
  refine ⟨fun v => pipelineTime m L (I.owner v).val (pos v), ?_, ?_⟩
  · exact I.pipeline_valid hm2 pos hpos hinj (by intros; rfl) hedge
  · exact I.pipeline_flowBound hm2 pos hpos (by intros; rfl)

theorem RecordedRun.optimum_bounds {m L c : ℕ} {hm : 0 < m} {hwpos : 0 < work}
    {A : DeterministicScheduler m} {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hwpos A (forcingLayerRule jobs work m c L hm)
      (initial m hm) Q records)
    (hm2 : 2 ≤ m) (hj : 0 < jobs) (hw : work = m * L) (hhalf : 2 * (L / 2) = L) :
    L ≤ (Q.toInstance L hwpos).optimum m hm ∧ (Q.toInstance L hwpos).optimum m hm ≤ 2 * L := by
  obtain ⟨O, hO, hflow⟩ := (Q.toInstance L hwpos).optimum_attained hm
  have hwork := (Q.toInstance L hwpos).job_work_bound hO hflow ⟨0, hj⟩
  rw [Q.jobVertices_card] at hwork
  refine ⟨Nat.le_of_mul_le_mul_left (hw.symm.le.trans hwork) hm, ?_⟩
  obtain ⟨S, hS, hb⟩ := h.offline_schedule hm2 hw hhalf
  exact (Q.toInstance L hwpos).optimum_le hm hS hb

end LayeredPrefix
end Scheduling
