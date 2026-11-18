import Scheduling.OfflinePipeline

namespace Scheduling
open Finset

/-- Keys occupy positions `0,...,depth-1` in each job. Every other vertex
is a leaf assigned to one of those layers. The identifiers here describe
the offline instance; an online adversary may relabel them. -/
structure LayeredForest (jobs work : ℕ) where
  depth : Fin jobs → ℕ
  depth_pos : ∀ j, 0 < depth j
  depth_le : ∀ j, depth j ≤ work
  leafLevel : (j : Fin jobs) → Fin work → Fin (depth j)

namespace LayeredForest
variable {jobs work : ℕ} (F : LayeredForest jobs work)

def level (j : Fin jobs) (k : Fin work) : ℕ :=
  if k.val < F.depth j then k.val else (F.leafLevel j k).val

theorem level_lt (j : Fin jobs) (k : Fin work) : F.level j k < F.depth j := by
  unfold level
  split_ifs with h
  · exact h
  · exact (F.leafLevel j k).isLt

theorem level_le_position (j : Fin jobs) (k : Fin work) : F.level j k ≤ k.val := by
  have := F.level_lt j k
  unfold level
  split_ifs <;> omega

def job (v : Fin (jobs * work)) : Fin jobs := (finProdFinEquiv.symm v).1
def position (v : Fin (jobs * work)) : Fin work := (finProdFinEquiv.symm v).2

theorem coordinates_injective : Function.Injective
    (fun v : Fin (jobs * work) => (job v, (position v).val)) := by
  intro u v h
  apply finProdFinEquiv.symm.injective
  have h₁ : job u = job v := congrArg (fun p : Fin jobs × ℕ => p.1) h
  have h₂ : (position u).val = (position v).val := congrArg (fun p : Fin jobs × ℕ => p.2) h
  exact Prod.ext h₁ (Fin.ext h₂)

@[simp] theorem job_pair (j : Fin jobs) (k : Fin work) :
    job (finProdFinEquiv (j, k)) = j := by simp [job]

@[simp] theorem position_pair (j : Fin jobs) (k : Fin work) :
    position (finProdFinEquiv (j, k)) = k := by simp [position]

/-- Each vertex of a noninitial layer has just the preceding layer's key
as parent. Initial-layer vertices are roots. -/
def toInstance (L : ℕ) : Instance jobs (jobs * work) where
  owner := job
  release j := j.val * L
  edge u v := job u = job v ∧ (position u).val + 1 = F.level (job v) (position v)
  same_job h := h.1
  rank v := (position v).val
  rank_increases := by
    intro u v h
    have := F.level_le_position (job v) (position v)
    omega
  nonempty_job := by
    intro j
    have hw : 0 < work := lt_of_lt_of_le (F.depth_pos j) (F.depth_le j)
    exact ⟨finProdFinEquiv (j, ⟨0, hw⟩), by simp⟩

theorem at_most_one_parent (L : ℕ) {u v w : Fin (jobs * work)}
    (hu : (F.toInstance L).edge u w) (hv : (F.toInstance L).edge v w) : u = v := by
  apply coordinates_injective
  refine Prod.ext (hu.1.trans hv.1.symm) ?_
  change (position u).val = (position v).val
  have h₁ : (position u).val + 1 = F.level (job w) (position w) := hu.2
  have h₂ : (position v).val + 1 = F.level (job w) (position w) := hv.2
  omega

theorem edge_from_key (L : ℕ) {u v : Fin (jobs * work)}
    (h : (F.toInstance L).edge u v) :
    (position u).val < F.depth (job u) ∧ (position u).val < (position v).val := by
  have hl := F.level_lt (job v) (position v)
  have hp := F.level_le_position (job v) (position v)
  have he := h.2
  rw [h.1]
  omega

theorem jobVertices_eq (L : ℕ) (j : Fin jobs) :
    (F.toInstance L).jobVertices j =
      univ.image (fun k : Fin work => finProdFinEquiv (j, k)) := by
  classical
  ext v
  simp only [Instance.jobVertices, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro h
    refine ⟨position v, ?_⟩
    change job v = j at h
    rw [← h]
    exact finProdFinEquiv.apply_symm_apply v
  · rintro ⟨k, rfl⟩
    exact job_pair j k

theorem jobVertices_card (L : ℕ) (j : Fin jobs) :
    ((F.toInstance L).jobVertices j).card = work := by
  classical
  rw [F.jobVertices_eq, card_image_of_injective]
  · simp
  · intro a b hab
    exact congrArg Prod.snd (finProdFinEquiv.injective hab)

/-- The concrete two-epoch schedule from the general lower bound. -/
theorem offline_schedule {m L : ℕ} (hm : 2 ≤ m) (hw : work = m * L)
    (hd : ∀ j, F.depth j ≤ L) :
    ∃ O, (F.toInstance L).Valid m O ∧ (F.toInstance L).FlowBound O (2 * L) := by
  let pos := fun v : Fin (jobs * work) => (position v).val
  have hpos : ∀ v, pos v < m * L := by intro v; exact (position v).isLt.trans_eq hw
  refine ⟨fun v => pipelineTime m L (job v).val (pos v), ?_, ?_⟩
  · apply (F.toInstance L).pipeline_valid hm pos hpos coordinates_injective (by intros; rfl)
    intro u v huv
    have h := F.edge_from_key L huv
    exact ⟨h.1.trans_le (hd _), h.2⟩
  · exact (F.toInstance L).pipeline_flowBound hm pos hpos (by intros; rfl)

/-- Lemma 6's offline comparison: any such forest family with `mL` work
per job and at most `L` layers has optimum between `L` and `2L`. -/
theorem optimum_bounds {m L : ℕ} (hm : 2 ≤ m) (hj : 0 < jobs)
    (hw : work = m * L) (hd : ∀ j, F.depth j ≤ L) :
    L ≤ (F.toInstance L).optimum m (by omega) ∧
      (F.toInstance L).optimum m (by omega) ≤ 2 * L := by
  have hm0 : 0 < m := by omega
  obtain ⟨O, hO, hflow⟩ := (F.toInstance L).optimum_attained hm0
  have hwork := (F.toInstance L).job_work_bound hO hflow ⟨0, hj⟩
  rw [F.jobVertices_card] at hwork
  refine ⟨Nat.le_of_mul_le_mul_left (hw.symm.le.trans hwork) hm0, ?_⟩
  obtain ⟨P, hP, hb⟩ := F.offline_schedule hm hw hd
  exact (F.toInstance L).optimum_le hm0 hP hb

end LayeredForest
end Scheduling
