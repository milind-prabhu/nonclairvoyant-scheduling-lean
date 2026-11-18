import Scheduling.OfflinePipeline
import Scheduling.LayeredForest

namespace Scheduling.StarChain
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs m : ℕ}

/-- Short jobs are stars; long jobs have one middle vertex before the
leaves. Labels 0 and 1 are respectively the root and potential middle.
Releases are translated one slot earlier than in the paper. -/
def toInstance (long : Fin jobs → Bool) (hm : 0 < m) : Instance jobs (jobs * (3 * m)) where
  owner := job
  release j := j.val * 3
  edge u v := job u = job v ∧
    if long (job v) then
      ((position u).val = 0 ∧ (position v).val = 1) ∨
      ((position u).val = 1 ∧ 2 ≤ (position v).val)
    else (position u).val = 0 ∧ 1 ≤ (position v).val
  same_job h := h.1
  rank v := (position v).val
  rank_increases := by
    intro u v h
    have hh := h.2
    split_ifs at hh <;> omega
  nonempty_job j := ⟨finProdFinEquiv (j, ⟨0, by omega⟩), by simp⟩

def root (hm : 0 < m) (j : Fin jobs) : Fin (jobs * (3 * m)) :=
  finProdFinEquiv (j, ⟨0, by omega⟩)

def middle (hm : 0 < m) (j : Fin jobs) : Fin (jobs * (3 * m)) :=
  finProdFinEquiv (j, ⟨1, by omega⟩)

@[simp] theorem job_root (hm : 0 < m) (j : Fin jobs) : job (root hm j) = j := by simp [root]
@[simp] theorem position_root (hm : 0 < m) (j : Fin jobs) : (position (root hm j)).val = 0 := by simp [root]
@[simp] theorem job_middle (hm : 0 < m) (j : Fin jobs) : job (middle hm j) = j := by simp [middle]
@[simp] theorem position_middle (hm : 0 < m) (j : Fin jobs) : (position (middle hm j)).val = 1 := by simp [middle]

theorem eq_root (hm : 0 < m) (v : Fin (jobs * (3 * m))) (hv : (position v).val = 0) :
    v = root hm (job v) := by
  apply LayeredForest.coordinates_injective
  exact Prod.ext (by simp) (by simpa using hv)

theorem eq_middle (hm : 0 < m) (v : Fin (jobs * (3 * m))) (hv : (position v).val = 1) :
    v = middle hm (job v) := by
  apply LayeredForest.coordinates_injective
  exact Prod.ext (by simp) (by simpa using hv)

def IsLeaf (long : Fin jobs → Bool) (v : Fin (jobs * (3 * m))) : Prop :=
  if long (job v) then 2 ≤ (position v).val else 1 ≤ (position v).val

def IsMiddle (long : Fin jobs → Bool) (v : Fin (jobs * (3 * m))) : Prop :=
  long (job v) = true ∧ (position v).val = 1

theorem vertex_kinds (long : Fin jobs → Bool) (v : Fin (jobs * (3 * m))) :
    (position v).val = 0 ∨ IsMiddle long v ∨ IsLeaf long v := by
  unfold IsMiddle IsLeaf
  cases long (job v) <;> simp <;> omega

theorem no_parent_root (long : Fin jobs → Bool) (hm : 0 < m) (j : Fin jobs)
    (u : Fin (jobs * (3 * m))) : ¬ (toInstance long hm).edge u (root hm j) := by
  simp [toInstance, root]

theorem middle_parent (long : Fin jobs → Bool) (hm : 0 < m) (j : Fin jobs) :
    (toInstance long hm).edge (root hm j) (middle hm j) := by
  constructor
  · simp
  · simp [root, middle]

theorem at_most_one_parent (long : Fin jobs → Bool) (hm : 0 < m)
    {u v w : Fin (jobs * (3 * m))}
    (hu : (toInstance long hm).edge u w) (hv : (toInstance long hm).edge v w) : u = v := by
  apply LayeredForest.coordinates_injective
  refine Prod.ext (hu.1.trans hv.1.symm) ?_
  have h₁ := hu.2
  have h₂ := hv.2
  change (position u).val = (position v).val
  split_ifs at h₁ h₂ <;> omega

theorem parent_exists (long : Fin jobs → Bool) (hm : 0 < m)
    (v : Fin (jobs * (3 * m))) (hv : 0 < (position v).val) :
    ∃ u, (toInstance long hm).edge u v := by
  by_cases hl : long (job v) = true
  · by_cases hmid : (position v).val = 1
    · refine ⟨root hm (job v), ?_⟩
      simp [toInstance, root, hl, hmid]
    · refine ⟨middle hm (job v), ?_⟩
      simp [toInstance, middle, hl, show 2 ≤ (position v).val by omega]
  · refine ⟨root hm (job v), ?_⟩
    simp [toInstance, root, hl, show 1 ≤ (position v).val by omega]

theorem parent_position (long : Fin jobs → Bool) (hm : 0 < m)
    {u v : Fin (jobs * (3 * m))} (he : (toInstance long hm).edge u v) :
    (position u).val ≤ 1 := by
  have hh := he.2
  split_ifs at hh <;> omega

theorem root_before_nonroot (long : Fin jobs → Bool) (hm : 0 < m)
    {S : Assignment} (hS : (toInstance long hm).Valid m S)
    (v : Fin (jobs * (3 * m))) (hv : 0 < (position v).val) :
    S (root hm (job v)) < S v := by
  obtain ⟨u, he⟩ := parent_exists long hm v hv
  have hu := parent_position long hm he
  have ho := he.1
  have ht := hS.precedence he
  by_cases hz : (position u).val = 0
  · rw [eq_root hm u hz, ho] at ht
    exact ht
  · have hone : (position u).val = 1 := by omega
    rw [eq_middle hm u hone, ho] at ht
    exact (hS.precedence (middle_parent long hm (job v))).trans ht

/-- Every vertex is at distance at most two from its job's root. Together
with unique parents, this certifies rooted out-trees of height at most three. -/
theorem root_reaches (long : Fin jobs → Bool) (hm : 0 < m)
    (v : Fin (jobs * (3 * m))) :
    v = root hm (job v) ∨ (toInstance long hm).edge (root hm (job v)) v ∨
      ∃ u, (toInstance long hm).edge (root hm (job v)) u ∧ (toInstance long hm).edge u v := by
  by_cases hz : (position v).val = 0
  · exact Or.inl (eq_root hm v hz)
  · obtain ⟨u, he⟩ := parent_exists long hm v (by omega)
    have hu := parent_position long hm he
    have ho := he.1
    by_cases hu0 : (position u).val = 0
    · exact Or.inr (Or.inl (by rwa [eq_root hm u hu0, ho] at he))
    · refine Or.inr (Or.inr ⟨u, ?_, he⟩)
      rw [eq_middle hm u (by omega), ho]
      exact middle_parent long hm _

theorem offline_schedule (long : Fin jobs → Bool) (hm : 2 ≤ m) :
    ∃ O, (toInstance (m := m) long (by omega)).Valid m O ∧ (toInstance (m := m) long (by omega)).FlowBound O 6 := by
  let I := toInstance long (show 0 < m by omega)
  let pos := fun v : Fin (jobs * (3 * m)) => (position v).val
  have hpos : ∀ v, pos v < m * 3 := by intro v; have := (position v).isLt; dsimp [pos]; omega
  have hinj : Function.Injective (fun v => (I.owner v, pos v)) := LayeredForest.coordinates_injective
  have hedge : ∀ u v, I.edge u v → pos u < 3 ∧ pos u < pos v := by
    intro u v he
    have hp := I.rank_increases he
    have hh := he.2
    change (position u).val < 3 ∧ (position u).val < (position v).val
    split_ifs at hh <;> omega
  refine ⟨fun v => pipelineTime m 3 (I.owner v).val (pos v), ?_, ?_⟩
  · exact I.pipeline_valid hm pos hpos hinj (by intros; rfl) hedge
  · exact I.pipeline_flowBound hm pos hpos (by intros; rfl)

theorem optimum_le_six (long : Fin jobs → Bool) (hm : 2 ≤ m) :
    (toInstance (m := m) long (by omega)).optimum m (by omega) ≤ 6 := by
  obtain ⟨O, hO, hflow⟩ := offline_schedule long hm
  exact (toInstance (m := m) long (by omega)).optimum_le (by omega) hO hflow

theorem jobVertices_card (long : Fin jobs → Bool) (hm : 0 < m) (j : Fin jobs) :
    ((toInstance long hm).jobVertices j).card = 3 * m := by
  have he : (toInstance long hm).jobVertices j =
      univ.image (fun p : Fin (3 * m) => finProdFinEquiv (j, p)) := by
    ext v
    simp only [Instance.jobVertices, mem_filter, mem_univ, true_and, mem_image]
    change job v = j ↔ ∃ p : Fin (3 * m), finProdFinEquiv (j, p) = v
    constructor
    · intro ho
      refine ⟨position v, ?_⟩
      apply LayeredForest.coordinates_injective
      simp only [LayeredForest.job_pair, LayeredForest.position_pair]
      exact Prod.ext ho.symm rfl
    · rintro ⟨p, rfl⟩
      simp
  rw [he, card_image_of_injective]
  · simp
  · intro p q hpq
    exact (Prod.mk.inj (finProdFinEquiv.injective hpq)).2

end Scheduling.StarChain
