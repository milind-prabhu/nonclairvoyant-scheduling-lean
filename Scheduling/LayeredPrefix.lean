import Scheduling.HiddenKey
import Scheduling.LayeredForest

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

/-- A partially fixed layered forest. Each job has a closed prefix, one
current frontier, and an unrevealed suffix. The suffix is temporarily
blocked by every vertex in the current frontier. -/
structure LayeredPrefix (jobs work : ℕ) where
  closed : Fin jobs → ℕ
  width : Fin jobs → ℕ
  fits : ∀ j, closed j + width j ≤ work
  frontier_pos : ∀ j, closed j < work → 0 < width j
  parent : Fin jobs → Fin work → Option (Fin work)
  parent_lt : ∀ j v u, parent j v = some u → u.val < v.val

namespace LayeredPrefix
variable {jobs work : ℕ} (P : LayeredPrefix jobs work)

def boundary (j : Fin jobs) : ℕ := P.closed j + P.width j

def toInstance (L : ℕ) (hw : 0 < work) : Instance jobs (jobs * work) where
  owner := job
  release j := j.val * L
  edge u v := job u = job v ∧
    if (position v).val < P.boundary (job v) then
      P.parent (job v) (position v) = some (position u)
    else P.closed (job v) ≤ (position u).val ∧ (position u).val < P.boundary (job v)
  same_job h := h.1
  rank v := (position v).val
  rank_increases := by
    intro u v h
    have hh := h.2
    split_ifs at hh with hv
    · exact P.parent_lt _ _ _ hh
    · omega
  nonempty_job j := ⟨finProdFinEquiv (j, ⟨0, hw⟩), by simp⟩

noncomputable def frontier (j : Fin jobs) : Finset (Fin (jobs * work)) :=
  univ.filter (fun v => job v = j ∧ P.closed j ≤ (position v).val ∧ (position v).val < P.boundary j)

noncomputable def hidden (j : Fin jobs) : Finset (Fin (jobs * work)) :=
  univ.filter (fun v => job v = j ∧ P.boundary j ≤ (position v).val)

theorem frontier_nonempty (j : Fin jobs) (hj : P.closed j < work) : (P.frontier j).Nonempty := by
  have hp := P.frontier_pos j hj
  refine ⟨finProdFinEquiv (j, ⟨P.closed j, hj⟩), ?_⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  simp only [LayeredForest.job_pair, LayeredForest.position_pair]
  exact ⟨trivial, le_rfl, by dsimp [boundary]; omega⟩

theorem frontier_hidden_edge (L : ℕ) (hw : 0 < work) (j : Fin jobs)
    {u v : Fin (jobs * work)} (hu : u ∈ P.frontier j) (hv : v ∈ P.hidden j) :
    (P.toInstance L hw).edge u v := by
  have hu' := (mem_filter.mp hu).2
  have hv' := (mem_filter.mp hv).2
  refine ⟨hu'.1.trans hv'.1.symm, ?_⟩
  rw [hv'.1, if_neg (by omega)]
  exact hu'.2

/-- Commit one layer's key and choose the size of the next frontier. All
vertices of that new frontier acquire the chosen key as their parent. -/
def advance (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work)
    (hqpos : P.boundary j < work → 0 < q) : LayeredPrefix jobs work where
  closed i := if i = j then P.boundary j else P.closed i
  width i := if i = j then q else P.width i
  fits := by intro i; by_cases hi : i = j <;> simp [hi, hq, P.fits]
  frontier_pos := by
    intro i
    by_cases hi : i = j
    · simpa [hi] using hqpos
    · simpa [hi] using P.frontier_pos i
  parent i v := if i = j ∧ P.boundary j ≤ v.val ∧ v.val < P.boundary j + q then some key else P.parent i v
  parent_lt := by
    intro i v u h
    split_ifs at h with hv
    · have he : key = u := Option.some.inj h
      subst u
      omega
    · exact P.parent_lt _ _ _ h

@[simp] theorem advance_closed (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) :
    (P.advance j key hk q hq hp).closed j = P.boundary j := by simp [advance]

@[simp] theorem advance_boundary (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) :
    (P.advance j key hk q hq hp).boundary j = P.boundary j + q := by simp [boundary, advance]

theorem advance_edge_outside (L : ℕ) (hw : 0 < work) (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q)
    (u v : Fin (jobs * work)) (hv : v ∉ P.hidden j) :
    (P.toInstance L hw).edge u v ↔ ((P.advance j key hk q hq hp).toInstance L hw).edge u v := by
  by_cases hj : job v = j
  · have hlt : (position v).val < P.boundary j := by
      simp only [hidden, mem_filter, mem_univ, true_and, hj, true_and, not_le] at hv
      exact hv
    have hlt' : (position v).val < P.boundary j + q := by omega
    dsimp only [boundary] at hlt hlt'
    simp [toInstance, hj, hlt, hlt', advance, boundary, show ¬ P.closed j + P.width j ≤ (position v).val by omega]
  · simp only [toInstance, advance, boundary, hj, if_false, false_and]
    rfl

theorem advance_hidden_blocked (L : ℕ) (hw : 0 < work) (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q)
    (v : Fin (jobs * work)) (hv : v ∈ P.hidden j) :
    ∃ u, ((P.advance j key hk q hq hp).toInstance L hw).edge u v ∧
      (u = finProdFinEquiv (j, key) ∨ u ∈ P.hidden j) := by
  have hv' := (mem_filter.mp hv).2
  have hbound : P.boundary j < work := hv'.2.trans_lt (position v).isLt
  have hqpos := hp hbound
  by_cases hnew : (position v).val < P.boundary j + q
  · refine ⟨finProdFinEquiv (j, key), ?_, Or.inl rfl⟩
    constructor
    · simpa using hv'.1.symm
    · have hb := hv'.2
      dsimp only [boundary] at hnew hb
      simp [advance, boundary, hv'.1, hnew, hb]
  · let first : Fin (jobs * work) := finProdFinEquiv (j, ⟨P.boundary j, hbound⟩)
    have hfirst : first ∈ P.hidden j := by simp [first, hidden]
    refine ⟨first, ?_, Or.inr hfirst⟩
    constructor
    · simpa [first] using hv'.1.symm
    · dsimp only [boundary] at hnew
      simp [advance, boundary, hv'.1, hnew, first, hqpos]

theorem advance_preserves {m L : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
      A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) :
    let I := P.toInstance L hw
    let J := (P.advance j key hk q hq hp).toInstance L hw
    let t := A.schedule I (finProdFinEquiv (j, key))
    (∀ u ≤ t, executionSlot (A.schedule I) u = executionSlot (A.schedule J) u) ∧
      (∀ v, A.schedule I v ≤ t → A.schedule J v = A.schedule I v) ∧
      (∀ v ∈ P.frontier j, A.schedule J v ≤ A.schedule J (finProdFinEquiv (j, key))) := by
  let I := P.toInstance L hw
  let J := (P.advance j key hk q hq hp).toInstance L hw
  let k : Fin (jobs * work) := finProdFinEquiv (j, key)
  have hkmem : k ∈ P.frontier j := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, LayeredForest.job_pair j key, ?_⟩
    simpa only [k, LayeredForest.position_pair] using hk
  have hI : ∀ v ∈ P.hidden j, ∃ u, I.edge u v ∧ A.schedule I k ≤ A.schedule I u := by
    intro v hv
    exact ⟨k, P.frontier_hidden_edge L hw j hkmem hv, le_rfl⟩
  have hJ : ∀ v ∈ P.hidden j, ∃ u, J.edge u v ∧ A.schedule I k ≤ A.schedule I u := by
    intro v hv
    obtain ⟨u, hu, hloc⟩ := P.advance_hidden_blocked L hw j key hk q hq hp v hv
    refine ⟨u, hu, ?_⟩
    rcases hloc with he | he
    · change u = k at he; rw [he]
    · exact ((A.valid I).precedence (P.frontier_hidden_edge L hw j hkmem he)).le
  have h := A.hidden_replacement I J (P.hidden j) rfl rfl
    (P.advance_edge_outside L hw j key hk q hq hp) hI hJ
  refine ⟨h.1, h.2, ?_⟩
  intro v hv
  rw [h.2 v (hmax v hv), h.2 k le_rfl]
  exact hmax v hv

theorem exists_last_key {m L : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (j : Fin jobs) (hj : P.closed j < work) :
    ∃ key : Fin work, (P.closed j ≤ key.val ∧ key.val < P.boundary j) ∧
      ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) := by
  obtain ⟨v, hv, hmax⟩ := exists_max_image (P.frontier j) (A.schedule (P.toInstance L hw))
    (P.frontier_nonempty j hj)
  have hv' := (mem_filter.mp hv).2
  refine ⟨position v, hv'.2, ?_⟩
  have he : finProdFinEquiv (j, position v) = v := by
    rw [← hv'.1]
    exact finProdFinEquiv.apply_symm_apply v
  rwa [he]

def remainingMass : ℕ := ∑ j : Fin jobs, (work - P.closed j)

theorem advance_mass_lt (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) :
    (P.advance j key hk q hq hp).remainingMass < P.remainingMass := by
  unfold remainingMass
  apply sum_lt_sum
  · intro i _
    by_cases hi : i = j
    · subst i
      simp only [advance_closed]
      dsimp [boundary]
      omega
    · simp [advance, hi]
  · refine ⟨j, mem_univ _, ?_⟩
    rw [advance_closed]
    have hf := P.fits j
    dsimp [boundary] at hk ⊢
    omega

theorem no_barrier_at_completion (L : ℕ) (hw : 0 < work)
    (hdone : ∀ j, P.closed j = work) {u v w : Fin (jobs * work)}
    (hu : (P.toInstance L hw).edge u w) (hv : (P.toInstance L hw).edge v w) : u = v := by
  have hb : (position w).val < P.boundary (job w) := by
    have := (position w).isLt
    simp only [boundary, hdone]
    omega
  have hpu := hu.2
  have hpv := hv.2
  rw [if_pos hb] at hpu hpv
  have he : position u = position v := Option.some.inj (hpu.symm.trans hpv)
  apply LayeredForest.coordinates_injective
  exact Prod.ext (hu.1.trans hv.1.symm) (congrArg Fin.val he)

theorem advance_boundary_ge (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) (i : Fin jobs) :
    P.boundary i ≤ (P.advance j key hk q hq hp).boundary i := by
  by_cases hi : i = j
  · subst i; rw [advance_boundary]; omega
  · simp only [boundary, advance, if_neg hi]
    exact le_rfl

theorem advance_parent_visible (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q)
    (i : Fin jobs) (v : Fin work) (hv : v.val < P.boundary i) :
    (P.advance j key hk q hq hp).parent i v = P.parent i v := by
  change (if i = j ∧ P.boundary j ≤ v.val ∧ v.val < P.boundary j + q then _ else _) = _
  rw [if_neg]
  rintro ⟨rfl, hge, _⟩
  omega

end LayeredPrefix
end Scheduling
