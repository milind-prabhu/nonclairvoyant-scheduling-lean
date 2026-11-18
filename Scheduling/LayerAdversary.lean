import Scheduling.LayeredPrefix

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

/-- Sizes may depend on the job, the already revealed prefix, and the
time at which the next layer is revealed. -/
structure LayerSizeRule (jobs work : ℕ) where
  size : Fin jobs → ℕ → ℕ → ℕ
  fits : ∀ j p t, p ≤ work → p + size j p t ≤ work
  positive : ∀ j p t, p < work → 0 < size j p t

def firstForcingTime (c L j : ℕ) : ℕ := ((j + c - 1) / c) * c * L

def forcingLayerRule (jobs work m c L : ℕ) (hm : 0 < m) : LayerSizeRule jobs work where
  size j p t := min (work - p)
    (if firstForcingTime c L j.val ≤ t ∧ t < firstForcingTime c L j.val + L / 2 then 1 else 2 * m)
  fits := by
    intro j p t hp
    have := min_le_left (work - p)
      (if firstForcingTime c L j.val ≤ t ∧ t < firstForcingTime c L j.val + L / 2 then 1 else 2 * m)
    omega
  positive := by
    intro j p t hp
    apply lt_min (by omega)
    split_ifs <;> omega

namespace LayeredPrefix
variable {jobs work : ℕ}

def initial (m : ℕ) (hm : 0 < m) : LayeredPrefix jobs work where
  closed _ := 0
  width _ := min (2 * m) work
  fits _ := by simp
  frontier_pos := by intro j hw; exact lt_min (by omega) hw
  parent _ _ := none
  parent_lt := by intros; contradiction

noncomputable def finishTime (P : LayeredPrefix jobs work) {m L : ℕ}
    (hw : 0 < work) (A : DeterministicScheduler m) (j : Fin jobs) : ℕ :=
  (P.frontier j).sup (A.schedule (P.toInstance L hw))

theorem exists_earliest (P : LayeredPrefix jobs work) {m L : ℕ}
    (hw : 0 < work) (A : DeterministicScheduler m)
    (hactive : ∃ j, P.closed j < work) :
    ∃ j : Fin jobs, ∃ key : Fin work,
      (P.closed j ≤ key.val ∧ key.val < P.boundary j) ∧
      (∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key))) ∧
      (∀ i, P.closed i < work → A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) ≤
        P.finishTime (L := L) hw A i) := by
  let active := univ.filter (fun j => P.closed j < work)
  have ha : active.Nonempty := by
    obtain ⟨j, hj⟩ := hactive
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  obtain ⟨j, hj, hmin⟩ := exists_min_image active (P.finishTime (L := L) hw A) ha
  obtain ⟨key, hk, hmax⟩ := P.exists_last_key (L := L) hw A j (mem_filter.mp hj).2
  refine ⟨j, key, hk, hmax, ?_⟩
  intro i hi
  have hm := hmin i (mem_filter.mpr ⟨mem_univ _, hi⟩)
  apply le_trans ?_ hm
  apply le_sup (f := A.schedule (P.toInstance L hw))
  apply mem_filter.mpr
  refine ⟨mem_univ _, LayeredForest.job_pair j key, ?_⟩
  simpa only [LayeredForest.position_pair] using hk

/-- A finite chronological sequence of commitments. Each step selects the
earliest finishing current frontier, commits one of its last vertices as
key, and chooses the new width from its actual reveal time. -/
inductive CompletionRun {m L : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (rule : LayerSizeRule jobs work) : LayeredPrefix jobs work → LayeredPrefix jobs work → Prop
  | done (P : LayeredPrefix jobs work) (h : ∀ j, P.closed j = work) : CompletionRun (L := L) hw A rule P P
  | step (P Q : LayeredPrefix jobs work) (j : Fin jobs) (key : Fin work)
      (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
      (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
      (hearliest : ∀ i, P.closed i < work →
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) ≤ P.finishTime (L := L) hw A i)
      (tail : CompletionRun (L := L) hw A rule
        (P.advance j key hk
          (rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
          (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)) Q) :
      CompletionRun (L := L) hw A rule P Q

/-- The construction terminates because every commitment closes at least
one additional vertex. Its stopping criterion does not assume an online
performance guarantee. -/
theorem exists_completion (P : LayeredPrefix jobs work) {m L : ℕ}
    (hw : 0 < work) (A : DeterministicScheduler m) (rule : LayerSizeRule jobs work) :
    ∃ Q, CompletionRun (L := L) hw A rule P Q := by
  have aux : ∀ n, ∀ P : LayeredPrefix jobs work, P.remainingMass = n →
      ∃ Q, CompletionRun (L := L) hw A rule P Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn
      by_cases ha : ∃ j, P.closed j < work
      · obtain ⟨j, key, hk, hmax, hearliest⟩ := P.exists_earliest (L := L) hw A ha
        let q := rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1)
        have hq : P.boundary j + q ≤ work := rule.fits _ _ _ (P.fits j)
        have hp : P.boundary j < work → 0 < q := rule.positive _ _ _
        let R := P.advance j key hk q hq hp
        have hlt : R.remainingMass < n := by rw [← hn]; exact P.advance_mass_lt j key hk q hq hp
        obtain ⟨Q, hQ⟩ := ih R.remainingMass hlt R rfl
        exact ⟨Q, CompletionRun.step P Q j key hk hmax hearliest hQ⟩
      · have hd : ∀ j, P.closed j = work := by
          intro j
          have hf := P.fits j
          have hh : ¬ P.closed j < work := by intro h; exact ha ⟨j, h⟩
          omega
        exact ⟨P, CompletionRun.done P hd⟩
  exact aux P.remainingMass P rfl

theorem CompletionRun.finished {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work}
    (h : CompletionRun (L := L) hw A rule P Q) : ∀ j, Q.closed j = work := by
  induction h with
  | done P hd => exact hd
  | step P Q j key hk hmax hearliest tail ih => exact ih

theorem CompletionRun.outForest {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work}
    (h : CompletionRun (L := L) hw A rule P Q)
    {u v w : Fin (jobs * work)} (hu : (Q.toInstance L hw).edge u w)
    (hv : (Q.toInstance L hw).edge v w) : u = v :=
  Q.no_barrier_at_completion L hw h.finished hu hv

end LayeredPrefix
end Scheduling
