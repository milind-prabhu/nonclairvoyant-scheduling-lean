import Scheduling.LayerAdversary

namespace Scheduling.LayeredPrefix
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs work : ℕ} (P : LayeredPrefix jobs work)

theorem finishTime_eq_key {m L : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
      A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key))) :
    P.finishTime (L := L) hw A j = A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) := by
  apply le_antisymm (Finset.sup_le hmax)
  apply le_sup (f := A.schedule (P.toInstance L hw))
  apply mem_filter.mpr
  refine ⟨mem_univ _, LayeredForest.job_pair j key, ?_⟩
  simpa only [LayeredForest.position_pair] using hk

theorem advance_other_frontier (j i : Fin jobs) (hi : i ≠ j) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) :
    (P.advance j key hk q hq hp).frontier i = P.frontier i := by
  simp only [frontier, boundary, advance, if_neg hi]
  rfl

theorem advance_new_frontier_parent (L : ℕ) (hw : 0 < work) (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q)
    (v : Fin (jobs * work)) (hv : v ∈ (P.advance j key hk q hq hp).frontier j) :
    ((P.advance j key hk q hq hp).toInstance L hw).edge (finProdFinEquiv (j, key)) v := by
  have hv' := (mem_filter.mp hv).2
  rw [advance_closed, advance_boundary] at hv'
  constructor
  · simpa only [LayeredForest.job_pair] using hv'.1.symm
  · have hlo := hv'.2.1
    have hhi := hv'.2.2
    dsimp only [boundary] at hlo hhi
    simp [advance, boundary, hv'.1, hlo, hhi]

/-- Advancing a last key never moves the earliest possible remaining
frontier completion backwards. Other frontiers retain an unprocessed
vertex, and the new frontier waits for the committed key. -/
theorem advance_finishTime_ge {m L t : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
      A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
    (hbefore : ∀ i, P.closed i < work → t ≤ P.finishTime (L := L) hw A i)
    (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q) :
    ∀ i, (P.advance j key hk q hq hp).closed i < work →
      t ≤ (P.advance j key hk q hq hp).finishTime (L := L) hw A i := by
  let I := P.toInstance L hw
  let R := P.advance j key hk q hq hp
  let J := R.toInstance L hw
  let k : Fin (jobs * work) := finProdFinEquiv (j, key)
  have ht : t ≤ A.schedule I k := by
    have hj : P.closed j < work := by have := P.fits j; dsimp [boundary] at hk; omega
    have h := hbefore j hj
    rwa [P.finishTime_eq_key hw A j key hk hmax] at h
  have hs := P.advance_preserves (L := L) hw A j key hk hmax q hq hp
  intro i hi
  by_cases hij : i = j
  · subst i
    obtain ⟨v, hv⟩ := R.frontier_nonempty j hi
    have hedge := P.advance_new_frontier_parent L hw j key hk q hq hp v hv
    have htime := (A.valid J).precedence hedge
    change A.schedule J k < A.schedule J v at htime
    have hkTime := hs.2.1 k le_rfl
    have hvt : t ≤ A.schedule J v := by change A.schedule J k = A.schedule I k at hkTime; omega
    exact hvt.trans (le_sup (f := A.schedule J) hv)
  · have hclosed : R.closed i = P.closed i := by simp [R, advance, hij]
    have hiP : P.closed i < work := by rwa [hclosed] at hi
    obtain ⟨v, hv, hlast⟩ := exists_max_image (P.frontier i) (A.schedule I)
      (P.frontier_nonempty i hiP)
    have hvt : t ≤ A.schedule I v := (hbefore i hiP).trans (Finset.sup_le hlast)
    have he : executionPrefix (A.schedule I) t = executionPrefix (A.schedule J) t :=
      executionPrefix_eq_of_slots (by intro u hu; exact hs.1 u (hu.le.trans ht))
    have hnew : t ≤ A.schedule J v := by
      by_contra hn
      have hm : v.val ∈ executionPrefix (A.schedule J) t := (val_mem_executionPrefix v).mpr (by omega)
      rw [← he] at hm
      have := (val_mem_executionPrefix v).mp hm
      omega
    have hvR : v ∈ R.frontier i := by
      rw [show R.frontier i = P.frontier i from P.advance_other_frontier j i hij key hk q hq hp]
      exact hv
    exact hnew.trans (le_sup (f := A.schedule J) hvR)

theorem CompletionRun.preserves_slots {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work}
    (h : CompletionRun (L := L) hw A rule P Q) (t : ℕ)
    (hbefore : ∀ i, P.closed i < work → t ≤ P.finishTime (L := L) hw A i) :
    ∀ u ≤ t, executionSlot (A.schedule (P.toInstance L hw)) u =
      executionSlot (A.schedule (Q.toInstance L hw)) u := by
  induction h with
  | done P hd => intros; rfl
  | step P Q j key hk hmax hearliest tail ih =>
    have ht : t ≤ A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) := by
      have hj : P.closed j < work := by have := P.fits j; dsimp [boundary] at hk; omega
      have h := hbefore j hj
      rwa [P.finishTime_eq_key hw A j key hk hmax] at h
    have hs := P.advance_preserves hw A j key hk hmax
      (rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
      (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)
    have hb := P.advance_finishTime_ge hw A j key hk hmax hbefore
      (rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
      (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)
    intro u hu
    exact (hs.1 u (by omega)).trans (ih hb u hu)

theorem head_times_in_final {m L : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (rule : LayerSizeRule jobs work) (Q : LayeredPrefix jobs work)
    (j : Fin jobs) (key : Fin work)
    (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
    (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
      A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
    (hearliest : ∀ i, P.closed i < work →
      A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) ≤ P.finishTime (L := L) hw A i)
    (tail : CompletionRun (L := L) hw A rule
      (P.advance j key hk
        (rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
        (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)) Q) :
    ∀ v, A.schedule (P.toInstance L hw) v ≤
      A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) →
      A.schedule (Q.toInstance L hw) v = A.schedule (P.toInstance L hw) v := by
  let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key))
  let q := rule.size j (P.boundary j) (t + 1)
  have hs := P.advance_preserves hw A j key hk hmax q
    (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)
  have hb := P.advance_finishTime_ge hw A j key hk hmax hearliest q
    (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)
  have ht := tail.preserves_slots t hb
  intro v hv
  have he := (hs.1 (A.schedule (P.toInstance L hw) v) hv).trans
    (ht (A.schedule (P.toInstance L hw) v) hv)
  have hm : v.val ∈ executionSlot (A.schedule (P.toInstance L hw)) (A.schedule (P.toInstance L hw) v) :=
    (val_mem_executionSlot v).mpr rfl
  rw [he] at hm
  exact (val_mem_executionSlot v).mp hm

theorem CompletionRun.parent_visible {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work}
    (h : CompletionRun (L := L) hw A rule P Q) :
    ∀ j (v : Fin work), v.val < P.boundary j → Q.parent j v = P.parent j v := by
  induction h with
  | done P hd => intros; rfl
  | step P Q j key hk hmax hearliest tail ih =>
    intro i v hv
    have hb := P.advance_boundary_ge j key hk
      (rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
      (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _) i
    rw [ih i v (hv.trans_le hb)]
    exact P.advance_parent_visible j key hk _ _ _ i v hv

end Scheduling.LayeredPrefix
