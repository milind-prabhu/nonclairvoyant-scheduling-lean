import Scheduling.BatchedLower
import Scheduling.DeterministicLower
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

/-- All data of an instance, excluding its proof fields, determine it. -/
theorem Instance.ext_data {jobs vertices : ℕ} {I J : Instance jobs vertices}
    (ho : I.owner = J.owner) (hr : I.release = J.release)
    (he : I.edge = J.edge) (hk : I.rank = J.rank) : I = J := by
  cases I
  cases J
  cases ho
  cases hr
  cases he
  cases hk
  rfl

/-- A finite encoding of an out-forest on fixed job and vertex labels.
The local vertex order witnesses acyclicity. Releases are supplied
separately, so this code contains no unbounded numerical data. -/
structure ForestCode (jobs work : ℕ) where
  parent : Fin jobs → Fin work → Option (Fin work)
  parent_lt : ∀ j v u, parent j v = some u → u.val < v.val

namespace ForestCode
variable {jobs work : ℕ}

theorem parent_injective : Function.Injective (parent : ForestCode jobs work → _) := by
  intro P Q he
  cases P
  cases Q
  cases he
  rfl

noncomputable instance : Fintype (ForestCode jobs work) :=
  Fintype.ofInjective parent parent_injective

noncomputable instance : DecidableEq (ForestCode jobs work) := Classical.decEq _

def toInstance (P : ForestCode jobs work) (L : ℕ) (hw : 0 < work) : Instance jobs (jobs * work) where
  owner := job
  release j := j.val * L
  edge u v := job u = job v ∧ P.parent (job v) (position v) = some (position u)
  same_job h := h.1
  rank v := (position v).val
  rank_increases := by intro u v h; exact P.parent_lt _ _ _ h.2
  nonempty_job j := ⟨finProdFinEquiv (j, ⟨0, hw⟩), LayeredForest.job_pair _ _⟩

theorem outForest (P : ForestCode jobs work) (L : ℕ) (hw : 0 < work)
    {u v w : Fin (jobs * work)}
    (hu : (P.toInstance L hw).edge u w) (hv : (P.toInstance L hw).edge v w) : u = v := by
  have hp := Option.some.inj (hu.2.symm.trans hv.2)
  exact LayeredForest.coordinates_injective
    (Prod.ext (hu.1.trans hv.1.symm) (congrArg Fin.val hp))

def ofPrefix (P : LayeredPrefix jobs work) : ForestCode jobs work :=
  ⟨P.parent, P.parent_lt⟩

theorem ofPrefix_toInstance (P : LayeredPrefix jobs work) (L : ℕ) (hw : 0 < work)
    (hd : ∀ j, P.closed j = work) : (ofPrefix P).toInstance L hw = P.toInstance L hw := by
  apply Instance.ext_data (I := (ofPrefix P).toInstance L hw) (J := P.toInstance L hw) rfl rfl ?_ rfl
  funext u v
  apply propext
  have hv : (position v).val < P.boundary (job v) := by
    have hh := (position v).isLt
    dsimp only [LayeredPrefix.boundary]
    rw [hd]
    omega
  simp only [toInstance, ofPrefix, LayeredPrefix.toInstance, if_pos hv]

theorem jobVertices_card (P : ForestCode jobs work) (L : ℕ) (hw : 0 < work) (j : Fin jobs) :
    ((P.toInstance L hw).jobVertices j).card = work := by
  let Q : LayeredPrefix jobs work := {
    closed := fun _ => work
    width := fun _ => 0
    fits := by simp
    frontier_pos := by intros; omega
    parent := P.parent
    parent_lt := P.parent_lt }
  have he : (ofPrefix Q).toInstance L hw = P.toInstance L hw := rfl
  rw [← he, ofPrefix_toInstance Q L hw (by intros; rfl)]
  exact Q.jobVertices_card L hw j

end ForestCode
end Scheduling
