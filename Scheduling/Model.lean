import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Scheduling
open Finset

/-- A finite collection of unit-time DAG jobs. `rank` witnesses acyclicity;
it is mathematical input and is not information supplied to an online scheduler. -/
structure Instance (jobs vertices : ℕ) where
  owner : Fin vertices → Fin jobs
  release : Fin jobs → ℕ
  edge : Fin vertices → Fin vertices → Prop
  same_job : ∀ {u v}, edge u v → owner u = owner v
  rank : Fin vertices → ℕ
  rank_increases : ∀ {u v}, edge u v → rank u < rank v
  nonempty_job : ∀ j, ∃ v, owner v = j

abbrev Assignment {vertices : ℕ} := Fin vertices → ℕ

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- All three schedule constraints in Section 2 of the paper. -/
structure Valid (m : ℕ) (S : Assignment (vertices := vertices)) : Prop where
  release : ∀ v, I.release (I.owner v) ≤ S v
  precedence : ∀ {u v}, I.edge u v → S u < S v
  capacity : ∀ t, (univ.filter (fun v => S v = t)).card ≤ m

noncomputable def jobVertices (j : Fin jobs) : Finset (Fin vertices) :=
  univ.filter (fun v => I.owner v = j)

noncomputable def completion (S : Assignment (vertices := vertices)) (j : Fin jobs) : ℕ :=
  (I.jobVertices j).sup (fun v => S v + 1)

noncomputable def maxFlow (S : Assignment (vertices := vertices)) : ℕ :=
  univ.sup (fun j => I.completion S j - I.release j)

/-- An offline comparison schedule with maximum flow at most `L`. -/
def FlowBound (S : Assignment (vertices := vertices)) (L : ℕ) : Prop :=
  ∀ v, S v < I.release (I.owner v) + L

/-- Ready vertices are revealed at the beginning of a slot. -/
def Ready (S : Assignment (vertices := vertices)) (t : ℕ) (v : Fin vertices) : Prop :=
  I.release (I.owner v) ≤ t ∧ t ≤ S v ∧ ∀ u, I.edge u v → S u < t

noncomputable def alive (S : Assignment (vertices := vertices)) (t : ℕ) : Finset (Fin jobs) :=
  univ.filter (fun j => I.release j ≤ t ∧ ∃ v, I.owner v = j ∧ t ≤ S v)

noncomputable def remaining (S : Assignment (vertices := vertices)) (t : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => I.release (I.owner v) ≤ t ∧ t ≤ S v)

/-- Work conservation and job-level FIFO priority. Ties between equal release
times may be broken arbitrarily. Both conditions inspect only ready vertices. -/
structure IsFIFO (m : ℕ) (S : Assignment (vertices := vertices)) : Prop where
  work_conserving : ∀ t v, I.Ready S t v → S v ≠ t →
    (univ.filter (fun u => S u = t)).card = m
  fifo_priority : ∀ t v u, I.Ready S t v → S v ≠ t → S u = t →
    I.release (I.owner u) ≤ I.release (I.owner v)

theorem flowBound_iff_maxFlow_le (S : Assignment (vertices := vertices)) (L : ℕ) :
    I.FlowBound S L ↔ I.maxFlow S ≤ L := by
  classical
  constructor
  · intro h
    apply Finset.sup_le
    intro j _
    apply Nat.sub_le_iff_le_add.mpr
    apply Finset.sup_le
    intro v hv
    have ho : I.owner v = j := (Finset.mem_filter.mp hv).2
    have := h v
    rw [ho] at this
    omega
  · intro h v
    have h₁ : S v + 1 ≤ I.completion S (I.owner v) :=
      Finset.le_sup (f := fun v => S v + 1) (by simp [jobVertices])
    have h₂ : I.completion S (I.owner v) - I.release (I.owner v) ≤ L :=
      (Finset.le_sup (f := fun j => I.completion S j - I.release j) (mem_univ _)).trans h
    omega

theorem flowBound_pos {S : Assignment (vertices := vertices)} {m L : ℕ}
    (hS : I.Valid m S) (hL : I.FlowBound S L) (v : Fin vertices) : 0 < L := by
  have := hS.release v
  have := hL v
  omega

end Instance
end Scheduling
