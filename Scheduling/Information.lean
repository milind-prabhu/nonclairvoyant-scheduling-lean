import Scheduling.FIFOConstruction

/-! Public observations use natural-number identifiers, independently of the
number of hidden vertices or future jobs in an instance. -/
namespace Scheduling
open Finset

/-- FIFO sees a finite set of `(release time, vertex identifier)` pairs. -/
abbrev FIFOObservation := Finset (ℕ ×ₗ ℕ)

def fifoPolicy (m : ℕ) (Q : FIFOObservation) : Finset ℕ :=
  (Packing.slice Q 0 m).image (fun x => (ofLex x).2)

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- The planner is a single function of a public observation, independent
of the instance's dimensions, ownership map, and hidden edges. -/
theorem fifoSelect_public (m : ℕ) (ready : Finset (Fin vertices)) :
    (I.fifoSelect m ready).image Fin.val = fifoPolicy m (ready.image I.fifoPriority) := by
  unfold fifoPolicy
  rw [← I.fifoSelect_image, image_image]
  rfl

variable [DecidableRel I.edge]

def fifoObservation (m t : ℕ) : FIFOObservation :=
  (I.fifoReady (I.fifoRun m t) t).image I.fifoPriority

theorem fifoAction_public (m t : ℕ) :
    (I.fifoAction m t).image Fin.val = fifoPolicy m (I.fifoObservation m t) :=
  I.fifoSelect_public m _

/-- Full cross-instance indistinguishability for FIFO: even when the hidden
numbers of vertices and jobs differ, equal current observations imply equal
execution decisions. FIFO needs no history beyond the current frontier. -/
theorem fifoSchedule_nonclairvoyant {otherJobs otherVertices m : ℕ}
    (J : Instance otherJobs otherVertices) [DecidableRel J.edge]
    (hm : 0 < m) (t : ℕ)
    (hobs : I.fifoObservation m t = J.fifoObservation m t) :
    (univ.filter (fun v => I.fifoSchedule m hm v = t)).image Fin.val =
      (univ.filter (fun v => J.fifoSchedule m hm v = t)).image Fin.val := by
  rw [← I.fifo_action_eq hm, ← J.fifo_action_eq hm,
    I.fifoAction_public, J.fifoAction_public, hobs]

end Instance

/-- A general stateful policy with a public observation interface. `step`
returns both its decision and its next internal state. -/
structure OnlinePolicy (Observation State Action : Type*) where
  initial : State
  step : ℕ → Observation → State → Action × State

namespace OnlinePolicy
variable {Observation State Action : Type*} (P : OnlinePolicy Observation State Action)

def state (history : ℕ → Observation) : ℕ → State
  | 0 => P.initial
  | t + 1 => (P.step t (history t) (state history t)).2

def decision (history : ℕ → Observation) (t : ℕ) : Action :=
  (P.step t (history t) (P.state history t)).1

/-- Equal observed prefixes yield equal states, regardless of the hidden
environments that produced those prefixes. -/
theorem state_eq_of_history_eq (a b : ℕ → Observation) (t : ℕ)
    (h : ∀ u < t, a u = b u) : P.state a t = P.state b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [state, h t (by omega), ih (by intro u hu; exact h u (by omega))]

theorem decision_eq_of_history_eq (a b : ℕ → Observation) (t : ℕ)
    (h : ∀ u ≤ t, a u = b u) : P.decision a t = P.decision b t := by
  unfold decision
  rw [P.state_eq_of_history_eq a b t (by intro u hu; exact h u (by omega)), h t le_rfl]

end OnlinePolicy
end Scheduling
