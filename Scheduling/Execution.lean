import Scheduling.RoundPlanner

namespace Scheduling
open Finset
variable {jobs vertices batches : ℕ}

structure ExecutionState (vertices : ℕ) where
  clock : ℕ
  stamp : Fin vertices → Option ℕ

namespace ExecutionState
def initial : ExecutionState vertices := ⟨0, fun _ => none⟩
def completed (s : ExecutionState vertices) : Finset (Fin vertices) :=
  univ.filter (fun v => s.stamp v ≠ none)
end ExecutionState

namespace Batching
variable {I : Instance jobs vertices} {L : ℕ} (B : Batching I L batches)
variable [DecidableRel I.edge]

/-- Environment observation: only admitted ready vertices are exposed. The
planner itself receives this snapshot, not the instance or its hidden edges. -/
def observe (s : ExecutionState vertices) : ReadySnapshot (Fin vertices) batches where
  batchOf := B.vertexBatch
  ready := fun b => univ.filter (fun v => B.vertexBatch v = b ∧ B.eligible b ≤ s.clock ∧
    s.stamp v = none ∧ ∀ u, I.edge u v → s.stamp u ≠ none)
  ready_batch := by intro b v hv; exact (mem_filter.mp hv).2.1

def advance (m : ℕ) (s : ExecutionState vertices) : ExecutionState vertices where
  clock := s.clock + (B.observe s).duration m
  stamp :=
    let cached := Vector.ofFn (fun v : Fin vertices => match (B.observe s).assignSlot m v with
      | none => s.stamp v
      | some k => some (s.clock + k))
    fun v => cached[v.val]

def run (B : Batching I L batches) (m : ℕ) : ℕ → ExecutionState vertices
  | 0 => ExecutionState.initial
  | k + 1 => B.advance m (run B m k)

theorem selected_ready {m k : ℕ} {s : ExecutionState vertices} {v : Fin vertices}
    (hk : (B.observe s).assignSlot m v = some k) :
    B.eligible (B.vertexBatch v) ≤ s.clock ∧ s.stamp v = none ∧
      ∀ u, I.edge u v → s.stamp u ≠ none := by
  have hs := (B.observe s).assignSlot_sound hk
  rcases (B.observe s).action_scope hs.2 with h | h
  · exact (mem_filter.mp h.2).2.2
  · exact (mem_filter.mp h.2).2.2

theorem preserves_stamp {m : ℕ} {s : ExecutionState vertices} {v : Fin vertices} {t : ℕ}
    (hv : s.stamp v = some t) : (B.advance m s).stamp v = some t := by
  unfold advance
  cases h : (B.observe s).assignSlot m v with
  | none => simp [h, hv]
  | some k =>
    have hn := (B.selected_ready h).2.1
    rw [hv] at hn
    cases hn

theorem completed_mono (m : ℕ) (s : ExecutionState vertices) :
    s.completed ⊆ (B.advance m s).completed := by
  intro v hv
  have hn := (mem_filter.mp hv).2
  cases h : s.stamp v with
  | none => exact False.elim (hn h)
  | some t => exact mem_filter.mpr ⟨mem_univ _, by rw [B.preserves_stamp h]; simp⟩

theorem clock_strict (m : ℕ) (s : ExecutionState vertices) : s.clock < (B.advance m s).clock := by
  have h := Packing.duration_pos (B.observe s |>.smallFront m).card m
  change s.clock < s.clock + (B.observe s).duration m
  exact Nat.lt_add_of_pos_right h

/-- Prefix feasibility invariant. Timestamps record only completed work;
every recorded predecessor completed earlier and every slot respects capacity. -/
structure Safe (m : ℕ) (s : ExecutionState vertices) : Prop where
  stamps : ∀ v t, s.stamp v = some t → B.eligible (B.vertexBatch v) ≤ t ∧ t < s.clock ∧
    ∀ u, I.edge u v → ∃ a, s.stamp u = some a ∧ a < t
  capacity : ∀ t, (univ.filter (fun v => s.stamp v = some t)).card ≤ m

omit [DecidableRel I.edge] in
theorem safe_initial (m : ℕ) : B.Safe m (ExecutionState.initial (vertices := vertices)) := by
  constructor
  · intro v t h; cases h
  · intro t; simp [ExecutionState.initial]

theorem safe_advance {m : ℕ} {s : ExecutionState vertices} (hs : B.Safe m s) :
    B.Safe m (B.advance m s) := by
  constructor
  · intro v t ht
    cases hk : (B.observe s).assignSlot m v with
    | none =>
      have hold : s.stamp v = some t := by simpa [advance, hk] using ht
      have h := hs.stamps v t hold
      refine ⟨h.1, h.2.1.trans (B.clock_strict m s), ?_⟩
      intro u he
      obtain ⟨a, ha, hat⟩ := h.2.2 u he
      exact ⟨a, B.preserves_stamp ha, hat⟩
    | some k =>
      have htime : s.clock + k = t := Option.some.inj (by simpa [advance, hk] using ht)
      have hr := B.selected_ready hk
      have hslot := (B.observe s).assignSlot_sound hk
      refine ⟨by omega, ?_, ?_⟩
      · change t < s.clock + (B.observe s).duration m
        omega
      · intro u he
        have hu := hr.2.2 u he
        cases ha : s.stamp u with
        | none => exact False.elim (hu ha)
        | some a =>
          have hat := (hs.stamps u a ha).2.1
          exact ⟨a, B.preserves_stamp ha, by omega⟩
  · intro t
    by_cases hbefore : t < s.clock
    · apply (card_le_card (t := univ.filter (fun v => s.stamp v = some t)) ?_).trans (hs.capacity t)
      intro v hv
      have hv' := (mem_filter.mp hv).2
      cases hk : (B.observe s).assignSlot m v with
      | none => exact mem_filter.mpr ⟨mem_univ _, by simpa [advance, hk] using hv'⟩
      | some k =>
        have he : s.clock + k = t := Option.some.inj (by simpa [advance, hk] using hv')
        omega
    · apply (card_le_card (t := (B.observe s).action m (t - s.clock)) ?_).trans
        ((B.observe s).action_card_le m (t - s.clock))
      intro v hv
      have hv' := (mem_filter.mp hv).2
      cases hk : (B.observe s).assignSlot m v with
      | none =>
        have hold : s.stamp v = some t := by simpa [advance, hk] using hv'
        have he := (hs.stamps v t hold).2.1
        omega
      | some k =>
        have he : s.clock + k = t := Option.some.inj (by simpa [advance, hk] using hv')
        have hslot := (B.observe s).assignSlot_sound hk
        have heq : k = t - s.clock := by omega
        simpa [heq] using hslot.2

theorem run_safe (m k : ℕ) : B.Safe m (B.run m k) := by
  induction k with
  | zero => exact B.safe_initial m
  | succ k ih => exact B.safe_advance ih

theorem run_clock_strict (m : ℕ) : StrictMono (fun k => (B.run m k).clock) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact B.clock_strict m (B.run m k)

theorem run_completed_mono (m : ℕ) : Monotone (fun k => (B.run m k).completed) := by
  apply monotone_nat_of_le_succ
  intro k
  exact B.completed_mono m (B.run m k)

end Batching
end Scheduling
