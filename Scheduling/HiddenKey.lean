import Scheduling.PublicGraph

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- A temporary barrier hides a suffix until the entire current frontier
has executed. Its outgoing edges are never revealed during the prefix used
to select the key. -/
def gate (frontier hidden : Finset (Fin vertices))
    (hjob : ∀ u ∈ frontier, ∀ v ∈ hidden, I.owner u = I.owner v)
    (hrank : ∀ u ∈ frontier, ∀ v ∈ hidden, I.rank u < I.rank v) : Instance jobs vertices where
  owner := I.owner
  release := I.release
  edge u v := I.edge u v ∨ u ∈ frontier ∧ v ∈ hidden
  same_job := by
    intro u v h
    rcases h with h | h
    · exact I.same_job h
    · exact hjob u h.1 v h.2
  rank := I.rank
  rank_increases := by
    intro u v h
    rcases h with h | h
    · exact I.rank_increases h
    · exact hrank u h.1 v h.2
  nonempty_job := I.nonempty_job

end Instance

namespace DeterministicScheduler
variable {m jobs vertices : ℕ} (A : DeterministicScheduler m)

/-- Deferred key selection against an arbitrary causal scheduler. Run the
temporary barrier to find a last frontier vertex. Any acyclic completion
whose hidden suffix is blocked by that key or by other hidden vertices
preserves the entire prefix, including all revealed predecessor information. -/
theorem select_hidden_key (B : Instance jobs vertices)
    (frontier hidden : Finset (Fin vertices)) (hne : frontier.Nonempty)
    (hjob : ∀ u ∈ frontier, ∀ v ∈ hidden, B.owner u = B.owner v)
    (hrank : ∀ u ∈ frontier, ∀ v ∈ hidden, B.rank u < B.rank v) :
    ∃ key ∈ frontier,
      let I := B.gate frontier hidden hjob hrank
      (∀ v ∈ frontier, A.schedule I v ≤ A.schedule I key) ∧
      ∀ J : Instance jobs vertices,
        B.owner = J.owner → B.release = J.release →
        (∀ u v, v ∉ hidden → (B.edge u v ↔ J.edge u v)) →
        (∀ v ∈ hidden, ∃ u, J.edge u v ∧ (u = key ∨ u ∈ hidden)) →
        (∀ t ≤ A.schedule I key, executionSlot (A.schedule I) t = executionSlot (A.schedule J) t) ∧
        (∀ v ∈ frontier, A.schedule J v = A.schedule I v) ∧
        (∀ v ∈ frontier, A.schedule J v ≤ A.schedule J key) := by
  let I := B.gate frontier hidden hjob hrank
  obtain ⟨key, hk, hmax⟩ := exists_max_image frontier (A.schedule I) hne
  refine ⟨key, hk, hmax, ?_⟩
  intro J ho hr he hblocked
  have hI : ∀ v ∈ hidden, ∃ u, I.edge u v ∧ A.schedule I key ≤ A.schedule I u := by
    intro v hv
    exact ⟨key, Or.inr ⟨hk, hv⟩, le_rfl⟩
  have hJ : ∀ v ∈ hidden, ∃ u, J.edge u v ∧ A.schedule I key ≤ A.schedule I u := by
    intro v hv
    obtain ⟨u, hu, hloc⟩ := hblocked v hv
    refine ⟨u, hu, ?_⟩
    rcases hloc with rfl | hhidden
    · exact le_rfl
    · exact ((A.valid I).precedence (Or.inr ⟨hk, hhidden⟩)).le
  have hedge : ∀ u v, v ∉ hidden → (I.edge u v ↔ J.edge u v) := by
    intro u v hv
    change (B.edge u v ∨ u ∈ frontier ∧ v ∈ hidden) ↔ J.edge u v
    simp only [hv, and_false, or_false]
    exact he u v hv
  have htransfer := A.hidden_replacement I J hidden ho hr hedge hI hJ
  have htimes : ∀ v ∈ frontier, A.schedule J v = A.schedule I v :=
    fun v hv => htransfer.2 v (hmax v hv)
  refine ⟨htransfer.1, htimes, ?_⟩
  intro v hv
  rw [htimes v hv, htimes key hk]
  exact hmax v hv

end DeterministicScheduler
end Scheduling
