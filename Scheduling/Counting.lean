import Scheduling.Model

namespace Scheduling
open Finset

/-- Count work by its execution slots, using the capacity constraint. -/
theorem card_le_slots {V : Type*} [Fintype V] [DecidableEq V]
    (S : V → ℕ) (m a b : ℕ) (s : Finset V)
    (cap : ∀ t, (univ.filter (fun v => S v = t)).card ≤ m)
    (times : ∀ v ∈ s, a ≤ S v ∧ S v < b) :
    s.card ≤ m * (b - a) := by
  classical
  have heq : s.card = ∑ t ∈ Ico a b, (s.filter (fun v => S v = t)).card :=
    card_eq_sum_card_fiberwise (fun v hv => mem_Ico.mpr (times v hv))
  rw [heq]
  calc
    _ ≤ ∑ _t ∈ Ico a b, m := by
      apply sum_le_sum
      intro t _
      exact (card_le_card (by intro v hv; simp only [mem_filter, mem_univ, true_and] at *; exact hv.2)).trans (cap t)
    _ = m * (b - a) := by simp [Nat.mul_comm]

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Proposition 5(2), in the paper's inclusive release interval convention. -/
theorem arrival_work_bound {m L a b : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) :
    (univ.filter (fun v => a ≤ I.release (I.owner v) ∧ I.release (I.owner v) ≤ b)).card
      ≤ m * (b + L - a) := by
  classical
  apply card_le_slots O m a (b + L) _ hO.capacity
  intro v hv
  have h := (mem_filter.mp hv).2
  have := hO.release v
  have := hL v
  omega

theorem job_work_bound {m L : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) (j : Fin jobs) :
    (I.jobVertices j).card ≤ m * L := by
  classical
  have h := I.arrival_work_bound (a := I.release j) (b := I.release j) hO hL
  have hsub : I.jobVertices j ⊆
      univ.filter (fun v => I.release j ≤ I.release (I.owner v) ∧
        I.release (I.owner v) ≤ I.release j) := by
    intro v hv
    have ho := (mem_filter.mp hv).2
    simp_all
  exact (card_le_card hsub).trans (by simpa using h)

/-- Proposition 5(1): every nonempty directed path has at most L vertices.
The vertex sequence need not be assumed injective: precedence already forces
its execution times to increase. -/
theorem path_length_bound {m L n : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L)
    (p : Fin (n + 1) → Fin vertices)
    (he : ∀ k : Fin n, I.edge (p k.castSucc) (p k.succ)) : n + 1 ≤ L := by
  have hpath : ∀ k : Fin (n + 1),
      I.owner (p k) = I.owner (p 0) ∧
      I.release (I.owner (p 0)) + k.val ≤ O (p k) := by
    intro k
    induction k using Fin.induction with
    | zero => exact ⟨rfl, by simpa using hO.release (p 0)⟩
    | succ k ih =>
      simp only [Fin.val_castSucc] at ih
      have hp := hO.precedence (he k)
      have ho := I.same_job (he k)
      exact ⟨ho.symm.trans ih.1, by simpa using (show I.release (I.owner (p 0)) + (k.val + 1) ≤ O (p k.succ) by omega)⟩
  have hlast := hpath (Fin.last n)
  have hb := hL (p (Fin.last n))
  rw [hlast.1] at hb
  simp only [Fin.val_last] at hlast
  omega

/-- Every nonempty finite residual DAG has a ready vertex. The proof descends
in the supplied topological rank, rather than assuming a ready vertex exists. -/
theorem exists_ready {S : Assignment (vertices := vertices)} {j : Fin jobs} {t : ℕ}
    (hr : I.release j ≤ t) (hu : ∃ v, I.owner v = j ∧ t ≤ S v) :
    ∃ v, I.owner v = j ∧ I.Ready S t v := by
  classical
  have aux : ∀ n v, I.rank v = n → I.owner v = j → t ≤ S v →
      ∃ w, I.owner w = j ∧ I.Ready S t w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hj ht
      by_cases hpred : ∀ u, I.edge u v → S u < t
      · exact ⟨v, hj, by rw [Ready, hj]; exact ⟨hr, ht, hpred⟩⟩
      · push Not at hpred
        obtain ⟨u, he, hu⟩ := hpred
        exact ih (I.rank u) (by have := I.rank_increases he; omega) u rfl
          ((I.same_job he).trans hj) hu
  obtain ⟨v, hj, ht⟩ := hu
  exact aux (I.rank v) v rfl hj ht

end Instance
end Scheduling
