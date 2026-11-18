import Scheduling.StarChainFIFO

namespace Scheduling.StarChain
open Finset
attribute [local instance] Classical.propDecidable

theorem consistent_flow_lower {jobs m : ℕ} (hm : 2 ≤ m)
    (hn : jobs = (3 * (m - 1) + 1) * m * m)
    (long : Fin jobs → Bool) (S : Assignment (vertices := jobs * (3 * m)))
    (hS : (toInstance long (show 0 < m by omega)).Valid m S)
    (hfifo : (toInstance long (show 0 < m by omega)).IsFIFO m S)
    (hc : ∀ j, TypeConsistent long (show 0 < m by omega) S j) :
    3 * (m - 1) ≤ (toInstance long (show 0 < m by omega)).maxFlow S := by
  let I := toInstance long (show 0 < m by omega)
  let B := 3 * (m - 1) + 1
  let N := 3 * m * m
  have hB : 0 < B := by dsimp [B]; omega
  by_contra hh
  change ¬ 3 * (m - 1) ≤ I.maxFlow S at hh
  have hflow : I.FlowBound S (3 * (m - 1)) :=
    (I.flowBound_iff_maxFlow_le S _).mpr (by omega)
  have hidle : ∀ k < N, I.epochWork S B k < m * B := by
    intro k _
    obtain ⟨t, ht, hidle⟩ := block_has_idle hS hfifo hflow hc (k * B)
    have ht' : t ∈ Ico (k * B) ((k + 1) * B) := by
      simpa only [Nat.add_mul, Nat.one_mul] using ht
    exact I.epochWork_lt_of_idle hS hB ht' hidle
  have hacc : N ≤ Accounting.idleBacklog (m * B) (I.epochWork S B) N := by
    simpa only [Nat.one_mul] using
      Accounting.forcing_epochs_accumulate (c := 1) (K := N) (by omega)
        (by simpa only [Nat.one_mul] using hidle)
  have hvcount : jobs * (3 * m) = N * (m * B) := by rw [hn]; dsimp [N, B]; ring
  have htime : N * B = jobs * 3 := by rw [hn]; dsimp [N, B]; ring
  rw [I.idleBacklog_eq_remaining hS hB hvcount, htime] at hacc
  have hcj : m - 1 ≤ jobs := by
    have hprod := Nat.mul_le_mul_right (m * m) (show 1 ≤ B from hB)
    have hm2 : m ≤ m * m := by nlinarith
    change jobs = B * m * m at hn
    rw [Nat.mul_assoc] at hn
    simp only [Nat.one_mul] at hprod
    omega
  have hwork : ∀ j, (I.jobVertices j).card = m * 3 := by
    intro j
    simpa [Nat.mul_comm] using jobVertices_card long (show 0 < m by omega) j
  have hflow' : I.FlowBound S ((m - 1) * 3) := by
    simpa only [Nat.mul_comm] using hflow
  have hy := I.regular_young_backlog hcj (by omega : 0 < 3) (by intros; rfl) hwork hflow'
  have hsub : m - 1 - 1 + 2 = m := by omega
  change 3 * m * m ≤ _ at hacc
  nlinarith

end Scheduling.StarChain

namespace Scheduling

/-- The FIFO lower bound on trees with constant optimum. The finite
instance is derived from the scheduler's causality and FIFO properties;
no adaptive trace or type-consistency premise remains in the conclusion. -/
theorem fifo_constant_optimum_lower {m : ℕ} (hm : 2 ≤ m)
    (A : DeterministicScheduler m)
    (hfifo : ∀ {jobs vertices} (I : Instance jobs vertices), I.IsFIFO m (A.schedule I)) :
    ∃ (jobs vertices : ℕ) (I : Instance jobs vertices),
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) ≤ 6 ∧
      3 * (m - 1) ≤ I.maxFlow (A.schedule I) := by
  let n := (3 * (m - 1) + 1) * m * m
  obtain ⟨long, hc⟩ := StarChain.exists_type_consistent A (show 0 < m by omega) n
  let I := StarChain.toInstance long (show 0 < m by omega)
  refine ⟨n, n * (3 * m), I, ?_, ?_, ?_⟩
  · intro u v w hu hv
    exact StarChain.at_most_one_parent long (show 0 < m by omega) hu hv
  · exact StarChain.optimum_le_six long hm
  · exact StarChain.consistent_flow_lower hm rfl long (A.schedule I) (A.valid I) (hfifo I) hc

theorem fifo_competitive_lower {m : ℕ} (hm : 2 ≤ m)
    (A : DeterministicScheduler m)
    (hfifo : ∀ {jobs vertices} (I : Instance jobs vertices), I.IsFIFO m (A.schedule I)) :
    ∃ (jobs vertices : ℕ) (I : Instance jobs vertices),
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) ≤ 6 ∧
      m * I.optimum m (by omega) ≤ 4 * I.maxFlow (A.schedule I) := by
  obtain ⟨jobs, vertices, I, htree, hopt, hflow⟩ := fifo_constant_optimum_lower hm A hfifo
  refine ⟨jobs, vertices, I, htree, hopt, ?_⟩
  have hm1 : m - 1 + 1 = m := by omega
  nlinarith

end Scheduling
