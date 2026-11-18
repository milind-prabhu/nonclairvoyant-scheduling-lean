import Scheduling.SFFInterference
import Scheduling.Optimum

namespace Scheduling.SFFRounds
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches m L : ℕ} {I : Instance jobs vertices}
variable {B : Batching I L batches} {S O : Assignment (vertices := vertices)}
variable (R : SFFRounds B m S)
include R

theorem boundary_ge_index (k : ℕ) : k ≤ R.boundary k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have h := R.strict (show k < k + 1 by omega)
    omega

theorem exists_admission (b : Fin batches) : ∃ k, B.eligible b ≤ R.boundary k :=
  ⟨B.eligible b, R.boundary_ge_index _⟩

noncomputable def admission (b : Fin batches) : ℕ := Nat.find (R.exists_admission b)

theorem admitted (b : Fin batches) : B.eligible b ≤ R.boundary (R.admission b) :=
  Nat.find_spec (R.exists_admission b)

theorem admission_delay (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L) (b : Fin batches) :
    R.boundary (R.admission b) ≤ B.eligible b + 4 * L := by
  have hp : 0 < R.admission b := by
    have h := R.admitted b
    by_contra hn
    have hz : R.admission b = 0 := by omega
    rw [hz, R.starts_zero] at h
    have := B.eligible_positive hLp b
    omega
  have hprev : R.boundary (R.admission b - 1) < B.eligible b := by
    by_contra hn
    have hmin := Nat.find_min' (R.exists_admission b) (show B.eligible b ≤ R.boundary (R.admission b - 1) by omega)
    change R.admission b ≤ R.admission b - 1 at hmin
    omega
  have hround := (R.round_bounds hm hLp hO hL (R.admission b - 1)).2
  have he : R.admission b - 1 + 1 = R.admission b := by omega
  rw [he] at hround
  have hmono := R.strict.monotone (Nat.sub_le (R.admission b) 1)
  omega

/-- Theorem 10, for any schedule obeying the operational SFF round routine.
The 44L² bound is derived here from backlog, interference, round lengths,
eligibility spacing, and frontier progress. None is an assumed guarantee. -/
theorem flow_bound (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L) : I.FlowBound S (44 * L ^ 2) := by
  intro v
  let b := B.vertexBatch v
  let A := R.admission b
  have hadmit : B.eligible b ≤ R.boundary A := R.admitted b
  have hdelay : R.boundary A ≤ B.eligible b + 4 * L := R.admission_delay hm hLp hO hL b
  have hrel : B.eligible b ≤ I.release (I.owner v) + 2 * L := by
    have hl := B.lower (I.owner v)
    dsimp [b, Batching.eligible, Batching.vertexBatch]
    nlinarith
  by_cases hearly : S v < R.boundary A
  · have harith : 6 * L ≤ 44 * L ^ 2 := by nlinarith
    omega
  · have hAv : R.boundary A ≤ S v := by omega
    have hAK : A ≤ S v + 1 := by have := R.boundary_ge_index A; omega
    have hKv : S v < R.boundary (S v + 1) := by have := R.boundary_ge_index (S v + 1); omega
    obtain ⟨r, hAr, hrK, hrv, hvr⟩ := R.containing_round hAK hAv hKv
    have hactive : ∀ k, A ≤ k → k < r + 1 → B.Active S (R.boundary k) b := by
      intro k hAk hkr
      have h₁ := R.strict.monotone hAk
      have h₂ := R.strict.monotone (show k ≤ r by omega)
      exact ⟨by omega, v, rfl, by omega⟩
    have hd := R.unfinished_interval_bound hm hLp hO hL (show A ≤ r + 1 by omega) hadmit hactive
    have ht := R.strict.monotone (show A ≤ r + 1 by omega)
    have harith : 32 * L ^ 2 + 10 * L ≤ 44 * L ^ 2 := by nlinarith
    omega

theorem maxFlow_bound (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L) : I.maxFlow S ≤ 44 * L ^ 2 :=
  (I.flowBound_iff_maxFlow_le S _).mp (R.flow_bound hm hLp hO hL)

end Scheduling.SFFRounds

namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- Canonical number of 2L-windows, allowing empty intermediate batches. -/
def batchCount (L : ℕ) : ℕ :=
  univ.sup (fun j => I.release j / (2 * L) + 1)

def canonicalBatching (L : ℕ) (hL : 0 < L) : Batching I L (I.batchCount L) where
  index := fun j => ⟨I.release j / (2 * L), by
    have h : I.release j / (2 * L) + 1 ≤ I.batchCount L :=
      le_sup (f := fun j => I.release j / (2 * L) + 1) (mem_univ j)
    omega⟩
  lower := by
    intro j
    have h := Nat.mod_add_div (I.release j) (2 * L)
    dsimp
    omega
  upper := by
    intro j
    have h := Nat.mod_add_div (I.release j) (2 * L)
    have hm := Nat.mod_lt (I.release j) (show 0 < 2 * L by omega)
    dsimp
    nlinarith

/-- Theorem 10 specialized to canonical batches and the actual attained
offline optimum, for a nonempty collection of jobs. -/
theorem sff_known_optimum {m : ℕ} {S : Assignment (vertices := vertices)}
    (hm : 0 < m) (hj : 0 < jobs)
    (R : SFFRounds (I.canonicalBatching (I.optimum m hm) (I.optimum_pos hm hj)) m S) :
    I.maxFlow S ≤ 44 * (I.optimum m hm) ^ 2 := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  exact R.maxFlow_bound hm (I.optimum_pos hm hj) hO hL

end Scheduling.Instance
