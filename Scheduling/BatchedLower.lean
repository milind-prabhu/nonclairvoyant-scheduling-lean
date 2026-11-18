import Scheduling.BatchedForcing
import Mathlib.Data.Nat.Log

namespace Scheduling
attribute [local instance] Classical.propDecidable

/-- The deterministic batched lower bound, with the paper's explicit
scale and finite number of jobs. All releases are multiples of the
attained optimum; no adversarial trace is assumed. -/
theorem batched_lower_bound {m c : ℕ} (hm : 2 ≤ m) (hc : 0 < c) (hcm : 2 * c ≤ m)
    (A : DeterministicScheduler m) :
    ∃ I : Instance (c * (m * (8 * c * 5 ^ c)))
        ((c * (m * (8 * c * 5 ^ c))) * (m * (8 * c * 5 ^ c))),
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) = 8 * c * 5 ^ c ∧
      (∀ j, I.release j = j.val * I.optimum m (by omega)) ∧
      c * I.optimum m (by omega) ≤ I.maxFlow (A.schedule I) := by
  let L := 8 * c * 5 ^ c
  have hL : 0 < L := Nat.mul_pos (Nat.mul_pos (by omega) hc) (pow_pos (by omega) c)
  have hdiv : 2 ∣ L := ⟨4 * c * 5 ^ c, by dsimp [L]; ring⟩
  have heven : 2 * (L / 2) = L := by
    have := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hw : 0 < m * L := Nat.mul_pos (by omega) hL
  obtain ⟨Q, records, hrun, _, hforest⟩ := BatchedAdversary.exists_candidate (c * (m * L)) m L hm hL A
  have hj : 0 < c * (m * L) := Nat.mul_pos hc hw
  have hopt := BatchedAdversary.optimum_eq hm hL heven hj A hrun
  refine ⟨Q.toInstance L hw, hforest, hopt, ?_, ?_⟩
  · intro j
    rw [hopt]
    rfl
  · rw [hopt]
    exact BatchedAdversary.flow_lower hm hL heven hc hcm rfl A hrun rfl

theorem batched_scale_clog_le {c : ℕ} (hc : 0 < c) : Nat.clog 2 (8 * c * 5 ^ c) ≤ 7 * c := by
  apply Nat.clog_le_of_le_pow
  have h8 : 8 ≤ 2 ^ (3 * c) := by
    have hh := Nat.pow_le_pow_right (by omega : 0 < 2) (show 3 ≤ 3 * c by omega)
    norm_num at hh
    exact hh
  have hc2 : c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
  have h5 : 5 ^ c ≤ 2 ^ (3 * c) := by
    calc
      5 ^ c ≤ 8 ^ c := Nat.pow_le_pow_left (by omega) c
      _ = 2 ^ (3 * c) := by rw [pow_mul]; norm_num
  calc
    8 * c * 5 ^ c ≤ 2 ^ (3 * c) * 2 ^ c * 2 ^ (3 * c) := Nat.mul_le_mul (Nat.mul_le_mul h8 hc2) h5
    _ = 2 ^ (7 * c) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- The logarithmic batched lower bound with an explicit absolute
constant, at every scale `8*c*5^c` permitted by `2*c ≤ m`. -/
theorem batched_competitive_lower {m c : ℕ} (hm : 2 ≤ m) (hc : 0 < c) (hcm : 2 * c ≤ m)
    (A : DeterministicScheduler m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      I.optimum m (by omega) = 8 * c * 5 ^ c ∧
      (∀ j, I.release j = j.val * I.optimum m (by omega)) ∧
      min m (Nat.clog 2 (I.optimum m (by omega))) * I.optimum m (by omega) ≤
        7 * I.maxFlow (A.schedule I) := by
  obtain ⟨I, hforest, hopt, hrelease, hflow⟩ := batched_lower_bound hm hc hcm A
  refine ⟨_, _, I, hforest, hopt, hrelease, ?_⟩
  have hlog : Nat.clog 2 (I.optimum m (by omega)) ≤ 7 * c := by
    rw [hopt]
    exact batched_scale_clog_le hc
  have hmin := (min_le_right m (Nat.clog 2 (I.optimum m (by omega)))).trans hlog
  have hmul := Nat.mul_le_mul_right (I.optimum m (by omega)) hmin
  nlinarith

end Scheduling
