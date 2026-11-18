import Scheduling.Optimum
import Mathlib.Logic.Equiv.Fin.Basic

namespace Scheduling
open Finset

/-- A reserved processor handles the first `L` vertices of each job in its
arrival epoch. The other processors finish that job in the next epoch. -/
def pipelineTime (m L j k : ℕ) : ℕ :=
  j * L + if k < L then k else L + (k - L) / (m - 1)

def pipelineLane (m L k : ℕ) : ℕ :=
  if k < L then 0 else 1 + (k - L) % (m - 1)

theorem pipeline_remainder_lt {m L k : ℕ} (hm : 2 ≤ m) (hk : k < m * L) :
    (k - L) / (m - 1) < L := by
  have hp : 0 < m - 1 := by omega
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have he : m - 1 + 1 = m := by omega
  by_cases h : k < L
  · have hL : 0 < L := by nlinarith
    have : k - L = 0 := by omega
    rw [this]
    exact Nat.mul_pos hL hp
  · have : k - L + L = k := Nat.sub_add_cancel (by omega)
    nlinarith

theorem pipeline_epoch_bounds {m L j k : ℕ} (hm : 2 ≤ m) (hk : k < m * L) :
    let e := j + if k < L then 0 else 1
    e * L ≤ pipelineTime m L j k ∧ pipelineTime m L j k < (e + 1) * L := by
  have hr := pipeline_remainder_lt hm hk
  dsimp [pipelineTime]
  generalize (k - L) / (m - 1) = q at *
  split_ifs <;> simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero] <;> omega

theorem epoch_index_unique {L t j k : ℕ}
    (hj : j * L ≤ t ∧ t < (j + 1) * L)
    (hk : k * L ≤ t ∧ t < (k + 1) * L) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · have := Nat.mul_le_mul_right L (show j + 1 ≤ k by omega)
    omega
  · exact h
  · have := Nat.mul_le_mul_right L (show k + 1 ≤ j by omega)
    omega

theorem pipeline_injective {m L j k j' k' : ℕ} (hm : 2 ≤ m)
    (hk : k < m * L) (hk' : k' < m * L)
    (ht : pipelineTime m L j k = pipelineTime m L j' k')
    (hp : pipelineLane m L k = pipelineLane m L k') : j = j' ∧ k = k' := by
  have he := pipeline_epoch_bounds (j := j) hm hk
  have he' := pipeline_epoch_bounds (j := j') hm hk'
  rw [← ht] at he'
  have hj := epoch_index_unique he he'
  have hd := Nat.div_add_mod (k - L) (m - 1)
  have hd' := Nat.div_add_mod (k' - L) (m - 1)
  by_cases ha : k < L <;> by_cases hb : k' < L
  · simp only [ha, hb, if_pos, Nat.add_zero] at hj
    subst j'
    simp only [pipelineTime, if_pos ha, if_pos hb] at ht
    exact ⟨rfl, by omega⟩
  · simp only [pipelineLane, if_pos ha, if_neg hb] at hp
    exact False.elim (Nat.ne_of_lt (Nat.zero_lt_succ _) (by omega : 0 = (k' - L) % (m - 1) + 1))
  · simp [pipelineLane, ha, hb] at hp
  · simp only [ha, hb, if_false] at hj
    have hjj : j = j' := by omega
    subst j'
    simp only [pipelineTime, if_neg ha, if_neg hb] at ht
    simp only [pipelineLane, if_neg ha, if_neg hb] at hp
    have hq : (k - L) / (m - 1) = (k' - L) / (m - 1) := by omega
    rw [hq] at hd
    exact ⟨rfl, by omega⟩

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- A key-first ordering is enough for the two-epoch offline schedule.
The hypotheses concern the graph and its ordering, not a presumed schedule. -/
theorem pipeline_valid {m L : ℕ} (hm : 2 ≤ m)
    (position : Fin vertices → ℕ)
    (hpos : ∀ v, position v < m * L)
    (hinj : Function.Injective (fun v => (I.owner v, position v)))
    (hrelease : ∀ j, I.release j = j.val * L)
    (hedge : ∀ u v, I.edge u v → position u < L ∧ position u < position v) :
    I.Valid m (fun v => pipelineTime m L (I.owner v).val (position v)) := by
  classical
  constructor
  · intro v
    rw [hrelease]
    unfold pipelineTime
    omega
  · intro u v huv
    have ho := I.same_job huv
    have he := hedge u v huv
    change pipelineTime m L (I.owner u).val (position u) <
      pipelineTime m L (I.owner v).val (position v)
    simp only [pipelineTime, ho, if_pos he.1]
    generalize (position v - L) / (m - 1) = q
    split_ifs <;> omega
  · intro t
    have hlane : ∀ v, pipelineLane m L (position v) < m := by
      intro v
      have hr := Nat.mod_lt (position v - L) (show 0 < m - 1 by omega)
      unfold pipelineLane
      split_ifs <;> omega
    let f : Fin vertices → Fin m := fun v => ⟨pipelineLane m L (position v), hlane v⟩
    have hc := card_le_card_of_injOn f
      (t := (univ : Finset (Fin m))) (s := univ.filter (fun v =>
        pipelineTime m L (I.owner v).val (position v) = t)) (by simp)
      (by
        intro u hu v hv heq
        have ht := (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm
        have he := pipeline_injective hm (hpos u) (hpos v) ht (congrArg Fin.val heq)
        exact hinj (Prod.ext (Fin.ext he.1) he.2))
    simpa using hc

theorem pipeline_flowBound {m L : ℕ} (hm : 2 ≤ m)
    (position : Fin vertices → ℕ) (hpos : ∀ v, position v < m * L)
    (hrelease : ∀ j, I.release j = j.val * L) :
    I.FlowBound (fun v => pipelineTime m L (I.owner v).val (position v)) (2 * L) := by
  intro v
  have hr := pipeline_remainder_lt hm (hpos v)
  rw [hrelease]
  dsimp only [pipelineTime]
  split_ifs <;> omega

end Instance
end Scheduling
