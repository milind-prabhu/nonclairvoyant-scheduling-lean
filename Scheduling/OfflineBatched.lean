import Scheduling.OfflinePipeline

namespace Scheduling
open Finset

/-- Keys use one reserved processor; leaves are packed on the other
processors during the same arrival epoch. -/
def batchedTime (m L j k : ℕ) : ℕ :=
  j * L + if k < L then k else (k - L) / (m - 1)

theorem batched_epoch_bounds {m L j k : ℕ} (hm : 2 ≤ m) (hk : k < m * L) :
    j * L ≤ batchedTime m L j k ∧ batchedTime m L j k < (j + 1) * L := by
  have hr := pipeline_remainder_lt hm hk
  dsimp [batchedTime]
  generalize (k - L) / (m - 1) = q at *
  split_ifs <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega

theorem batched_injective {m L j k j' k' : ℕ} (hm : 2 ≤ m)
    (hk : k < m * L) (hk' : k' < m * L)
    (ht : batchedTime m L j k = batchedTime m L j' k')
    (hp : pipelineLane m L k = pipelineLane m L k') : j = j' ∧ k = k' := by
  have he := batched_epoch_bounds (j := j) hm hk
  have he' := batched_epoch_bounds (j := j') hm hk'
  rw [← ht] at he'
  have hj := epoch_index_unique he he'
  subst j'
  have htime : pipelineTime m L j k = pipelineTime m L j k' := by
    by_cases ha : k < L <;> by_cases hb : k' < L
    · simpa only [pipelineTime, batchedTime, if_pos ha, if_pos hb] using ht
    · simp only [pipelineLane, if_pos ha, if_neg hb] at hp
      omega
    · simp [pipelineLane, ha, hb] at hp
    · simp only [batchedTime, if_neg ha, if_neg hb] at ht
      simp only [pipelineTime, if_neg ha, if_neg hb]
      omega
  exact pipeline_injective hm hk hk' htime hp

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- The prefix-balance condition is used to place each leaf late enough
for its parent key. Capacity and all other constraints follow from the
key-first indexing itself. -/
theorem batched_valid {m L : ℕ} (hm : 2 ≤ m)
    (position : Fin vertices → ℕ) (hpos : ∀ v, position v < m * L)
    (hinj : Function.Injective (fun v => (I.owner v, position v)))
    (hrelease : ∀ j, I.release j = j.val * L)
    (hedge : ∀ u v, I.edge u v → position u < L ∧
      (if position v < L then position u < position v
       else (position u + 1) * (m - 1) ≤ position v - L)) :
    I.Valid m (fun v => batchedTime m L (I.owner v).val (position v)) := by
  classical
  constructor
  · intro v
    rw [hrelease]
    exact (batched_epoch_bounds hm (hpos v)).1
  · intro u v huv
    have ho := I.same_job huv
    have he := hedge u v huv
    change batchedTime m L (I.owner u).val (position u) <
      batchedTime m L (I.owner v).val (position v)
    simp only [batchedTime, ho, if_pos he.1]
    by_cases hv : position v < L
    · simp only [if_pos hv] at he ⊢
      omega
    · simp only [if_neg hv] at he ⊢
      have hdiv := (Nat.le_div_iff_mul_le (show 0 < m - 1 by omega)).mpr he.2
      omega
  · intro t
    have hlane : ∀ v, pipelineLane m L (position v) < m := by
      intro v
      have hr := Nat.mod_lt (position v - L) (show 0 < m - 1 by omega)
      unfold pipelineLane
      split_ifs <;> omega
    let f : Fin vertices → Fin m := fun v => ⟨pipelineLane m L (position v), hlane v⟩
    have hc := card_le_card_of_injOn f
      (t := (univ : Finset (Fin m))) (s := univ.filter (fun v =>
        batchedTime m L (I.owner v).val (position v) = t)) (by simp) (by
        intro u hu v hv heq
        have ht := (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm
        have he := batched_injective hm (hpos u) (hpos v) ht (congrArg Fin.val heq)
        exact hinj (Prod.ext (Fin.ext he.1) he.2))
    simpa using hc

theorem batched_flowBound {m L : ℕ} (hm : 2 ≤ m)
    (position : Fin vertices → ℕ) (hpos : ∀ v, position v < m * L)
    (hrelease : ∀ j, I.release j = j.val * L) :
    I.FlowBound (fun v => batchedTime m L (I.owner v).val (position v)) L := by
  intro v
  rw [hrelease]
  have hh := (batched_epoch_bounds hm (hpos v) (j := (I.owner v).val)).2
  simpa only [Nat.add_mul, Nat.one_mul] using hh

end Instance
end Scheduling
