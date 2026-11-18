import Scheduling.FiniteForests

namespace Scheduling.HardFamily
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs m c L : ℕ}

/-- A fixed finite family, independent of the online scheduler. It may
contain more forests than the adaptive adversary generates; every member
has the offline guarantee needed by the general lower bound. -/
noncomputable def general (jobs m L : ℕ) (hm : 0 < m) (hL : 0 < L) :
    Finset (ForestCode jobs (m * L)) :=
  univ.filter (fun P => L ≤ (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm ∧
    (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm ≤ 2 * L)

/-- The batched family has exact optimum `L`, so concatenating copies
at multiples of `L` can preserve the batched-arrival restriction. -/
noncomputable def batched (jobs m L : ℕ) (hm : 0 < m) (hL : 0 < L) :
    Finset (ForestCode jobs (m * L)) :=
  univ.filter (fun P => (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm = L)

theorem mem_general {hm : 0 < m} {hL : 0 < L} (P : ForestCode jobs (m * L)) :
    P ∈ general jobs m L hm hL ↔
      L ≤ (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm ∧
      (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm ≤ 2 * L := by
  simp only [general, mem_filter, mem_univ, true_and]

theorem mem_batched {hm : 0 < m} {hL : 0 < L} (P : ForestCode jobs (m * L)) :
    P ∈ batched jobs m L hm hL ↔ (P.toInstance L (Nat.mul_pos hm hL)).optimum m hm = L := by
  simp only [batched, mem_filter, mem_univ, true_and]

theorem general_offline {hm : 0 < m} {hL : 0 < L} {P : ForestCode jobs (m * L)}
    (hP : P ∈ general jobs m L hm hL) :
    ∃ O, (P.toInstance L (Nat.mul_pos hm hL)).Valid m O ∧
      (P.toInstance L (Nat.mul_pos hm hL)).FlowBound O (2 * L) := by
  let I := P.toInstance L (Nat.mul_pos hm hL)
  obtain ⟨O, hO, hflow⟩ := I.optimum_attained hm
  refine ⟨O, hO, ?_⟩
  have hb := (mem_general P).mp hP
  intro v
  exact (hflow v).trans_le (Nat.add_le_add_left hb.2 _)

theorem batched_offline {hm : 0 < m} {hL : 0 < L} {P : ForestCode jobs (m * L)}
    (hP : P ∈ batched jobs m L hm hL) :
    ∃ O, (P.toInstance L (Nat.mul_pos hm hL)).Valid m O ∧
      (P.toInstance L (Nat.mul_pos hm hL)).FlowBound O L := by
  let I := P.toInstance L (Nat.mul_pos hm hL)
  obtain ⟨O, hO, hflow⟩ := I.optimum_attained hm
  have he := (mem_batched P).mp hP
  change I.optimum m hm = L at he
  exact ⟨O, hO, by simpa only [he] using hflow⟩

/-- Every deterministic causal scheduler has a hard member of the same
finite family. The family itself does not depend on that scheduler. -/
theorem general_hard (hm : 2 ≤ m) (hc : 0 < c) (hL : 0 < L)
    (heven : 2 * (L / 2) = L) (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (A : DeterministicScheduler m) :
    ∃ P ∈ general (c * (c * (m * L))) m L (by omega) hL,
      c * L ≤ (P.toInstance L (Nat.mul_pos (by omega) hL)).maxFlow
        (A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL))) := by
  have hm0 : 0 < m := by omega
  have hw : 0 < m * L := Nat.mul_pos hm0 hL
  obtain ⟨Q, records, hrun, _, _⟩ := LayeredPrefix.exists_recorded_forcing_forest
    (jobs := c * (c * (m * L))) (work := m * L) (L := L) (c := c) hm0 hw A
  have he := ForestCode.ofPrefix_toInstance Q L hw hrun.completion.finished
  have hj : 0 < c * (c * (m * L)) := Nat.mul_pos hc (Nat.mul_pos hc hw)
  refine ⟨ForestCode.ofPrefix Q, ?_, ?_⟩
  · apply (mem_general _).mpr
    rw [he]
    exact hrun.optimum_bounds hm hj rfl heven
  · rw [he]
    exact hrun.flow_lower hc hL heven hcL hcm rfl rfl

theorem batched_hard (hm : 2 ≤ m) (hc : 0 < c) (hL : 0 < L)
    (heven : 2 * (L / 2) = L) (hcm : 2 * c ≤ m) (hscale : L = 8 * c * 5 ^ c)
    (A : DeterministicScheduler m) :
    ∃ P ∈ batched (c * (m * L)) m L (by omega) hL,
      c * L ≤ (P.toInstance L (Nat.mul_pos (by omega) hL)).maxFlow
        (A.schedule (P.toInstance L (Nat.mul_pos (by omega) hL))) := by
  have hw : 0 < m * L := Nat.mul_pos (by omega) hL
  obtain ⟨Q, records, hrun, _, _⟩ := BatchedAdversary.exists_candidate (c * (m * L)) m L hm hL A
  obtain ⟨staticRule, hr⟩ := hrun.flexible.recorded
  have he := ForestCode.ofPrefix_toInstance Q L hw hr.completion.finished
  have hj : 0 < c * (m * L) := Nat.mul_pos hc hw
  refine ⟨ForestCode.ofPrefix Q, ?_, ?_⟩
  · apply (mem_batched _).mpr
    rw [he]
    exact BatchedAdversary.optimum_eq hm hL heven hj A hrun
  · rw [he]
    exact BatchedAdversary.flow_lower hm hL heven hc hcm hscale A hrun rfl

end Scheduling.HardFamily
