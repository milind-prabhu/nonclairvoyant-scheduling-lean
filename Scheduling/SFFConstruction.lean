import Scheduling.ExecutionBridge

namespace Scheduling.Batching
open Finset
variable {jobs vertices batches L : ℕ} {I : Instance jobs vertices}
variable (B : Batching I L batches) [DecidableRel I.edge]

/-- All operational SFF round properties are realized by the deterministic
ready-snapshot executor. No operational property is supplied as a hypothesis. -/
def execution_rounds {m : ℕ} (hm : 0 < m) : SFFRounds B m (B.execution m) where
  boundary := fun k => (B.run m k).clock
  starts_zero := rfl
  strict := B.run_clock_strict m
  filler := fun k => (B.observe (B.run m k)).filler m
  clear_small := by
    classical
    intro k b hb v hv hr
    have hq : b ∈ (B.observe (B.run m k)).small m := by rwa [B.observed_small_eq hm]
    have he := (mem_filter.mp hb).2.1.1
    have hready := (B.observed_ready_iff hm b v).mpr ⟨hv, he, hr⟩
    obtain ⟨j, hj, hvj⟩ := (B.observe (B.run m k)).clears_small hm hq hready
    have ht := (B.action_iff_execution hm hj v).mp hvj
    change B.execution m v < (B.run m k).clock + (B.observe (B.run m k)).duration m
    omega
  large_service := by
    classical
    intro k v ht₁ ht₂ hl
    have hj : B.execution m v - (B.run m k).clock < (B.observe (B.run m k)).duration m := by
      change B.execution m v < (B.run m k).clock + (B.observe (B.run m k)).duration m at ht₂
      omega
    have hv := (B.action_iff_execution hm hj v).mpr (by omega)
    rcases (B.observe (B.run m k)).action_scope hv with hs | hf
    · have hs' : B.vertexBatch v ∈ B.small m (B.execution m) (B.run m k).clock := by
        have hs₀ := hs.1
        rw [B.observed_small_eq hm] at hs₀
        exact hs₀
      exact False.elim (disjoint_left.mp (B.small_large_disjoint m (B.execution m) (B.run m k).clock) hs' hl)
    · exact hf.1
  length_eq := by
    classical
    intro k
    change ((B.run m k).clock + (B.observe (B.run m k)).duration m) - (B.run m k).clock = _
    rw [Nat.add_sub_cancel_left]
    change Packing.duration ((B.observe (B.run m k)).smallFront m).card m = _
    rw [B.observed_smallFront_eq hm]
    rfl
  eligible_service := by
    classical
    intro v
    exact ((B.run_safe m B.completionRound).stamps v (B.execution m v) (B.execution_stamp hm v)).1
  packed := by
    classical
    intro k t ht₁ ht₂
    have htend : t < (B.run m (k + 1)).clock := by omega
    rw [B.execution_slot_eq hm ht₁ htend]
    apply (B.observe (B.run m k)).nonfinal_full hm
    change t + 1 < (B.run m k).clock + (B.observe (B.run m k)).duration m at ht₂
    omega
  fill_last := by
    classical
    intro k hl t ht₁ ht₂
    have hq : ((B.observe (B.run m k)).large m).Nonempty := by rwa [B.observed_large_eq hm]
    rw [B.execution_slot_eq hm ht₁ ht₂]
    apply (B.observe (B.run m k)).full_with_large hm ?_ hq
    change t < (B.run m k).clock + (B.observe (B.run m k)).duration m at ht₂
    omega
  service_scope := by
    classical
    intro k v ht₁ ht₂
    have hj : B.execution m v - (B.run m k).clock < (B.observe (B.run m k)).duration m := by
      change B.execution m v < (B.run m k).clock + (B.observe (B.run m k)).duration m at ht₂
      omega
    have hv := (B.action_iff_execution hm hj v).mpr (by omega)
    rcases (B.observe (B.run m k)).action_scope hv with hs | hf
    · have hs' : B.vertexBatch v ∈ B.small m (B.execution m) (B.run m k).clock := by
        have hs₀ := hs.1
        rw [B.observed_small_eq hm] at hs₀
        exact hs₀
      exact Or.inl ⟨hs', ((B.observed_ready_iff hm _ v).mp hs.2).2.2⟩
    · exact Or.inr hf.1
  filler_oldest := by
    classical
    intro k b c hb hc
    have hc' : c ∈ (B.observe (B.run m k)).large m := by rwa [B.observed_large_eq hm]
    have hle := (B.observe (B.run m k)).filler_oldest hb hc'
    change b.val ≤ c.val at hle
    exact Nat.mul_le_mul_left (2 * L) (by omega)

theorem execution_flow_bound {m : ℕ} (hm : 0 < m) (hLp : 0 < L)
    {O : Assignment (vertices := vertices)} (hO : I.Valid m O) (hL : I.FlowBound O L) :
    I.maxFlow (B.execution m) ≤ 44 * L ^ 2 :=
  (B.execution_rounds hm).maxFlow_bound hm hLp hO hL

end Scheduling.Batching

namespace Scheduling.Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices) [DecidableRel I.edge]

/-- The executable scheduler takes a positive flow upper-bound guess L.
The finite horizon is used only to extract all timestamps from its online
round execution, whose decisions depend on ready snapshots. -/
def sffSchedule (m L : ℕ) (hL : 0 < L) : Assignment (vertices := vertices) :=
  (I.canonicalBatching L hL).execution m

theorem sffSchedule_valid {m L : ℕ} (hm : 0 < m) (hL : 0 < L) :
    I.Valid m (I.sffSchedule m L hL) :=
  (I.canonicalBatching L hL).execution_valid hm

theorem sffSchedule_bound {m L : ℕ} (hm : 0 < m) (hLp : 0 < L)
    {O : Assignment (vertices := vertices)} (hO : I.Valid m O) (hL : I.FlowBound O L) :
    I.maxFlow (I.sffSchedule m L hLp) ≤ 44 * L ^ 2 :=
  (I.canonicalBatching L hLp).execution_flow_bound hm hLp hO hL

/-- The SFF guarantee for the constructed scheduler at the actual optimum.
Unlike `sff_known_optimum`, this theorem takes no round-execution witness. -/
theorem sffSchedule_known_optimum {m : ℕ} (hm : 0 < m) (hj : 0 < jobs) :
    I.maxFlow (I.sffSchedule m (I.optimum m hm) (I.optimum_pos hm hj)) ≤
      44 * (I.optimum m hm) ^ 2 := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  exact I.sffSchedule_bound hm (I.optimum_pos hm hj) hO hL

omit [DecidableRel I.edge] in
/-- The existence part of the known-bound upper theorem, with no assumed
SFF execution. Decidable readiness is used only by the environment simulator. -/
theorem exists_sff_schedule {m L : ℕ} (hm : 0 < m) (hLp : 0 < L)
    {O : Assignment (vertices := vertices)} (hO : I.Valid m O) (hL : I.FlowBound O L) :
    ∃ S : Assignment (vertices := vertices), I.Valid m S ∧ I.maxFlow S ≤ 44 * L ^ 2 := by
  classical
  exact ⟨I.sffSchedule m L hLp, I.sffSchedule_valid hm hLp, I.sffSchedule_bound hm hLp hO hL⟩

end Scheduling.Instance
