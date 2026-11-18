import Scheduling.Termination

namespace Scheduling.Batching
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches L : ℕ} {I : Instance jobs vertices}
variable (B : Batching I L batches) [DecidableRel I.edge]

/-- Work first stamped after a prefix cannot receive a timestamp before the
prefix clock. This connects the finite simulation to the total assignment. -/
theorem future_stamp_lower {m a b : ℕ} (hab : a ≤ b) {v : Fin vertices} {t : ℕ}
    (hn : (B.run m a).stamp v = none) (ht : (B.run m b).stamp v = some t) :
    (B.run m a).clock ≤ t := by
  induction b, hab using Nat.le_induction with
  | base => rw [hn] at ht; cases ht
  | succ b hab ih =>
    cases hk : (B.observe (B.run m b)).assignSlot m v with
    | none =>
      have hp : (B.run m b).stamp v = some t := by simpa [run, advance, hk] using ht
      exact ih hp
    | some k =>
      have hp : (B.run m b).clock + k = t := Option.some.inj (by simpa [run, advance, hk] using ht)
      have hm := (B.run_clock_strict m).monotone hab
      omega

theorem run_stamp_exact {m : ℕ} (hm : 0 < m) (k : ℕ) (v : Fin vertices) :
    (B.run m k).stamp v =
      if B.execution m v < (B.run m k).clock then some (B.execution m v) else none := by
  by_cases hk : k ≤ B.completionRound
  · cases hs : (B.run m k).stamp v with
    | none =>
      have hl := B.future_stamp_lower hk hs (B.execution_stamp hm v)
      simp [show ¬B.execution m v < (B.run m k).clock by omega]
    | some t =>
      have hp := B.run_preserves_stamp hk hs
      have he := Option.some.inj (hp.symm.trans (B.execution_stamp hm v))
      have ht := (B.run_safe m k).stamps v t hs
      simp [show B.execution m v < (B.run m k).clock by omega, he]
  · have hrev : B.completionRound ≤ k := by omega
    have hs := B.run_preserves_stamp hrev (B.execution_stamp hm v)
    have ht := (B.run_safe m k).stamps v (B.execution m v) hs
    rw [if_pos ht.2.1]
    exact hs

theorem run_stamp_some_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (v : Fin vertices) (t : ℕ) :
    (B.run m k).stamp v = some t ↔ B.execution m v = t ∧ t < (B.run m k).clock := by
  rw [B.run_stamp_exact hm]
  split_ifs with h <;> simp_all <;> intro he <;> omega

theorem run_stamp_none_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (v : Fin vertices) :
    (B.run m k).stamp v = none ↔ (B.run m k).clock ≤ B.execution m v := by
  rw [B.run_stamp_exact hm]
  split_ifs <;> simp_all

theorem run_stamp_done_iff {m : ℕ} (hm : 0 < m) (k : ℕ) (v : Fin vertices) :
    (B.run m k).stamp v ≠ none ↔ B.execution m v < (B.run m k).clock := by
  rw [B.run_stamp_exact hm]
  split_ifs <;> simp_all

/-- The executable action at local slot j is exactly the set of vertices
assigned to that global execution timestep. -/
theorem action_iff_execution {m k j : ℕ} (hm : 0 < m)
    (hj : j < (B.observe (B.run m k)).duration m) (v : Fin vertices) :
    v ∈ (B.observe (B.run m k)).action m j ↔
      B.execution m v = (B.run m k).clock + j := by
  constructor
  · intro hv
    have ha := (B.observe (B.run m k)).assignSlot_complete hj hv
    have hs : (B.run m (k + 1)).stamp v = some ((B.run m k).clock + j) := by
      simp [run, advance, ha]
    exact ((B.run_stamp_some_iff hm (k + 1) v _).mp hs).1
  · intro hv
    have hn : (B.run m k).stamp v = none := (B.run_stamp_none_iff hm k v).mpr (by omega)
    have ht : B.execution m v < (B.run m (k + 1)).clock := by
      change B.execution m v < (B.run m k).clock + (B.observe (B.run m k)).duration m
      omega
    have hs := (B.run_stamp_some_iff hm (k + 1) v (B.execution m v)).mpr ⟨rfl, ht⟩
    cases ha : (B.observe (B.run m k)).assignSlot m v with
    | none =>
      have hnone : (B.run m (k + 1)).stamp v = none := by simp [run, advance, ha, hn]
      rw [hnone] at hs
      cases hs
    | some a =>
      have he : (B.run m k).clock + a = B.execution m v :=
        Option.some.inj (by simpa [run, advance, ha] using hs)
      have haj : a = j := by omega
      simpa [haj] using ((B.observe (B.run m k)).assignSlot_sound ha).2

theorem execution_slot_eq {m k t : ℕ} (hm : 0 < m)
    (h₁ : (B.run m k).clock ≤ t) (h₂ : t < (B.run m (k + 1)).clock) :
    univ.filter (fun v => B.execution m v = t) =
      (B.observe (B.run m k)).action m (t - (B.run m k).clock) := by
  have hj : t - (B.run m k).clock < (B.observe (B.run m k)).duration m := by
    change t < (B.run m k).clock + (B.observe (B.run m k)).duration m at h₂
    omega
  ext v
  simp only [mem_filter, mem_univ, true_and]
  rw [B.action_iff_execution hm hj]
  omega

theorem observed_ready_iff {m k : ℕ} (hm : 0 < m) (b : Fin batches) (v : Fin vertices) :
    v ∈ (B.observe (B.run m k)).ready b ↔
      B.vertexBatch v = b ∧ B.eligible b ≤ (B.run m k).clock ∧
        I.Ready (B.execution m) (B.run m k).clock v := by
  constructor
  · intro hv
    have h := (mem_filter.mp hv).2
    refine ⟨h.1, h.2.1, ?_⟩
    have hr := B.released_by_eligible h.1
    refine ⟨by omega, (B.run_stamp_none_iff hm k v).mp h.2.2.1, ?_⟩
    intro u he
    exact (B.run_stamp_done_iff hm k u).mp (h.2.2.2 u he)
  · rintro ⟨hb, he, hr⟩
    exact mem_filter.mpr ⟨mem_univ _, hb, he, (B.run_stamp_none_iff hm k v).mpr hr.2.1,
      by intro u hu; exact (B.run_stamp_done_iff hm k u).mpr (hr.2.2 u hu)⟩

theorem observed_frontier_eq {m k : ℕ} (hm : 0 < m) {b : Fin batches}
    (hb : B.eligible b ≤ (B.run m k).clock) :
    (B.observe (B.run m k)).ready b = B.frontier (B.execution m) (B.run m k).clock b := by
  ext v
  rw [B.observed_ready_iff hm]
  simp only [frontier, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h₁, _, h₃⟩; exact ⟨h₁, h₃⟩
  · rintro ⟨h₁, h₃⟩; exact ⟨h₁, hb, h₃⟩

theorem observed_small_eq {m k : ℕ} (hm : 0 < m) :
    (B.observe (B.run m k)).small m = B.small m (B.execution m) (B.run m k).clock := by
  ext b
  constructor
  · intro hb
    have h := (mem_filter.mp hb).2
    obtain ⟨v, hv⟩ := card_pos.mp h.1
    have hv' := (B.observed_ready_iff hm b v).mp hv
    have ha : B.Active (B.execution m) (B.run m k).clock b :=
      ⟨hv'.2.1, v, hv'.1, hv'.2.2.2.1⟩
    have heq := B.observed_frontier_eq hm hv'.2.1
    exact mem_filter.mpr ⟨mem_univ _, ha, by rw [← heq]; exact h.2⟩
  · intro hb
    have h := (mem_filter.mp hb).2
    obtain ⟨v, hv, hu⟩ := h.1.2
    have hrel := (B.released_by_eligible hv).le.trans h.1.1
    obtain ⟨w, hw, hr⟩ := I.exists_ready hrel ⟨v, rfl, hu⟩
    have hb' : B.vertexBatch w = b := by simpa [vertexBatch, hw] using hv
    have hobs := (B.observed_ready_iff hm b w).mpr ⟨hb', h.1.1, hr⟩
    have heq := B.observed_frontier_eq hm h.1.1
    exact mem_filter.mpr ⟨mem_univ _, card_pos.mpr ⟨w, hobs⟩, by rw [heq]; exact h.2⟩

theorem observed_large_eq {m k : ℕ} (hm : 0 < m) :
    (B.observe (B.run m k)).large m = B.large m (B.execution m) (B.run m k).clock := by
  ext b
  constructor
  · intro hb
    have h := (mem_filter.mp hb).2
    have hp : 0 < ((B.observe (B.run m k)).ready b).card := by omega
    obtain ⟨v, hv⟩ := card_pos.mp hp
    have hv' := (B.observed_ready_iff hm b v).mp hv
    have heq := B.observed_frontier_eq hm hv'.2.1
    exact mem_filter.mpr ⟨mem_univ _, ⟨hv'.2.1, v, hv'.1, hv'.2.2.2.1⟩, by rw [← heq]; exact h⟩
  · intro hb
    have h := (mem_filter.mp hb).2
    have heq := B.observed_frontier_eq hm h.1.1
    exact mem_filter.mpr ⟨mem_univ _, by rw [heq]; exact h.2⟩

theorem observed_smallFront_eq {m k : ℕ} (hm : 0 < m) :
    (B.observe (B.run m k)).smallFront m =
      univ.filter (fun v => B.vertexBatch v ∈ B.small m (B.execution m) (B.run m k).clock ∧
        I.Ready (B.execution m) (B.run m k).clock v) := by
  ext v
  constructor
  · intro hv
    have h := (B.observe (B.run m k)).smallFront_ready hv
    have hr := (B.observed_ready_iff hm (B.vertexBatch v) v).mp h.2
    exact mem_filter.mpr ⟨mem_univ _, by rw [← B.observed_small_eq hm]; exact h.1, hr.2.2⟩
  · intro hv
    have h := (mem_filter.mp hv).2
    have hs : B.vertexBatch v ∈ (B.observe (B.run m k)).small m := by rw [B.observed_small_eq hm]; exact h.1
    have he := (mem_filter.mp h.1).2.1.1
    exact mem_biUnion.mpr ⟨B.vertexBatch v, hs,
      (B.observed_ready_iff hm _ v).mpr ⟨rfl, he, h.2⟩⟩

end Scheduling.Batching
