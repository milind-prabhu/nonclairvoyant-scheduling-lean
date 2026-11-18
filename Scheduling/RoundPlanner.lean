import Scheduling.Packing

/-! An executable SFF round planner. Its input consists only of the ready
frontiers of admitted batches, together with public batch labels. -/
namespace Scheduling
open Finset

structure ReadySnapshot (V : Type*) (batches : ℕ) where
  batchOf : V → Fin batches
  ready : Fin batches → Finset V
  ready_batch : ∀ b v, v ∈ ready b → batchOf v = b

namespace ReadySnapshot
variable {V : Type*} [LinearOrder V] {batches : ℕ} (Q : ReadySnapshot V batches)

def small (m : ℕ) : Finset (Fin batches) :=
  univ.filter (fun b => 0 < (Q.ready b).card ∧ (Q.ready b).card ≤ m)
def large (m : ℕ) : Finset (Fin batches) :=
  univ.filter (fun b => m < (Q.ready b).card)
def smallFront (m : ℕ) : Finset V := (Q.small m).biUnion Q.ready
def filler (m : ℕ) : Option (Fin batches) :=
  if h : (Q.large m).Nonempty then some ((Q.large m).min' h) else none
def fillerFront (m : ℕ) : Finset V :=
  match Q.filler m with | none => ∅ | some b => Q.ready b
def duration (m : ℕ) : ℕ := Packing.duration (Q.smallFront m).card m
def action (m k : ℕ) : Finset V :=
  Packing.slot (Q.smallFront m) m k ∪
    if k + 1 = Q.duration m then
      Packing.slice (Q.fillerFront m) 0 (m - (Packing.slot (Q.smallFront m) m k).card)
    else ∅

omit [LinearOrder V] in
theorem filler_mem {m : ℕ} {b : Fin batches} (hb : Q.filler m = some b) : b ∈ Q.large m := by
  unfold filler at hb
  split_ifs at hb with h
  · have he := Option.some.inj hb
    rw [← he]
    exact min'_mem _ _

omit [LinearOrder V] in
theorem filler_oldest {m : ℕ} {b c : Fin batches}
    (hb : Q.filler m = some b) (hc : c ∈ Q.large m) : b ≤ c := by
  unfold filler at hb
  split_ifs at hb with h
  · have he := Option.some.inj hb
    rw [← he]
    exact min'_le _ _ hc

omit [LinearOrder V] in
theorem filler_exists {m : ℕ} (h : (Q.large m).Nonempty) : ∃ b, Q.filler m = some b := by
  exact ⟨(Q.large m).min' h, by simp [filler, h]⟩

theorem smallFront_ready {m : ℕ} {v : V} (hv : v ∈ Q.smallFront m) :
    Q.batchOf v ∈ Q.small m ∧ v ∈ Q.ready (Q.batchOf v) := by
  obtain ⟨b, hb, hv⟩ := mem_biUnion.mp hv
  have he := Q.ready_batch b v hv
  rw [he]
  exact ⟨hb, hv⟩

omit [LinearOrder V] in
theorem fillerFront_ready {m : ℕ} {v : V} (hv : v ∈ Q.fillerFront m) :
    Q.filler m = some (Q.batchOf v) ∧ v ∈ Q.ready (Q.batchOf v) := by
  unfold fillerFront at hv
  cases he : Q.filler m with
  | none => simp [he] at hv
  | some b =>
    rw [he] at hv
    have ho := Q.ready_batch b v hv
    exact ⟨by simp [ho], by simpa [ho] using hv⟩

theorem frontiers_disjoint (m : ℕ) : Disjoint (Q.smallFront m) (Q.fillerFront m) := by
  apply disjoint_left.mpr
  intro v hv hw
  have hs := Q.smallFront_ready hv
  have hf := Q.fillerFront_ready hw
  have hl := Q.filler_mem hf.1
  have h₁ := (mem_filter.mp hs.1).2.2
  have h₂ := (mem_filter.mp hl).2
  omega

theorem action_scope {m k : ℕ} {v : V} (hv : v ∈ Q.action m k) :
    (Q.batchOf v ∈ Q.small m ∧ v ∈ Q.ready (Q.batchOf v)) ∨
      (Q.filler m = some (Q.batchOf v) ∧ v ∈ Q.ready (Q.batchOf v)) := by
  rcases mem_union.mp hv with h | h
  · exact Or.inl (Q.smallFront_ready (Packing.slice_subset _ _ _ h))
  · split_ifs at h with hk
    · exact Or.inr (Q.fillerFront_ready (Packing.slice_subset _ _ _ h))
    · exact False.elim (notMem_empty _ h)

theorem action_card_le (m k : ℕ) : (Q.action m k).card ≤ m := by
  have hp := Packing.slot_card_le (Q.smallFront m) m k
  unfold action
  split_ifs with hk
  · have hf : (Packing.slice (Q.fillerFront m) 0
        (m - (Packing.slot (Q.smallFront m) m k).card)).card ≤
        m - (Packing.slot (Q.smallFront m) m k).card := by
      rw [Packing.slice_card]
      omega
    have hu := card_union_le (Packing.slot (Q.smallFront m) m k)
      (Packing.slice (Q.fillerFront m) 0 (m - (Packing.slot (Q.smallFront m) m k).card))
    omega
  · simpa using hp

theorem clears_small {m : ℕ} (hm : 0 < m) {b : Fin batches} (hb : b ∈ Q.small m)
    {v : V} (hv : v ∈ Q.ready b) : ∃ k < Q.duration m, v ∈ Q.action m k := by
  have hvP : v ∈ Q.smallFront m := mem_biUnion.mpr ⟨b, hb, hv⟩
  obtain ⟨k, hk, hvk⟩ := Packing.covers _ hm hvP
  exact ⟨k, hk, mem_union_left _ hvk⟩

theorem nonfinal_full {m k : ℕ} (hm : 0 < m) (hk : k + 1 < Q.duration m) :
    (Q.action m k).card = m := by
  have he : k + 1 ≠ Q.duration m := by omega
  simp only [action, if_neg he, union_empty]
  exact Packing.before_last_full _ hm hk

theorem full_with_large {m k : ℕ} (hm : 0 < m) (hk : k < Q.duration m)
    (hl : (Q.large m).Nonempty) : (Q.action m k).card = m := by
  by_cases hlast : k + 1 = Q.duration m
  · obtain ⟨b, hb⟩ := Q.filler_exists hl
    have hbig := (mem_filter.mp (Q.filler_mem hb)).2
    have he : Q.fillerFront m = Q.ready b := by simp [fillerFront, hb]
    have hc := Packing.slot_card_le (Q.smallFront m) m k
    have hd : Disjoint (Packing.slot (Q.smallFront m) m k)
        (Packing.slice (Q.fillerFront m) 0 (m - (Packing.slot (Q.smallFront m) m k).card)) := by
      exact (Q.frontiers_disjoint m).mono (Packing.slice_subset _ _ _) (Packing.slice_subset _ _ _)
    simp only [action, if_pos hlast, card_union_of_disjoint hd, Packing.slice_card, Nat.sub_zero]
    rw [he, min_eq_left (by omega)]
    omega
  · exact Q.nonfinal_full hm (by omega)

theorem actions_disjoint {m i j : ℕ} (hij : i ≠ j) : Disjoint (Q.action m i) (Q.action m j) := by
  apply disjoint_left.mpr
  intro v hv hw
  rcases mem_union.mp hv with hv | hv <;> rcases mem_union.mp hw with hw | hw
  · exact disjoint_left.mp (Packing.slot_disjoint (Q.smallFront m) hij) hv hw
  · split_ifs at hw with hj
    · exact disjoint_left.mp (Q.frontiers_disjoint m)
        (Packing.slice_subset _ _ _ hv) (Packing.slice_subset _ _ _ hw)
    · exact notMem_empty _ hw
  · split_ifs at hv with hi
    · exact disjoint_left.mp (Q.frontiers_disjoint m)
        (Packing.slice_subset _ _ _ hw) (Packing.slice_subset _ _ _ hv)
    · exact notMem_empty _ hv
  · split_ifs at hv hw with hi hj
    all_goals simp_all
    all_goals omega

/-- A bounded, executable search for a vertex's unique slot in the round. -/
def assignSlot (m : ℕ) (v : V) : Option ℕ :=
  let A := (range (Q.duration m)).filter (fun k => v ∈ Q.action m k)
  if h : A.Nonempty then some (A.min' h) else none

theorem assignSlot_sound {m k : ℕ} {v : V} (h : Q.assignSlot m v = some k) :
    k < Q.duration m ∧ v ∈ Q.action m k := by
  dsimp only [assignSlot] at h
  split_ifs at h with hn
  have he := Option.some.inj h
  have hm := mem_filter.mp (min'_mem _ hn)
  rw [he] at hm
  exact ⟨mem_range.mp hm.1, hm.2⟩

theorem assignSlot_complete {m k : ℕ} {v : V}
    (hk : k < Q.duration m) (hv : v ∈ Q.action m k) : Q.assignSlot m v = some k := by
  let A := (range (Q.duration m)).filter (fun j => v ∈ Q.action m j)
  have hmem : k ∈ A := mem_filter.mpr ⟨mem_range.mpr hk, hv⟩
  have hn : A.Nonempty := ⟨k, hmem⟩
  have hm := (mem_filter.mp (min'_mem A hn)).2
  have he : A.min' hn = k := by
    by_contra he
    exact disjoint_left.mp (Q.actions_disjoint he) hm hv
  change (if h : A.Nonempty then some (A.min' h) else none) = some k
  rw [dif_pos hn, he]

theorem progress {m : ℕ} (hm : 0 < m) {b : Fin batches} {v : V} (hv : v ∈ Q.ready b) :
    ∃ w k, k < Q.duration m ∧ Q.assignSlot m w = some k := by
  have hp : 0 < (Q.ready b).card := card_pos.mpr ⟨v, hv⟩
  by_cases hs : (Q.ready b).card ≤ m
  · have hb : b ∈ Q.small m := mem_filter.mpr ⟨mem_univ _, hp, hs⟩
    obtain ⟨k, hk, hvk⟩ := Q.clears_small hm hb hv
    exact ⟨v, k, hk, Q.assignSlot_complete hk hvk⟩
  · have hl : (Q.large m).Nonempty := ⟨b, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
    have hk : 0 < Q.duration m := Packing.duration_pos _ _
    have hc := Q.full_with_large hm hk hl
    have hn : (Q.action m 0).Nonempty := card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hn
    exact ⟨w, 0, hk, Q.assignSlot_complete hk hw⟩

/-- Local observation noninterference: every computed round decision is
determined by the exposed ready frontiers. Even the ownership function and
the proofs attached to the observation cannot affect the output. -/
theorem ready_only (Q' : ReadySnapshot V batches) (h : Q.ready = Q'.ready) (m : ℕ) :
    Q.duration m = Q'.duration m ∧ Q.filler m = Q'.filler m ∧
      Q.action m = Q'.action m ∧ Q.assignSlot m = Q'.assignSlot m := by
  cases Q with
  | mk owner ready sound =>
    cases Q' with
    | mk owner' ready' sound' =>
      change ready = ready' at h
      subst ready'
      exact ⟨rfl, rfl, rfl, rfl⟩

end ReadySnapshot
end Scheduling
