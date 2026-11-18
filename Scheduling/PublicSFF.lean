import Scheduling.Information
import Scheduling.PackingTransport
import Scheduling.SFFConstruction

namespace Scheduling
open Finset

/-- A round observation carries only nonempty exposed frontiers. Neither
the total number of batches nor the hidden vertex domain is part of it. -/
structure PublicSnapshot where
  support : Finset ℕ
  ready : ℕ → Finset ℕ
  supported : ∀ b, b ∈ support ↔ (ready b).Nonempty

namespace PublicSnapshot

theorem ext_ready {Q R : PublicSnapshot} (h : Q.ready = R.ready) : Q = R := by
  cases Q with
  | mk qs qr qp =>
    cases R with
    | mk rs rr rp =>
      change qr = rr at h
      subst rr
      have hs : qs = rs := by
        ext b
        exact (qp b).trans (rp b).symm
      subst rs
      rfl

def small (Q : PublicSnapshot) (m : ℕ) : Finset ℕ :=
  Q.support.filter (fun b => (Q.ready b).card ≤ m)
def large (Q : PublicSnapshot) (m : ℕ) : Finset ℕ :=
  Q.support.filter (fun b => m < (Q.ready b).card)
def smallFront (Q : PublicSnapshot) (m : ℕ) : Finset ℕ := (Q.small m).biUnion Q.ready
def filler (Q : PublicSnapshot) (m : ℕ) : Option ℕ :=
  if h : (Q.large m).Nonempty then some ((Q.large m).min' h) else none
def fillerFront (Q : PublicSnapshot) (m : ℕ) : Finset ℕ :=
  match Q.filler m with | none => ∅ | some b => Q.ready b
def duration (Q : PublicSnapshot) (m : ℕ) : ℕ := Packing.duration (Q.smallFront m).card m
def action (Q : PublicSnapshot) (m k : ℕ) : Finset ℕ :=
  Packing.slot (Q.smallFront m) m k ∪
    if k + 1 = Q.duration m then
      Packing.slice (Q.fillerFront m) 0 (m - (Packing.slot (Q.smallFront m) m k).card)
    else ∅

end PublicSnapshot

namespace ReadySnapshot
variable {vertices batches : ℕ} (Q : ReadySnapshot (Fin vertices) batches)

def expose : PublicSnapshot where
  support := (univ.filter (fun b => (Q.ready b).Nonempty)).image Fin.val
  ready := fun n => if hn : n < batches then (Q.ready ⟨n, hn⟩).image Fin.val else ∅
  supported := by
    intro n
    by_cases hn : n < batches
    · simp only [dif_pos hn, image_nonempty, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨b, hb, he⟩
        have hb' : b = ⟨n, hn⟩ := Fin.ext he
        simpa [hb'] using hb
      · intro h
        exact ⟨⟨n, hn⟩, h, rfl⟩
    · simp only [dif_neg hn, Finset.not_nonempty_empty, iff_false, mem_image, mem_filter,
        mem_univ, true_and]
      rintro ⟨b, _, he⟩
      exact hn (he ▸ b.isLt)

@[simp] theorem expose_ready (b : Fin batches) :
    Q.expose.ready b.val = (Q.ready b).image Fin.val := by
  simp [expose]

theorem mem_expose_ready (b n : ℕ) : n ∈ Q.expose.ready b ↔
    ∃ c : Fin batches, c.val = b ∧ ∃ v, v ∈ Q.ready c ∧ v.val = n := by
  by_cases hb : b < batches
  · simp only [expose, dif_pos hb, mem_image]
    constructor
    · rintro ⟨v, hv, he⟩
      exact ⟨⟨b, hb⟩, rfl, v, hv, he⟩
    · rintro ⟨c, hc, v, hv, he⟩
      have hcb : c = ⟨b, hb⟩ := Fin.ext hc
      exact ⟨v, by simpa [hcb] using hv, he⟩
  · simp only [expose, dif_neg hb, notMem_empty, false_iff]
    rintro ⟨c, hc, _⟩
    exact hb (hc ▸ c.isLt)

theorem expose_small (m : ℕ) : Q.expose.small m = (Q.small m).image Fin.val := by
  ext n
  constructor
  · intro hn
    have hn' := mem_filter.mp hn
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hn'.1
    have hp : 0 < (Q.ready b).card := card_pos.mpr (mem_filter.mp hb).2
    have hc : (Q.ready b).card ≤ m := by
      simpa only [Q.expose_ready, card_image_of_injective _ Fin.val_injective] using hn'.2
    exact mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hp, hc⟩, rfl⟩
  · intro hn
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hn
    have hb' := (mem_filter.mp hb).2
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, card_pos.mp hb'.1⟩, rfl⟩
    · simpa only [Q.expose_ready, card_image_of_injective _ Fin.val_injective] using hb'.2

theorem expose_large (m : ℕ) : Q.expose.large m = (Q.large m).image Fin.val := by
  ext n
  constructor
  · intro hn
    have hn' := mem_filter.mp hn
    obtain ⟨b, _, rfl⟩ := mem_image.mp hn'.1
    have hc : m < (Q.ready b).card := by
      simpa only [Q.expose_ready, card_image_of_injective _ Fin.val_injective] using hn'.2
    exact mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hc⟩, rfl⟩
  · intro hn
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hn
    have hb' := (mem_filter.mp hb).2
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, card_pos.mp (by omega)⟩, rfl⟩
    · simpa only [Q.expose_ready, card_image_of_injective _ Fin.val_injective] using hb'

theorem expose_smallFront (m : ℕ) :
    Q.expose.smallFront m = (Q.smallFront m).image Fin.val := by
  ext n
  constructor
  · intro hn
    obtain ⟨k, hk, hv⟩ := mem_biUnion.mp hn
    rw [Q.expose_small] at hk
    obtain ⟨b, hb, he⟩ := mem_image.mp hk
    subst k
    rw [Q.expose_ready] at hv
    obtain ⟨v, hw, he⟩ := mem_image.mp hv
    subst n
    exact mem_image.mpr ⟨v, mem_biUnion.mpr ⟨b, hb, hw⟩, rfl⟩
  · intro hn
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
    obtain ⟨b, hb, hv⟩ := mem_biUnion.mp hv
    apply mem_biUnion.mpr
    refine ⟨b.val, ?_, ?_⟩
    · rw [Q.expose_small]
      exact mem_image.mpr ⟨b, hb, rfl⟩
    · rw [Q.expose_ready]
      exact mem_image.mpr ⟨v, hv, rfl⟩

theorem expose_filler (m : ℕ) : Q.expose.filler m = (Q.filler m).map Fin.val := by
  unfold PublicSnapshot.filler ReadySnapshot.filler
  rw [Q.expose_large]
  by_cases h : (Q.large m).Nonempty
  · simp only [h, image_nonempty, ↓reduceDIte, Option.map_some]
    congr 1
    exact min'_image (f := Fin.val) (show Monotone (Fin.val : Fin batches → ℕ) from fun _ _ hab => hab) _ _
  · simp only [h, image_nonempty, ↓reduceDIte, Option.map_none]

theorem expose_fillerFront (m : ℕ) :
    Q.expose.fillerFront m = (Q.fillerFront m).image Fin.val := by
  unfold PublicSnapshot.fillerFront ReadySnapshot.fillerFront
  rw [Q.expose_filler]
  cases h : Q.filler m with
  | none => simp
  | some b => simp only [Option.map_some, Q.expose_ready]

theorem expose_duration (m : ℕ) : Q.expose.duration m = Q.duration m := by
  unfold PublicSnapshot.duration ReadySnapshot.duration
  rw [Q.expose_smallFront, card_image_of_injective _ Fin.val_injective]

/-- The public planner computes exactly the finite executor's round actions. -/
theorem expose_action (m k : ℕ) : Q.expose.action m k = (Q.action m k).image Fin.val := by
  have hmono : StrictMono (Fin.val : Fin vertices → ℕ) := fun _ _ h => h
  unfold PublicSnapshot.action ReadySnapshot.action
  rw [Q.expose_smallFront, Q.expose_fillerFront, Q.expose_duration]
  rw [← Packing.slot_image _ _ hmono, card_image_of_injective _ Fin.val_injective]
  rw [image_union]
  split_ifs <;> simp only [Packing.slice_image _ _ hmono, image_empty]

end ReadySnapshot
end Scheduling
