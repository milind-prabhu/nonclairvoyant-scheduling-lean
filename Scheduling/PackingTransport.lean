import Scheduling.Packing

namespace Scheduling.Packing
open Finset
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- Ordered packing is invariant under order-preserving relabeling. In
particular, converting finite vertex labels to natural numbers does not
change a round's execution order. -/
theorem slice_image (s : Finset V) (f : V → W) (hf : StrictMono f) (a b : ℕ) :
    (slice s a b).image f = slice (s.image f) a b := by
  classical
  have hc : (s.image f).card = s.card := card_image_of_injective _ hf.injective
  have henum : (fun i : Fin s.card => f (s.orderEmbOfFin rfl i)) =
      (s.image f).orderEmbOfFin hc := by
    apply orderEmbOfFin_unique hc
    · intro i
      exact mem_image.mpr ⟨_, orderEmbOfFin_mem _ _ _, rfl⟩
    · exact hf.comp (s.orderEmbOfFin rfl).strictMono
  have hcast (i : Fin s.card) :
      (s.image f).orderEmbOfFin rfl (i.cast hc.symm) = f (s.orderEmbOfFin rfl i) := by
    rw [congrFun henum i]
    exact orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  ext y
  constructor
  · intro hy
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨i, hi₁, hi₂, hi⟩ := (mem_slice_iff _ _ _ _).mp hv
    refine (mem_slice_iff _ _ _ _).mpr ⟨i.cast hc.symm, hi₁, hi₂, ?_⟩
    rw [hcast, hi]
  · intro hy
    obtain ⟨i, hi₁, hi₂, hi⟩ := (mem_slice_iff _ _ _ _).mp hy
    let j : Fin s.card := i.cast hc
    have he : f (s.orderEmbOfFin rfl j) = y := by
      rw [← hcast]
      exact hi
    exact mem_image.mpr ⟨_, (mem_slice_iff _ _ _ _).mpr ⟨j, hi₁, hi₂, rfl⟩, he⟩

theorem slot_image (s : Finset V) (f : V → W) (hf : StrictMono f) (m k : ℕ) :
    (slot s m k).image f = slot (s.image f) m k :=
  slice_image s f hf _ _

end Scheduling.Packing
