import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

/-- Put the distinguished keys first, retaining their original order;
then list the remaining vertices. -/
noncomputable def keyFirstPosition {work : ℕ} (keys : Finset (Fin work)) (v : Fin work) : ℕ :=
  if hv : v ∈ keys then ((keys.orderIsoOfFin rfl).symm ⟨v, hv⟩).val else
    keys.card + (((univ \ keys).orderIsoOfFin rfl).symm ⟨v, by simp [hv]⟩).val

theorem keyFirstPosition_key_lt {work : ℕ} (keys : Finset (Fin work))
    (v : Fin work) (hv : v ∈ keys) : keyFirstPosition keys v < keys.card := by
  rw [keyFirstPosition, dif_pos hv]
  exact ((keys.orderIsoOfFin rfl).symm ⟨v, hv⟩).isLt

theorem keyFirstPosition_nonkey_ge {work : ℕ} (keys : Finset (Fin work))
    (v : Fin work) (hv : v ∉ keys) : keys.card ≤ keyFirstPosition keys v := by
  rw [keyFirstPosition, dif_neg hv]
  omega

theorem keyFirstPosition_lt {work : ℕ} (keys : Finset (Fin work)) (v : Fin work) :
    keyFirstPosition keys v < work := by
  have hc : keys.card + (univ \ keys).card = work := by
    have h := card_sdiff_add_card_eq_card (subset_univ keys)
    simp only [card_univ, Fintype.card_fin] at h
    omega
  by_cases hv : v ∈ keys
  · have hk := keyFirstPosition_key_lt keys v hv
    omega
  · rw [keyFirstPosition, dif_neg hv]
    have ht := (((univ \ keys).orderIsoOfFin rfl).symm ⟨v, by simp [hv]⟩).isLt
    omega

theorem keyFirstPosition_injective {work : ℕ} (keys : Finset (Fin work)) :
    Function.Injective (keyFirstPosition keys) := by
  intro u v he
  by_cases hu : u ∈ keys <;> by_cases hv : v ∈ keys
  · rw [keyFirstPosition, dif_pos hu, keyFirstPosition, dif_pos hv] at he
    have hh := (keys.orderIsoOfFin rfl).symm.injective (Fin.ext he)
    exact congrArg Subtype.val hh
  · have h₁ := keyFirstPosition_key_lt keys u hu
    have h₂ := keyFirstPosition_nonkey_ge keys v hv
    omega
  · have h₁ := keyFirstPosition_nonkey_ge keys u hu
    have h₂ := keyFirstPosition_key_lt keys v hv
    omega
  · rw [keyFirstPosition, dif_neg hu, keyFirstPosition, dif_neg hv] at he
    have hh := ((univ \ keys).orderIsoOfFin rfl).symm.injective (Fin.ext (Nat.add_left_cancel he))
    exact congrArg Subtype.val hh

theorem keyFirstPosition_edge {work : ℕ} (keys : Finset (Fin work))
    {u v : Fin work} (hu : u ∈ keys) (huv : u < v) :
    keyFirstPosition keys u < keyFirstPosition keys v := by
  by_cases hv : v ∈ keys
  · rw [keyFirstPosition, dif_pos hu, keyFirstPosition, dif_pos hv]
    exact (keys.orderIsoOfFin rfl).symm.strictMono (show (⟨u, hu⟩ : keys) < ⟨v, hv⟩ from huv)
  · exact (keyFirstPosition_key_lt keys u hu).trans_le (keyFirstPosition_nonkey_ge keys v hv)

end Scheduling
