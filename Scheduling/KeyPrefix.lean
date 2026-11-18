import Scheduling.KeyOrder
import Scheduling.BalancedLayers

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

theorem keyFirstPosition_key_eq {work : ℕ} (keys : Finset (Fin work))
    (v : Fin work) (hv : v ∈ keys) :
    keyFirstPosition keys v = (keys.filter (fun k => k < v)).card := by
  let q := (keys.orderIsoOfFin rfl).symm ⟨v, hv⟩
  have he : keys.orderEmbOfFin rfl q = v :=
    congrArg Subtype.val ((keys.orderIsoOfFin rfl).apply_symm_apply ⟨v, hv⟩)
  have hc := card_before_orderEmb keys q
  rw [he] at hc
  rw [keyFirstPosition, dif_pos hv]
  exact hc.symm

theorem keyFirstPosition_nonkey_eq {work : ℕ} (keys : Finset (Fin work))
    (v : Fin work) (hv : v ∉ keys) :
    keyFirstPosition keys v - keys.card = ((univ \ keys).filter (fun k => k < v)).card := by
  have hv' : v ∈ univ \ keys := by simp [hv]
  let q := ((univ \ keys).orderIsoOfFin rfl).symm ⟨v, hv'⟩
  have he : (univ \ keys).orderEmbOfFin rfl q = v :=
    congrArg Subtype.val (((univ \ keys).orderIsoOfFin rfl).apply_symm_apply ⟨v, hv'⟩)
  have hc := card_before_orderEmb (univ \ keys) q
  rw [he] at hc
  rw [keyFirstPosition, dif_neg hv, Nat.add_sub_cancel_left]
  exact hc.symm

theorem key_nonkey_prefix_card {work : ℕ} (keys : Finset (Fin work)) (p : Fin work) :
    (keys.filter (fun k => k < p)).card + ((univ \ keys).filter (fun k => k < p)).card = p.val := by
  have hh := card_filter_add_card_filter_not (s := Iio p) (fun k => k ∈ keys)
  have hk : (Iio p).filter (fun k => k ∈ keys) = keys.filter (fun k => k < p) := by
    ext k; simp only [mem_filter, mem_Iio]; tauto
  have hn : (Iio p).filter (fun k => k ∉ keys) = (univ \ keys).filter (fun k => k < p) := by
    ext k; simp only [mem_filter, mem_Iio, mem_sdiff, mem_univ, true_and]; tauto
  rw [hk, hn, Fin.card_Iio] at hh
  exact hh

/-- If a layer boundary has at least `m` vertices per earlier key, the
leaf order leaves room to execute every earlier key before these leaves. -/
theorem keyFirstPosition_leaf_after_cut {work m p n : ℕ} (hm : 0 < m)
    (keys : Finset (Fin work)) (u v : Fin work) (hu : u ∈ keys) (hv : v ∉ keys)
    (hup : u.val < p) (hpv : p ≤ v.val)
    (hwork : m * n ≤ p) (hkeys : (keys.filter (fun k => k.val < p)).card ≤ n) :
    (keyFirstPosition keys u + 1) * (m - 1) ≤ keyFirstPosition keys v - keys.card := by
  let cut : Fin work := ⟨p, lt_of_le_of_lt hpv v.isLt⟩
  have hkey : keyFirstPosition keys u + 1 ≤ n := by
    rw [keyFirstPosition_key_eq keys u hu]
    have hsub : insert u (keys.filter (fun k => k < u)) ⊆ keys.filter (fun k => k.val < p) := by
      intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · exact mem_filter.mpr ⟨hu, hup⟩
      · have hh := mem_filter.mp hk
        exact mem_filter.mpr ⟨hh.1, lt_trans hh.2 hup⟩
    have hc := (card_le_card hsub).trans hkeys
    have hn : u ∉ keys.filter (fun k => k < u) := by simp
    rw [card_insert_of_notMem hn] at hc
    exact hc
  have hsplit := key_nonkey_prefix_card keys cut
  have hsmall : (keys.filter (fun k => k < cut)).card ≤ n := hkeys
  have hbase : (m - 1) * n + n = m * n := by
    have h := Nat.sub_add_cancel (show 1 ≤ m from hm)
    nlinarith
  have hleaf : (m - 1) * n ≤ ((univ \ keys).filter (fun k => k < cut)).card := by
    change _ + _ = p at hsplit
    omega
  have hsub : (univ \ keys).filter (fun k => k < cut) ⊆
      (univ \ keys).filter (fun k => k < v) := by
    intro k hk
    have hh := mem_filter.mp hk
    exact mem_filter.mpr ⟨hh.1, lt_of_lt_of_le hh.2 hpv⟩
  rw [keyFirstPosition_nonkey_eq keys v hv]
  have hmul := Nat.mul_le_mul_right (m - 1) hkey
  exact hmul.trans (by simpa only [Nat.mul_comm] using hleaf.trans (card_le_card hsub))

end Scheduling
