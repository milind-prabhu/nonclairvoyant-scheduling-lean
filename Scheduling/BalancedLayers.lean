import Scheduling.OfflineBatched
import Scheduling.LayeredForest
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

theorem card_before_orderEmb {L : ℕ} (W : Finset (Fin L)) (q : Fin W.card) :
    (W.filter (fun i => i < W.orderEmbOfFin rfl q)).card = q.val := by
  let e := W.orderEmbOfFin rfl
  have he : W.filter (fun i => i < e q) = (Iio q).image e := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiW, hiq⟩ := mem_filter.mp hi
      let p := (W.orderIsoOfFin rfl).symm ⟨i, hiW⟩
      have hp : e p = i := congrArg Subtype.val ((W.orderIsoOfFin rfl).apply_symm_apply ⟨i, hiW⟩)
      refine mem_image.mpr ⟨p, mem_Iio.mpr ?_, hp⟩
      exact e.lt_iff_lt.mp (by rwa [hp])
    · rintro hi
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
      exact mem_filter.mpr ⟨W.orderEmbOfFin_mem rfl p, e.strictMono (mem_Iio.mp hp)⟩
  change (W.filter (fun i => i < e q)).card = q.val
  rw [he, card_image_of_injective _ e.injective, Fin.card_Iio]

/-- The layer order of each job has equally many wide and narrow layers,
and no prefix has more narrow layers than wide layers. -/
structure BalancedLayers (jobs L : ℕ) where
  wide : Fin jobs → Finset (Fin L)
  half : ∀ j, 2 * (wide j).card = L
  balanced_prefix : ∀ j (i : Fin L), i.val ≤ 2 * ((wide j).filter (fun w => w < i)).card

namespace BalancedLayers
variable {jobs L : ℕ} (F : BalancedLayers jobs L)

theorem wide_early (j : Fin jobs) (q : Fin (F.wide j).card) :
    ((F.wide j).orderEmbOfFin rfl q).val ≤ 2 * q.val := by
  have h := F.balanced_prefix j ((F.wide j).orderEmbOfFin rfl q)
  rwa [card_before_orderEmb] at h

/-- Each wide layer contributes `2(m-1)` leaves, listed in layer order. -/
def leafGroup {m : ℕ} (hm : 2 ≤ m) (j : Fin jobs) (k : Fin (m * L))
    (hk : L ≤ k.val) : Fin (F.wide j).card :=
  ⟨(k.val - L) / (2 * (m - 1)), by
    have hp : 0 < 2 * (m - 1) := by omega
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    have hh := F.half j
    have hm1 : m - 1 + 1 = m := by omega
    have he : k.val - L + L = k.val := Nat.sub_add_cancel hk
    have hlt := k.isLt
    nlinarith⟩

def forest {m : ℕ} (hm : 2 ≤ m) (hL : 0 < L) : LayeredForest jobs (m * L) where
  depth _ := L
  depth_pos _ := hL
  depth_le _ := by nlinarith
  leafLevel j k := if hk : k.val < L then ⟨0, hL⟩ else
    (F.wide j).orderEmbOfFin rfl (F.leafGroup hm j k (by omega))

theorem leaf_level_bound {m : ℕ} (hm : 2 ≤ m) (hL : 0 < L)
    (j : Fin jobs) (k : Fin (m * L)) (hk : L ≤ k.val) :
    (F.forest hm hL).level j k * (m - 1) ≤ k.val - L := by
  have hn : ¬ k.val < L := by omega
  have he := F.wide_early j (F.leafGroup hm j k hk)
  have hmul := Nat.mul_le_mul_right (m - 1) he
  have hdiv := Nat.div_mul_le_self (k.val - L) (2 * (m - 1))
  dsimp [LayeredForest.level, forest]
  rw [if_neg hn, dif_neg hn]
  change ((F.wide j).orderEmbOfFin rfl (F.leafGroup hm j k hk)).val * (m - 1) ≤ k.val - L
  dsimp [leafGroup] at hmul ⊢
  nlinarith

theorem offline_schedule {m : ℕ} (hm : 2 ≤ m) (hL : 0 < L) :
    ∃ O, ((F.forest hm hL).toInstance L).Valid m O ∧
      ((F.forest hm hL).toInstance L).FlowBound O L := by
  let G := F.forest hm hL
  let I := G.toInstance L
  let pos := fun v : Fin (jobs * (m * L)) => (LayeredForest.position v).val
  have hpos : ∀ v, pos v < m * L := fun v => (LayeredForest.position v).isLt
  refine ⟨fun v => batchedTime m L (I.owner v).val (pos v), ?_, ?_⟩
  · apply I.batched_valid hm pos hpos LayeredForest.coordinates_injective (by intros; rfl)
    intro u v huv
    have hk := G.edge_from_key L huv
    have he := huv.2
    change (LayeredForest.position u).val + 1 =
      G.level (LayeredForest.job v) (LayeredForest.position v) at he
    refine ⟨hk.1, ?_⟩
    by_cases hv : pos v < L
    · simpa only [if_pos hv] using hk.2
    · rw [if_neg hv]
      change ((LayeredForest.position u).val + 1) * (m - 1) ≤
        (LayeredForest.position v).val - L
      rw [he]
      exact F.leaf_level_bound hm hL _ _ (Nat.le_of_not_gt hv)
  · exact I.batched_flowBound hm pos hpos (by intros; rfl)

/-- The optimum is exactly the release spacing, as required by batched
arrivals. The lower bound follows from the exact `mL` work in each job. -/
theorem optimum_eq {m : ℕ} (hm : 2 ≤ m) (hL : 0 < L) (hj : 0 < jobs) :
    ((F.forest hm hL).toInstance L).optimum m (by omega) = L := by
  let G := F.forest hm hL
  let I := G.toInstance L
  have hm0 : 0 < m := by omega
  obtain ⟨O, hO, hflow⟩ := F.offline_schedule hm hL
  apply Nat.le_antisymm (I.optimum_le hm0 hO hflow)
  obtain ⟨P, hP, hp⟩ := I.optimum_attained hm0
  have hwork := I.job_work_bound hP hp ⟨0, hj⟩
  rw [G.jobVertices_card] at hwork
  exact Nat.le_of_mul_le_mul_left hwork hm0

end BalancedLayers
end Scheduling
