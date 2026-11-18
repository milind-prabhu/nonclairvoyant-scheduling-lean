import Scheduling.InstanceSequence
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

namespace Scheduling.FiniteAmplification
open Finset
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

noncomputable def safeWords (bad : List α → Prop) (k : ℕ) : Finset (Fin k → α) :=
  univ.filter (fun w => ¬ bad (List.ofFn w))

theorem safe_next_card (bad : List α → Prop) (xs : List α)
    (hnext : ∃ x, bad (xs ++ [x])) :
    (univ.filter (fun x => ¬ bad (xs ++ [x]))).card ≤ Fintype.card α - 1 := by
  obtain ⟨x, hx⟩ := hnext
  have hs : univ.filter (fun x => ¬ bad (xs ++ [x])) ⊂ univ := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ univ.filter (fun x => ¬ bad (xs ++ [x])) := by rw [he]; exact mem_univ x
    exact (mem_filter.mp hm).2 hx
  have hh := card_lt_card hs
  rw [card_univ] at hh
  omega

theorem safe_card_step (bad : List α → Prop)
    (hpersist : ∀ xs x, bad xs → bad (xs ++ [x]))
    (hnext : ∀ xs, ∃ x, bad (xs ++ [x])) (k : ℕ) :
    (safeWords bad (k + 1)).card ≤ (safeWords bad k).card * (Fintype.card α - 1) := by
  have hprefix : ∀ w ∈ safeWords bad (k + 1), Fin.init w ∈ safeWords bad k := by
    intro w hw
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hb
    have hh := hpersist (List.ofFn (Fin.init w)) (w (Fin.last k)) hb
    have he : List.ofFn w = List.ofFn (Fin.init w) ++ [w (Fin.last k)] := List.ofFn_succ_last
    rw [← he] at hh
    exact (mem_filter.mp hw).2 hh
  rw [card_eq_sum_card_fiberwise (f := Fin.init) hprefix]
  have hf : ∀ w ∈ safeWords bad k,
      ((safeWords bad (k + 1)).filter (fun v => Fin.init v = w)).card ≤ Fintype.card α - 1 := by
    intro w _
    have hi := card_le_card_of_injOn (fun v : Fin (k + 1) → α => v (Fin.last k))
      (s := (safeWords bad (k + 1)).filter (fun v => Fin.init v = w))
      (t := univ.filter (fun x => ¬ bad (List.ofFn w ++ [x])))
      (by
        intro v hv
        obtain ⟨hv, he⟩ := mem_filter.mp hv
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        have hh := (mem_filter.mp hv).2
        have hseq : List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last k)] := List.ofFn_succ_last
        rwa [hseq, he] at hh)
      (by
        intro u hu v hv he
        have hup := (mem_filter.mp hu).2
        have hvp := (mem_filter.mp hv).2
        change u (Fin.last k) = v (Fin.last k) at he
        calc
          u = Fin.snoc (Fin.init u) (u (Fin.last k)) := (Fin.snoc_init_self u).symm
          _ = Fin.snoc (Fin.init v) (v (Fin.last k)) := by rw [hup, hvp, he]
          _ = v := Fin.snoc_init_self v)
    exact hi.trans (safe_next_card bad (List.ofFn w) (hnext _))
  have hh := sum_le_sum hf
  simpa only [sum_const, Nat.nsmul_eq_mul] using hh

theorem safe_card_le (bad : List α → Prop)
    (hpersist : ∀ xs x, bad xs → bad (xs ++ [x]))
    (hnext : ∀ xs, ∃ x, bad (xs ++ [x])) (k : ℕ) :
    (safeWords bad k).card ≤ (Fintype.card α - 1) ^ k := by
  induction k with
  | zero =>
    have hh := card_le_card (filter_subset (fun w : Fin 0 → α => ¬ bad (List.ofFn w)) univ)
    simpa only [safeWords, card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero] using hh
  | succ k ih =>
    exact (safe_card_step bad hpersist hnext k).trans
      (by simpa only [pow_succ] using Nat.mul_le_mul_right (Fintype.card α - 1) ih)

theorem pow_succ_first_terms (x k : ℕ) :
    x ^ (k + 1) + (k + 1) * x ^ k ≤ (x + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := Nat.mul_le_mul_right (x + 1) ih
    calc
      x ^ (k + 1 + 1) + (k + 1 + 1) * x ^ (k + 1) ≤
          x ^ (k + 1 + 1) + (k + 1 + 1) * x ^ (k + 1) + (k + 1) * x ^ k := Nat.le_add_right _ _
      _ = (x ^ (k + 1) + (k + 1) * x ^ k) * (x + 1) := by rw [pow_succ, pow_succ]; ring
      _ ≤ (x + 1) ^ (k + 1 + 1) := by simpa only [pow_succ] using hh

theorem twice_pred_pow_le {N : ℕ} (hN : 0 < N) : 2 * (N - 1) ^ N ≤ N ^ N := by
  have hn : N - 1 + 1 = N := by omega
  have hh := pow_succ_first_terms (N - 1) (N - 1)
  rw [hn] at hh
  have hp : (N - 1) ^ N = (N - 1) ^ (N - 1) * (N - 1) := by
    calc
      (N - 1) ^ N = (N - 1) ^ (N - 1 + 1) := by rw [hn]
      _ = _ := pow_succ _ _
  have hm := Nat.mul_le_mul_right ((N - 1) ^ (N - 1)) (Nat.sub_le N 1)
  nlinarith

/-- Uniformly sampling `N` symbols from an alphabet of size `N` reaches
a bad word with probability at least one half. This is the exact finite
counting statement, with no independence or conditioning premise. -/
theorem half_words_bad [Nonempty α] (bad : List α → Prop)
    (hpersist : ∀ xs x, bad xs → bad (xs ++ [x]))
    (hnext : ∀ xs, ∃ x, bad (xs ++ [x])) :
    Fintype.card α ^ Fintype.card α ≤
      2 * (univ.filter (fun w : Fin (Fintype.card α) → α => bad (List.ofFn w))).card := by
  have hs := safe_card_le bad hpersist hnext (Fintype.card α)
  have hp := twice_pred_pow_le (Fintype.card_pos (α := α))
  have hpartition := card_filter_add_card_filter_not (s := (univ : Finset (Fin (Fintype.card α) → α)))
    (fun w => bad (List.ofFn w))
  simp only [card_univ, Fintype.card_fun, Fintype.card_fin] at hpartition
  change (univ.filter (fun w : Fin (Fintype.card α) → α => ¬ bad (List.ofFn w))).card ≤ _ at hs
  omega

theorem cost_sum_lower [Nonempty α] (cost : List α → ℕ) (F : ℕ)
    (hpersist : ∀ xs x, F ≤ cost xs → F ≤ cost (xs ++ [x]))
    (hnext : ∀ xs, ∃ x, F ≤ cost (xs ++ [x])) :
    Fintype.card (Fin (Fintype.card α) → α) * F ≤
      2 * ∑ w : Fin (Fintype.card α) → α, cost (List.ofFn w) := by
  have hb := half_words_bad (fun xs => F ≤ cost xs) hpersist hnext
  let s := univ.filter (fun w : Fin (Fintype.card α) → α => F ≤ cost (List.ofFn w))
  have hs : s.card * F ≤ ∑ w ∈ s, cost (List.ofFn w) := by
    calc
      s.card * F = ∑ _w ∈ s, F := by simp
      _ ≤ _ := sum_le_sum (fun w hw => (mem_filter.mp hw).2)
  have ht : ∑ w ∈ s, cost (List.ofFn w) ≤ ∑ w : Fin (Fintype.card α) → α, cost (List.ofFn w) :=
    sum_le_sum_of_subset (filter_subset _ _)
  have hb' : Fintype.card α ^ Fintype.card α ≤ 2 * s.card := by
    convert hb using 1
    congr 2
    ext w
    simp [s]
  have hh := Nat.mul_le_mul_right F hb'
  rw [Fintype.card_fun, Fintype.card_fin]
  nlinarith

end Scheduling.FiniteAmplification
