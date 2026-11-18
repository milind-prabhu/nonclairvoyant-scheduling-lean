import Scheduling.StarChain
import Scheduling.PublicGraph

namespace Scheduling.StarChain
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs m : ℕ}

def MiddleAt (long : Fin jobs → Bool) (hm : 0 < m)
    (S : Assignment (vertices := jobs * (3 * m))) (t : ℕ) : Prop :=
  ∃ j, long j = true ∧ S (middle hm j) = t

def TypeConsistent (long : Fin jobs → Bool) (hm : 0 < m)
    (S : Assignment (vertices := jobs * (3 * m))) (j : Fin jobs) : Prop :=
  long j = true ↔ ¬ MiddleAt long hm S (S (root hm j))

/-- A job's type can be chosen after the slot executing its root. All of
its nonroot vertices are still hidden at the beginning of that slot. -/
theorem change_type (A : DeterministicScheduler m) (hm : 0 < m)
    (long : Fin jobs → Bool) (j : Fin jobs) (b : Bool) :
    let I := toInstance long hm
    let J := toInstance (Function.update long j b) hm
    ∀ t ≤ A.schedule I (root hm j), ∀ v,
      A.schedule I v = t ↔ A.schedule J v = t := by
  dsimp only
  let I := toInstance long hm
  let J := toInstance (Function.update long j b) hm
  let hidden := univ.filter (fun v : Fin (jobs * (3 * m)) =>
    job v = j ∧ 0 < (position v).val)
  have hparent : ∀ v ∈ hidden, ∃ u, J.edge u v ∧
      A.schedule I (root hm j) ≤ A.schedule I u := by
    intro v hv
    obtain ⟨ho, hp⟩ := (mem_filter.mp hv).2
    obtain ⟨u, he⟩ := parent_exists (Function.update long j b) hm v hp
    refine ⟨u, he, ?_⟩
    have hu := parent_position (Function.update long j b) hm he
    have howner : job u = j := he.1.trans ho
    by_cases hz : (position u).val = 0
    · rw [eq_root hm u hz, howner]
    · have hone : (position u).val = 1 := by omega
      rw [eq_middle hm u hone, howner]
      exact Nat.le_of_lt ((A.valid I).precedence (middle_parent long hm j))
  have hreplace := A.hidden_replacement I J hidden rfl rfl (by
    intro u v hv
    by_cases ho : job v = j
    · have hz : (position v).val = 0 := by
        simp only [hidden, mem_filter, mem_univ, true_and, ho, true_and] at hv
        omega
      rw [eq_root hm v hz]
      exact iff_of_false (no_parent_root long hm _ u)
        (no_parent_root (Function.update long j b) hm _ u)
    · change (job u = job v ∧ _) ↔ (job u = job v ∧ _)
      simp only [Function.update_of_ne ho]) (by
    intro v hv
    obtain ⟨ho, hp⟩ := (mem_filter.mp hv).2
    obtain ⟨u, he⟩ := parent_exists long hm v hp
    refine ⟨u, he, ?_⟩
    have hu := parent_position long hm he
    have howner : job u = j := he.1.trans ho
    by_cases hz : (position u).val = 0
    · rw [eq_root hm u hz, howner]
    · have hone : (position u).val = 1 := by omega
      rw [eq_middle hm u hone, howner]
      exact Nat.le_of_lt ((A.valid I).precedence (middle_parent long hm j))) hparent
  intro t ht v
  have he := hreplace.1 t ht
  simpa only [val_mem_executionSlot] using
    (show v.val ∈ executionSlot (A.schedule I) t ↔
      v.val ∈ executionSlot (A.schedule J) t from by rw [he])

/-- Choosing a type cannot change which middle vertices execute in any
slot up to and including this job's root slot. -/
theorem change_type_middle (A : DeterministicScheduler m) (hm : 0 < m)
    (long : Fin jobs → Bool) (j : Fin jobs) (b : Bool)
    (t : ℕ) (ht : t ≤ A.schedule (toInstance long hm) (root hm j)) :
    MiddleAt long hm (A.schedule (toInstance long hm)) t ↔
      MiddleAt (Function.update long j b) hm
        (A.schedule (toInstance (Function.update long j b) hm)) t := by
  have hs := change_type A hm long j b t ht
  have hmid := (A.valid (toInstance long hm)).precedence (middle_parent long hm j)
  constructor
  · rintro ⟨i, hi, htime⟩
    have hij : i ≠ j := by rintro rfl; omega
    exact ⟨i, by simpa [Function.update_of_ne hij] using hi, (hs _).mp htime⟩
  · rintro ⟨i, hi, htime⟩
    have htime' := (hs _).mpr htime
    have hij : i ≠ j := by rintro rfl; omega
    exact ⟨i, by simpa [Function.update_of_ne hij] using hi, htime'⟩

def Settled (A : DeterministicScheduler m) (hm : 0 < m)
    (long : Fin jobs → Bool) (fixed : Finset (Fin jobs)) : Prop :=
  (∀ j ∈ fixed, TypeConsistent long hm (A.schedule (toInstance long hm)) j) ∧
    ∀ j ∈ fixed, ∀ k ∉ fixed,
      A.schedule (toInstance long hm) (root hm j) ≤
        A.schedule (toInstance long hm) (root hm k)

theorem settle_next (A : DeterministicScheduler m) (hm : 0 < m)
    (long : Fin jobs → Bool) (fixed : Finset (Fin jobs))
    (hfixed : Settled A hm long fixed) (j : Fin jobs) (hj : j ∉ fixed)
    (hmin : ∀ k ∉ fixed, A.schedule (toInstance long hm) (root hm j) ≤
      A.schedule (toInstance long hm) (root hm k)) :
    ∃ long', Settled A hm long' (insert j fixed) := by
  let S := A.schedule (toInstance long hm)
  let t := S (root hm j)
  let b := decide (¬ MiddleAt long hm S t)
  let long' := Function.update long j b
  let S' := A.schedule (toInstance long' hm)
  have hslot : ∀ u ≤ t, ∀ v, S v = u ↔ S' v = u := change_type A hm long j b
  have htime : ∀ v, S v ≤ t → S' v = S v := by
    intro v hv
    exact (hslot _ hv v).mp rfl
  have hmiddle : ∀ u ≤ t, MiddleAt long hm S u ↔ MiddleAt long' hm S' u :=
    change_type_middle A hm long j b
  have hnew : S' (root hm j) = t := htime _ le_rfl
  have hearly : ∀ i ∈ fixed, S' (root hm i) = S (root hm i) := by
    intro i hi
    exact htime _ (hfixed.2 i hi j hj)
  have hlate : ∀ k ∉ fixed, t ≤ S' (root hm k) := by
    intro k hk
    by_contra hn
    have hh : S' (root hm k) ≤ t := by omega
    have he := (hslot _ hh (root hm k)).mpr rfl
    have hle := hmin k hk
    change t ≤ S (root hm k) at hle
    omega
  refine ⟨long', ?_, ?_⟩
  · intro i hi
    rcases mem_insert.mp hi with hij | hi
    · subst i
      change long' j = true ↔ ¬ MiddleAt long' hm S' (S' (root hm j))
      rw [hnew, ← hmiddle t le_rfl]
      simp only [long', Function.update_self, b, decide_eq_true_eq]
    · have hij : i ≠ j := by intro heq; exact hj (heq ▸ hi)
      change long' i = true ↔ ¬ MiddleAt long' hm S' (S' (root hm i))
      rw [hearly i hi, ← hmiddle _ (hfixed.2 i hi j hj)]
      simpa only [long', Function.update_of_ne hij, TypeConsistent, S] using hfixed.1 i hi
  · intro i hi k hk
    have hk' : k ∉ fixed := fun h => hk (mem_insert_of_mem h)
    change S' (root hm i) ≤ S' (root hm k)
    rcases mem_insert.mp hi with rfl | hi
    · rw [hnew]
      exact hlate k hk'
    · rw [hearly i hi]
      exact (hfixed.2 i hi j hj).trans (hlate k hk')

/-- The adaptive rule is realized by a fixed star-and-chain instance for
every deterministic non-clairvoyant scheduler. Simultaneous roots receive
the same rule; changing one of them leaves that slot's middle set intact. -/
theorem exists_type_consistent (A : DeterministicScheduler m) (hm : 0 < m)
    (jobs : ℕ) : ∃ long : Fin jobs → Bool,
      ∀ j, TypeConsistent long hm (A.schedule (toInstance long hm)) j := by
  have extend : ∀ n : ℕ, ∀ (long : Fin jobs → Bool) (fixed : Finset (Fin jobs)),
      (univ \ fixed).card = n → Settled A hm long fixed →
      ∃ final : Fin jobs → Bool,
        ∀ j, TypeConsistent final hm (A.schedule (toInstance final hm)) j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro long fixed hn hf
      by_cases hempty : (univ \ fixed).Nonempty
      · obtain ⟨j, hj, hmin⟩ := exists_min_image (univ \ fixed)
          (fun j => A.schedule (toInstance long hm) (root hm j)) hempty
        have hj' : j ∉ fixed := (mem_sdiff.mp hj).2
        obtain ⟨long', hf'⟩ := settle_next A hm long fixed hf j hj' (by
          intro k hk
          exact hmin k (mem_sdiff.mpr ⟨mem_univ _, hk⟩))
        have he : univ \ insert j fixed = (univ \ fixed).erase j := by
          ext k
          simp only [mem_sdiff, mem_univ, mem_insert, mem_erase, true_and]
          tauto
        have hlt : (univ \ insert j fixed).card < n := by
          rw [he, ← hn]
          exact card_erase_lt_of_mem hj
        exact ih _ hlt long' (insert j fixed) rfl hf'
      · refine ⟨long, fun j => hf.1 j ?_⟩
        by_contra hj
        exact hempty ⟨j, mem_sdiff.mpr ⟨mem_univ _, hj⟩⟩
  exact extend _ (fun _ => true) ∅ rfl ⟨by simp, by simp⟩

end Scheduling.StarChain
