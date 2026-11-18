import Scheduling.StarChainAdversary
import Scheduling.RegularBacklog

namespace Scheduling.StarChain
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs m : ℕ} {long : Fin jobs → Bool} {hm : 0 < m}
variable {S : Assignment (vertices := jobs * (3 * m))}

theorem leaf_positive {v : Fin (jobs * (3 * m))} (hv : IsLeaf long v) :
    0 < (position v).val := by
  unfold IsLeaf at hv
  split_ifs at hv <;> omega

theorem nonleaf_position {v : Fin (jobs * (3 * m))} (hv : ¬ IsLeaf long v) :
    (position v).val ≤ 1 := by
  unfold IsLeaf at hv
  split_ifs at hv <;> omega

theorem executed_ready (hS : (toInstance long hm).Valid m S)
    (v : Fin (jobs * (3 * m))) : (toInstance long hm).Ready S (S v) v :=
  ⟨hS.release v, le_rfl, fun _ he => hS.precedence he⟩

theorem alive_card_lt (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (t : ℕ) : ((toInstance long hm).alive S t).card < m := by
  have hc := card_le_card_of_injOn Fin.val (s := (toInstance long hm).alive S t)
    (t := Ico (t / 3 + 1 - (m - 1)) (t / 3 + 1)) (by
      intro j hj
      obtain ⟨hr, v, ho, ht⟩ := (mem_filter.mp hj).2
      have hf := hflow v
      rw [ho] at hf
      change j.val * 3 ≤ t at hr
      change S v < j.val * 3 + 3 * (m - 1) at hf
      exact mem_Ico.mpr ⟨by omega, by omega⟩)
    (by intro u _ v _ huv; exact Fin.ext huv)
  have hlen : (Ico (t / 3 + 1 - (m - 1)) (t / 3 + 1)).card ≤ m - 1 := by
    rw [Nat.card_Ico]
    omega
  exact lt_of_le_of_lt (hc.trans hlen) (by omega)

theorem ready_nonleaf_injective (_hS : (toInstance long hm).Valid m S)
    {t : ℕ} {u v : Fin (jobs * (3 * m))}
    (hu : (toInstance long hm).Ready S t u) (hv : (toInstance long hm).Ready S t v)
    (hlu : ¬ IsLeaf long u) (hlv : ¬ IsLeaf long v) (ho : job u = job v) : u = v := by
  have hpu := nonleaf_position hlu
  have hpv := nonleaf_position hlv
  apply LayeredForest.coordinates_injective
  refine Prod.ext ho ?_
  change (position u).val = (position v).val
  by_contra hne
  have hcases : ((position u).val = 0 ∧ (position v).val = 1) ∨
      ((position v).val = 0 ∧ (position u).val = 1) := by omega
  rcases hcases with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
  · have he : (toInstance long hm).edge u v := by
      rw [eq_root hm u hu0, eq_middle hm v hv1, ho]
      exact middle_parent long hm _
    have hh := hv.2.2 u he
    have ht := hu.2.1
    omega
  · have he : (toInstance long hm).edge v u := by
      rw [eq_root hm v hv0, eq_middle hm u hu1, ho]
      exact middle_parent long hm _
    have hh := hu.2.2 v he
    have ht := hv.2.1
    omega

theorem no_leaves_idle (hS : (toInstance long hm).Valid m S)
    (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (t : ℕ) (hn : ∀ v, (toInstance long hm).Ready S t v → ¬ IsLeaf long v) :
    (univ.filter (fun v => S v = t)).card < m := by
  have hcard := card_le_card_of_injOn job
    (s := univ.filter (fun v => S v = t)) (t := (toInstance long hm).alive S t) (by
      intro v hv
      have he := (mem_filter.mp hv).2
      have hr := hS.release v
      refine mem_filter.mpr ⟨mem_univ _, ?_, v, rfl, ?_⟩
      · change (toInstance long hm).release (job v) ≤ S v at hr
        omega
      · omega) (by
      intro u hu v hv ho
      have hut := (mem_filter.mp hu).2
      have hvt := (mem_filter.mp hv).2
      have hru : (toInstance long hm).Ready S t u := hut ▸ executed_ready hS u
      have hrv : (toInstance long hm).Ready S t v := hvt ▸ executed_ready hS v
      exact ready_nonleaf_injective hS hru hrv (hn u hru) (hn v hrv) ho)
  exact hcard.trans_lt (alive_card_lt hflow t)

theorem no_leaves_process_all (hS : (toInstance long hm).Valid m S)
    (hfifo : (toInstance long hm).IsFIFO m S)
    (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (t : ℕ) (hn : ∀ v, (toInstance long hm).Ready S t v → ¬ IsLeaf long v)
    (v : Fin (jobs * (3 * m))) (hv : (toInstance long hm).Ready S t v) : S v = t := by
  by_contra he
  have hfull := hfifo.work_conserving t v hv he
  have hidle := no_leaves_idle hS hflow t hn
  omega

/-- Ready leaves are older than every unprocessed root and exclude
ready middle vertices. -/
def StateInvariant (long : Fin jobs → Bool) (hm : 0 < m) (S : Assignment (vertices := jobs * (3 * m))) (t : ℕ) : Prop :=
  (∀ v, (toInstance long hm).Ready S t v → IsLeaf long v →
    ∀ j, t ≤ S (root hm j) → (job v).val < j.val) ∧
  (∀ v, (toInstance long hm).Ready S t v → IsLeaf long v →
    ∀ w, (toInstance long hm).Ready S t w → ¬ IsMiddle long w)

theorem ready_root_iff (t : ℕ) (j : Fin jobs) :
    (toInstance long hm).Ready S t (root hm j) ↔ j.val * 3 ≤ t ∧ t ≤ S (root hm j) := by
  constructor
  · intro h
    exact ⟨by simpa [toInstance] using h.1, h.2.1⟩
  · intro h
    exact ⟨by simpa [toInstance] using h.1, h.2,
      fun u he => False.elim (no_parent_root long hm j u he)⟩

theorem ready_nonroot_iff (hS : (toInstance long hm).Valid m S)
    {u v : Fin (jobs * (3 * m))} (he : (toInstance long hm).edge u v) (t : ℕ) :
    (toInstance long hm).Ready S t v ↔ t ≤ S v ∧ S u < t := by
  constructor
  · intro h; exact ⟨h.2.1, h.2.2 u he⟩
  · intro h
    have hr := hS.release u
    rw [(toInstance long hm).same_job he] at hr
    exact ⟨by omega, h.1, fun w hw => by
      rw [at_most_one_parent long hm hw he]
      exact h.2⟩

def leafParent (long : Fin jobs → Bool) (hm : 0 < m)
    (v : Fin (jobs * (3 * m))) : Fin (jobs * (3 * m)) :=
  if long (job v) then middle hm (job v) else root hm (job v)

theorem leaf_parent_edge {v : Fin (jobs * (3 * m))} (hv : IsLeaf long v) :
    (toInstance long hm).edge (leafParent long hm v) v := by
  unfold leafParent IsLeaf at *
  split_ifs at * <;> simp_all [toInstance]

theorem fresh_leaf_has_middle (_hS : (toInstance long hm).Valid m S)
    (hc : ∀ j, TypeConsistent long hm S j)
    {t : ℕ} {v : Fin (jobs * (3 * m))} (_hv : IsLeaf long v)
    (hparent : S (leafParent long hm v) = t) : MiddleAt long hm S t := by
  by_cases hl : long (job v) = true
  · exact ⟨job v, hl, by simpa [leafParent, hl] using hparent⟩
  · have hr : S (root hm (job v)) = t := by simpa [leafParent, hl] using hparent
    have hh := hc (job v)
    unfold TypeConsistent at hh
    rw [hr] at hh
    by_contra hn
    exact hl (hh.mpr hn)

theorem leaf_persists (hS : (toInstance long hm).Valid m S)
    (hc : ∀ j, TypeConsistent long hm S j) {t : ℕ}
    (hinv : StateInvariant long hm S t)
    (hex : ∃ w, (toInstance long hm).Ready S t w ∧ IsLeaf long w)
    {v : Fin (jobs * (3 * m))} (hv : (toInstance long hm).Ready S (t + 1) v)
    (hl : IsLeaf long v) : (toInstance long hm).Ready S t v := by
  obtain ⟨w, hw, hwl⟩ := hex
  have hp := (ready_nonroot_iff hS (leaf_parent_edge hl) (t + 1)).mp hv
  have hne : S (leafParent long hm v) ≠ t := by
    intro he
    obtain ⟨j, hj, ht⟩ := fresh_leaf_has_middle hS hc hl he
    have hr : (toInstance long hm).Ready S t (middle hm j) := ht ▸ executed_ready hS _
    exact hinv.2 w hw hwl _ hr ⟨by simpa, by simp⟩
  exact (ready_nonroot_iff hS (leaf_parent_edge hl) t).mpr ⟨by omega, by omega⟩

theorem stateInvariant_zero (_hS : (toInstance long hm).Valid m S) :
    StateInvariant long hm S 0 := by
  have hn : ∀ v, (toInstance long hm).Ready S 0 v → ¬ IsLeaf long v := by
    intro v hv hl
    have hp := hv.2.2 _ (leaf_parent_edge hl)
    omega
  exact ⟨fun v hv hl => False.elim (hn v hv hl),
    fun v hv hl => False.elim (hn v hv hl)⟩

theorem stateInvariant_step (hS : (toInstance long hm).Valid m S)
    (hfifo : (toInstance long hm).IsFIFO m S)
    (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (hc : ∀ j, TypeConsistent long hm S j) {t : ℕ}
    (hinv : StateInvariant long hm S t) : StateInvariant long hm S (t + 1) := by
  by_cases hex : ∃ v, (toInstance long hm).Ready S t v ∧ IsLeaf long v
  · have hpersist := fun v hv hl => leaf_persists hS hc hinv hex (v := v) hv hl
    constructor
    · intro v hv hl j hj
      exact hinv.1 v (hpersist v hv hl) hl j (by omega)
    · intro v hv hl w hw hmid
      have hvt := hpersist v hv hl
      have hwpos := hmid.2
      have he : (toInstance long hm).edge (root hm (job w)) w := by
        rw [eq_middle hm w hwpos]
        simpa only [job_middle] using middle_parent long hm (job w)
      have hwp := (ready_nonroot_iff hS he (t + 1)).mp hw
      by_cases heq : S (root hm (job w)) = t
      · have hne : S v ≠ t := by have := hv.2.1; omega
        have hprio := hfifo.fifo_priority t v (root hm (job w)) hvt hne heq
        have hold := hinv.1 v hvt hl (job w) (by omega)
        simp only [toInstance, job_root] at hprio
        omega
      · have hwold : (toInstance long hm).Ready S t w :=
          (ready_nonroot_iff hS he t).mpr ⟨by omega, by omega⟩
        exact hinv.2 v hvt hl w hwold hmid
  · have hn : ∀ v, (toInstance long hm).Ready S t v → ¬ IsLeaf long v := by
      intro v hv hl
      exact hex ⟨v, hv, hl⟩
    have hall := no_leaves_process_all hS hfifo hflow t hn
    have hroots : ∀ j, t + 1 ≤ S (root hm j) → t < j.val * 3 := by
      intro j hj
      by_contra hh
      have hr : (toInstance long hm).Ready S t (root hm j) :=
        (ready_root_iff t j).mpr ⟨by omega, by omega⟩
      have he := hall _ hr
      omega
    constructor
    · intro v hv hl j hj
      have hp := hv.2.2 _ (leaf_parent_edge hl)
      have hr := hS.release (leafParent long hm v)
      have howner : job (leafParent long hm v) = job v := by
        unfold leafParent
        split_ifs <;> simp
      change (job (leafParent long hm v)).val * 3 ≤ S (leafParent long hm v) at hr
      rw [howner] at hr
      have hh := hroots j hj
      omega
    · intro v hv hl w hw hmid
      have hp := (ready_nonroot_iff hS (leaf_parent_edge hl) (t + 1)).mp hv
      have hpt : S (leafParent long hm v) = t := by
        by_contra hh
        have hvold : (toInstance long hm).Ready S t v :=
          (ready_nonroot_iff hS (leaf_parent_edge hl) t).mpr ⟨by omega, by omega⟩
        exact hn v hvold hl
      have hmiddle := fresh_leaf_has_middle hS hc hl hpt
      have he : (toInstance long hm).edge (root hm (job w)) w := by
        rw [eq_middle hm w hmid.2]
        simpa only [job_middle] using middle_parent long hm (job w)
      have hwp := (ready_nonroot_iff hS he (t + 1)).mp hw
      have hrt : S (root hm (job w)) = t := by
        by_contra hh
        have hwold : (toInstance long hm).Ready S t w :=
          (ready_nonroot_iff hS he t).mpr ⟨by omega, by omega⟩
        have hdone := hall w hwold
        omega
      have hnone := (hc (job w)).mp hmid.1
      rw [hrt] at hnone
      exact hnone hmiddle

theorem stateInvariant_all (hS : (toInstance long hm).Valid m S)
    (hfifo : (toInstance long hm).IsFIFO m S)
    (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (hc : ∀ j, TypeConsistent long hm S j) (t : ℕ) : StateInvariant long hm S t := by
  induction t with
  | zero => exact stateInvariant_zero hS
  | succ t ih => exact stateInvariant_step hS hfifo hflow hc ih

theorem leaf_run_subset (hS : (toInstance long hm).Valid m S)
    (hfifo : (toInstance long hm).IsFIFO m S)
    (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (hc : ∀ j, TypeConsistent long hm S j) (a n : ℕ)
    (hex : ∀ k < n, ∃ v, (toInstance long hm).Ready S (a + k) v ∧ IsLeaf long v)
    {v : Fin (jobs * (3 * m))} (hv : (toInstance long hm).Ready S (a + n) v)
    (hl : IsLeaf long v) : (toInstance long hm).Ready S a v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hprev := leaf_persists hS hc (stateInvariant_all hS hfifo hflow hc (a + n))
      (hex n (by omega)) (by simpa [Nat.add_assoc] using hv) hl
    exact ih (fun k hk => hex k (by omega)) hprev

/-- Every block of `3(m-1)+1` slots wastes capacity if the maximum flow
were at most `3(m-1)`. A continuous run of ready leaves can only shrink,
so no such run can last longer than the assumed flow bound. -/
theorem block_has_idle (hS : (toInstance long hm).Valid m S)
    (hfifo : (toInstance long hm).IsFIFO m S)
    (hflow : (toInstance long hm).FlowBound S (3 * (m - 1)))
    (hc : ∀ j, TypeConsistent long hm S j) (a : ℕ) :
    ∃ t ∈ Ico a (a + (3 * (m - 1) + 1)),
      (univ.filter (fun v => S v = t)).card < m := by
  by_contra hn
  push Not at hn
  have hex : ∀ k ≤ 3 * (m - 1),
      ∃ v, (toInstance long hm).Ready S (a + k) v ∧ IsLeaf long v := by
    intro k hk
    by_contra hnone
    have hno : ∀ v, (toInstance long hm).Ready S (a + k) v → ¬ IsLeaf long v := by
      intro v hv hl; exact hnone ⟨v, hv, hl⟩
    have hidle := no_leaves_idle hS hflow (a + k) hno
    have hfull := hn (a + k) (mem_Ico.mpr ⟨by omega, by omega⟩)
    omega
  obtain ⟨v, hv, hl⟩ := hex _ le_rfl
  have hstart := leaf_run_subset hS hfifo hflow hc a (3 * (m - 1))
    (fun k hk => hex k (by omega)) hv hl
  have hr := hstart.1
  have ht := hv.2.1
  have hf := hflow v
  omega

end Scheduling.StarChain
