import Scheduling.Backlog
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Scheduling.Instance jobs vertices)

noncomputable def prefixService (S : Assignment (vertices := vertices)) (r t : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => S v = t ∧ I.release (I.owner v) ≤ r)

def PrefixFull (m : ℕ) (S : Assignment (vertices := vertices)) (r t : ℕ) : Prop :=
  (I.prefixService S r t).card = m

noncomputable def partialSlots (m : ℕ) (S : Assignment (vertices := vertices)) (r t : ℕ) : Finset ℕ :=
  (Ico r t).filter (fun s => ¬ I.PrefixFull m S r s)

theorem partialSlots_succ {m r t : ℕ} {S : Assignment (vertices := vertices)} (hrt : r ≤ t) :
    (I.partialSlots m S r (t + 1)).card = (I.partialSlots m S r t).card +
      (if I.PrefixFull m S r t then 0 else 1) := by
  classical
  have hi : Ico r (t + 1) = insert t (Ico r t) := by
    ext x
    simp only [mem_Ico, mem_insert]
    omega
  rw [partialSlots, hi]
  by_cases h : I.PrefixFull m S r t
  · simp [Finset.filter_insert, h, partialSlots]
  · simp [Finset.filter_insert, h, partialSlots]

theorem prefixService_card_le {m r t : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) : (I.prefixService S r t).card ≤ m := by
  classical
  apply (card_le_card (t := univ.filter (fun v => S v = t)) ?_).trans (hS.capacity t)
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2.1⟩

/-- If a slot is not full on the old-job prefix, FIFO processes every ready
vertex of the target job in that slot. -/
theorem ready_processed_of_partial {m r t : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hp : ¬ I.PrefixFull m S r t)
    {v : Fin vertices} (hv : I.Ready S t v) (hr : I.release (I.owner v) ≤ r) : S v = t := by
  classical
  by_contra hne
  have hg := hF.work_conserving t v hv hne
  have hsub : univ.filter (fun u => S u = t) ⊆ I.prefixService S r t := by
    intro u hu
    have he := (mem_filter.mp hu).2
    exact mem_filter.mpr ⟨mem_univ _, he,
      (hF.fifo_priority t v u hv hne he).trans hr⟩
  apply hp
  apply Nat.le_antisymm (I.prefixService_card_le hS)
  rw [← hg]
  exact card_le_card hsub

/-- Sequential progress measured using an offline schedule: after `p` partial
slots, every remaining vertex has offline slot at least release + p.
This proves the longest-path step without postulating a depth-decrease axiom. -/
theorem partial_progress {m : ℕ} {S O : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O)
    (j : Fin jobs) (t : ℕ) (hrt : I.release j ≤ t)
    (v : Fin vertices) (hj : I.owner v = j) (htv : t ≤ S v) :
    I.release j + (I.partialSlots m S (I.release j) t).card ≤ O v := by
  classical
  induction t using Nat.strong_induction_on generalizing v with
  | h t ih =>
    by_cases he : t = I.release j
    · subst t
      simpa [partialSlots, hj] using hO.release v
    · have hrprev : I.release j ≤ t - 1 := by omega
      have htprev : t - 1 < t := by omega
      have hvprev : t - 1 ≤ S v := by omega
      have hprev := ih (t - 1) htprev hrprev v hj hvprev
      have ht : t - 1 + 1 = t := by omega
      have hrec := I.partialSlots_succ (m := m) (S := S) hrprev
      rw [ht] at hrec
      by_cases hf : I.PrefixFull m S (I.release j) (t - 1)
      · rw [if_pos hf] at hrec
        omega
      · rw [if_neg hf] at hrec
        have hnotready : ¬ I.Ready S (t - 1) v := by
          intro hready
          have := I.ready_processed_of_partial hS hF hf hready (by rw [hj])
          omega
        have hpred : ∃ u, I.edge u v ∧ t - 1 ≤ S u := by
          by_contra hn
          push Not at hn
          exact hnotready ⟨by rw [hj]; exact hrprev, hvprev,
            by intro u hu; have := hn u hu; omega⟩
        obtain ⟨u, heuv, hu⟩ := hpred
        have hju : I.owner u = j := (I.same_job heuv).trans hj
        have hpu := ih (t - 1) htprev hrprev u hju hu
        have hprec := hO.precedence heuv
        omega

/-- At most L-1 partial slots have occurred while a job is still unfinished. -/
theorem partial_slots_lt {m L t : ℕ} {S O : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (hO : I.Valid m O)
    (hL : I.FlowBound O L) (j : Fin jobs) (hrt : I.release j ≤ t)
    (hu : ∃ v, I.owner v = j ∧ t ≤ S v) :
    (I.partialSlots m S (I.release j) t).card < L := by
  obtain ⟨v, hj, hv⟩ := hu
  have h := I.partial_progress hS hF hO j t hrt v hj hv
  have hbound := hL v
  rw [hj] at hbound
  omega

noncomputable def prefixWork (S : Assignment (vertices := vertices)) (r t : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => r ≤ S v ∧ S v < t ∧ I.release (I.owner v) ≤ r)

theorem prefixWork_card {S : Assignment (vertices := vertices)} (r t : ℕ) :
    (I.prefixWork S r t).card = ∑ s ∈ Ico r t, (I.prefixService S r s).card := by
  classical
  have hf : ∀ s ∈ Ico r t,
      (I.prefixWork S r t).filter (fun v => S v = s) = I.prefixService S r s := by
    intro s hs
    have hs' := mem_Ico.mp hs
    ext v
    simp only [prefixWork, prefixService, mem_filter, mem_univ, true_and]
    constructor
    · intro h; exact ⟨h.2, h.1.2.2⟩
    · intro h; exact ⟨⟨by omega, by omega, h.2⟩, h.1⟩
  have heq : (I.prefixWork S r t).card =
      ∑ s ∈ Ico r t, ((I.prefixWork S r t).filter (fun v => S v = s)).card :=
    card_eq_sum_card_fiberwise (by intro v hv; have h := (mem_filter.mp hv).2; exact mem_Ico.mpr ⟨h.1, h.2.1⟩)
  rw [heq]
  apply sum_congr rfl
  intro s hs
  rw [hf s hs]

theorem prefixWork_le_remaining {S : Assignment (vertices := vertices)} (r t : ℕ) :
    (I.prefixWork S r t).card ≤ (I.remaining S r).card := by
  classical
  apply card_le_card
  intro v hv
  have h := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ _, h.2.2, h.1⟩

/-- Charge m units to full slots and one unit to each partial slot in a
target job's lifetime. All charges are to distinct old-prefix vertices. -/
theorem fifo_service_accounting {m t : ℕ} {S : Assignment (vertices := vertices)}
    (hS : I.Valid m S) (hF : I.IsFIFO m S) (j : Fin jobs)
    (v : Fin vertices) (hj : I.owner v = j) (ht : t ≤ S v + 1) :
    m * ((Ico (I.release j) t).filter (I.PrefixFull m S (I.release j))).card +
      (I.partialSlots m S (I.release j) t).card ≤ (I.remaining S (I.release j)).card := by
  classical
  have hslot : ∀ s ∈ Ico (I.release j) t,
      (if I.PrefixFull m S (I.release j) s then m else 1) ≤
        (I.prefixService S (I.release j) s).card := by
    intro s hs
    have hs' := mem_Ico.mp hs
    by_cases hf : I.PrefixFull m S (I.release j) s
    · simp only [if_pos hf]; exact le_of_eq hf.symm
    · simp only [if_neg hf]
      obtain ⟨w, hw, hready⟩ := I.exists_ready (S := S) hs'.1 ⟨v, hj, by omega⟩
      have he := I.ready_processed_of_partial hS hF hf hready (by rw [hw])
      have hmem : w ∈ I.prefixService S (I.release j) s :=
        mem_filter.mpr ⟨mem_univ _, he, by rw [hw]⟩
      exact card_pos.mpr ⟨w, hmem⟩
  have hsum := sum_le_sum hslot
  have heq : (∑ s ∈ Ico (I.release j) t,
      if I.PrefixFull m S (I.release j) s then m else 1) =
      m * ((Ico (I.release j) t).filter (I.PrefixFull m S (I.release j))).card +
      (I.partialSlots m S (I.release j) t).card := by
    rw [sum_ite]
    simp [partialSlots, Nat.mul_comm]
  rw [heq, ← I.prefixWork_card] at hsum
  exact hsum.trans (I.prefixWork_le_remaining _ _)

/-- Theorem 8, as a denominator-free inequality on each vertex's completion
time. It is exactly the factor m + 1 - 1/m, without rounding a rational. -/
theorem fifo_vertex_bound {m L : ℕ} {S O : Assignment (vertices := vertices)}
    (hm : 0 < m) (hS : I.Valid m S) (hF : I.IsFIFO m S)
    (hO : I.Valid m O) (hL : I.FlowBound O L) (v : Fin vertices) :
    m * (S v + 1 - I.release (I.owner v)) ≤ (m * m + m - 1) * L := by
  classical
  let r := I.release (I.owner v)
  let C := S v + 1
  let P := (I.partialSlots m S r C).card
  let F := ((Ico r C).filter (I.PrefixFull m S r)).card
  have hr : r ≤ S v := hS.release v
  have hp0 := I.partial_slots_lt hS hF hO hL (I.owner v) hr ⟨v, rfl, le_rfl⟩
  have hrec := I.partialSlots_succ (m := m) (S := S) hr
  have hp : P ≤ L := by
    dsimp [P, C, r]
    dsimp [r] at hrec
    split_ifs at hrec <;> omega
  have hpartition : F + P = C - r := by
    dsimp [F, P, partialSlots]
    simpa using card_filter_add_card_filter_not (s := Ico r C) (I.PrefixFull m S r)
  have hwork : m * F + P ≤ m * m * L :=
    (I.fifo_service_accounting hS hF (I.owner v) v rfl (t := C) le_rfl).trans
      (I.fifo_backlog_bound hm hS hF hO hL r)
  have hm1 : m - 1 + 1 = m := by omega
  have hmul : (m - 1) * P ≤ (m - 1) * L := Nat.mul_le_mul_left _ hp
  have heq : (m * m + m - 1) * L = m * m * L + (m - 1) * L := by
    have haux : m * m + m - 1 = m * m + (m - 1) := by omega
    rw [haux, Nat.add_mul]
  change m * (C - r) ≤ _
  rw [← hpartition, Nat.mul_add, heq]
  nlinarith

/-- Theorem 8 for maximum flow time of a concrete FIFO schedule. -/
theorem fifo_maxFlow_bound {m L : ℕ} {S O : Assignment (vertices := vertices)}
    (hm : 0 < m) (hS : I.Valid m S) (hF : I.IsFIFO m S)
    (hO : I.Valid m O) (hL : I.FlowBound O L) :
    m * I.maxFlow S ≤ (m * m + m - 1) * L := by
  classical
  have hj : ∀ j, m * (I.completion S j - I.release j) ≤ (m * m + m - 1) * L := by
    intro j
    have hn : (I.jobVertices j).Nonempty := by
      obtain ⟨v, hv⟩ := I.nonempty_job j
      exact ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
    obtain ⟨v, hv, heq⟩ := Finset.exists_mem_eq_sup (I.jobVertices j) hn (fun v => S v + 1)
    have ho := (mem_filter.mp hv).2
    have h := I.fifo_vertex_bound hm hS hF hO hL v
    simpa [completion, ← heq, ho] using h
  by_cases hjobs : (univ : Finset (Fin jobs)).Nonempty
  · obtain ⟨j, _, heq⟩ := Finset.exists_mem_eq_sup univ hjobs (fun j => I.completion S j - I.release j)
    simpa [maxFlow, ← heq] using hj j
  · have he : (univ : Finset (Fin jobs)) = ∅ := not_nonempty_iff_eq_empty.mp hjobs
    simp [maxFlow, he]

end Scheduling.Instance
