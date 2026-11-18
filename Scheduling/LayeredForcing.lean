import Scheduling.LayeredExecution
import Scheduling.RegularBacklog

namespace Scheduling.LayeredForest
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs work : ℕ} (F : LayeredForest jobs work)

def revealTime (S : Assignment (vertices := jobs * work)) (L : ℕ)
    (v : Fin (jobs * work)) : ℕ :=
  max ((job v).val * L) (if hp : 0 < F.vertexLevel v then
    S (F.key (job v) ⟨F.vertexLevel v - 1, by
      have := F.level_lt (job v) (position v); change F.vertexLevel v < F.depth (job v) at this; omega⟩) + 1
    else 0)

theorem ready_iff_reveal {L t : ℕ} {S : Assignment (vertices := jobs * work)}
    (v : Fin (jobs * work)) :
    (F.toInstance L).Ready S t v ↔ F.revealTime S L v ≤ t ∧ t ≤ S v := by
  unfold revealTime
  by_cases hp : 0 < F.vertexLevel v
  · rw [dif_pos hp]
    have hedge := F.key_parent (L := L) v hp
    constructor
    · intro h
      exact ⟨max_le h.1 (by have := h.2.2 _ hedge; omega), h.2.1⟩
    · intro h
      refine ⟨(le_max_left _ _).trans h.1, h.2, ?_⟩
      intro u hu
      have he := F.at_most_one_parent L hu hedge
      rw [he]
      have := (le_max_right _ _).trans h.1
      omega
  · rw [dif_neg hp, max_eq_left (Nat.zero_le _)]
    constructor
    · intro h; exact ⟨h.1, h.2.1⟩
    · intro h
      refine ⟨h.1, h.2, ?_⟩
      intro u hu
      have he : (position u).val + 1 = F.vertexLevel v := hu.2
      omega

theorem reveal_le_execution {m L : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (v : Fin (jobs * work)) :
    F.revealTime S L v ≤ S v :=
  ((F.ready_iff_reveal v).mp ⟨hS.release v, le_rfl, fun _ he => hS.precedence he⟩).1

/-- A forcing interval may begin with one wide frontier. Every layer
revealed strictly after its beginning and before its end must be narrow. -/
def NewLayersNarrow (S : Assignment (vertices := jobs * work)) (L a b : ℕ) : Prop :=
  ∀ v, a < F.revealTime S L v → F.revealTime S L v < b →
    (F.layerVertices (job v) (F.vertexLevel v)).card ≤ 1

theorem interval_job_work {m L a b W : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    (hwidth : ∀ j l, (F.layerVertices j l).card ≤ W)
    (hnarrow : F.NewLayersNarrow S L a b) (j : Fin jobs) :
    (univ.filter (fun v => job v = j ∧ a ≤ S v ∧ S v < b)).card ≤ W + (b - a) := by
  classical
  let R := univ.filter (fun v : Fin (jobs * work) => job v = j ∧ a ≤ S v ∧ S v < b)
  let Q := R.filter (fun v => (F.toInstance L).Ready S a v)
  let N := R.filter (fun v => ¬ (F.toInstance L).Ready S a v)
  have hQ : Q.card ≤ W := by
    apply (card_le_card (t := univ.filter (fun v => job v = j ∧ (F.toInstance L).Ready S a v)) ?_).trans
      (F.ready_card_le_width hS hkey hwidth j)
    intro v hv
    have hv' := mem_filter.mp hv
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv'.1).2.1, hv'.2⟩
  have hN : N.card ≤ b - a := by
    have hc := card_le_card_of_injOn S (s := N) (t := Ico a b)
      (by intro v hv; exact mem_Ico.mpr (mem_filter.mp (mem_filter.mp hv).1).2.2)
      (by
        intro u hu v hv he
        have hu' := mem_filter.mp hu
        have hv' := mem_filter.mp hv
        have hur := (mem_filter.mp hu'.1).2
        have hvr := (mem_filter.mp hv'.1).2
        have hlevel := F.simultaneous_same_layer hS hkey (hur.1.trans hvr.1.symm) he
        have hreveal : a < F.revealTime S L u := by
          have hn := hu'.2
          rw [F.ready_iff_reveal] at hn
          omega
        have hcard := hnarrow u hreveal ((F.reveal_le_execution hS u).trans_lt hur.2.2)
        apply card_le_one.mp hcard
        · exact mem_filter.mpr ⟨mem_univ _, rfl, rfl⟩
        · exact mem_filter.mpr ⟨mem_univ _, hvr.1.trans hur.1.symm, hlevel.symm⟩)
    simpa using hc
  have he := card_filter_add_card_filter_not (s := R) (fun v => (F.toInstance L).Ready S a v)
  change Q.card + N.card = R.card at he
  change R.card ≤ W + (b - a)
  omega

/-- Summing over alive jobs derives the local processed-work bound used
by the forcing-capacity calculation. No work inequality is assumed. -/
theorem interval_work {m L a b W : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    (hwidth : ∀ j l, (F.layerVertices j l).card ≤ W)
    (hnarrow : F.NewLayersNarrow S L a b)
    (harrivals : ∀ v, a ≤ S v → S v < b → (job v).val * L ≤ a) :
    (univ.filter (fun v => a ≤ S v ∧ S v < b)).card ≤
      ((F.toInstance L).alive S a).card * (W + (b - a)) := by
  classical
  let R := univ.filter (fun v : Fin (jobs * work) => a ≤ S v ∧ S v < b)
  have hf : ∀ v ∈ R, job v ∈ (F.toInstance L).alive S a := by
    intro v hv
    have ht := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _, harrivals v ht.1 ht.2, v, rfl, ht.1⟩
  have he := card_eq_sum_card_fiberwise hf
  change R.card ≤ _
  rw [he]
  calc
    _ ≤ ∑ _j ∈ (F.toInstance L).alive S a, (W + (b - a)) := by
      apply sum_le_sum
      intro j _
      have hset : R.filter (fun v => job v = j) =
          univ.filter (fun v => job v = j ∧ a ≤ S v ∧ S v < b) := by
        ext v
        simp only [R, mem_filter, mem_univ, true_and]
        tauto
      rw [hset]
      exact F.interval_job_work hS hkey hwidth hnarrow j
    _ = _ := by simp

/-- A forcing half-epoch loses capacity, derived from its layer structure. -/
theorem forcing_epoch_idle {m L c i : ℕ} {S : Assignment (vertices := jobs * work)}
    (hm : 0 < m) (hL : 0 < L) (hhalf : 2 * (L / 2) = L)
    (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    (hwidth : ∀ j l, (F.layerVertices j l).card ≤ 2 * m)
    (hnarrow : F.NewLayersNarrow S L (i * L) (i * L + L / 2))
    (halive : ((F.toInstance L).alive S (i * L)).card ≤ c) :
    (F.toInstance L).epochWork S L i < m * L := by
  have hhalf_le : L / 2 ≤ L := Nat.div_le_self _ _
  have hw := F.interval_work hS hkey hwidth hnarrow (by
    intro v _ hvt
    exact (F.toInstance L).regular_epoch_no_arrivals hS hL (by intros; rfl) v (by nlinarith))
  simp only [Nat.add_sub_cancel_left] at hw
  have hscaled : 2 * (univ.filter (fun v => i * L ≤ S v ∧ S v < i * L + L / 2)).card ≤
      ((F.toInstance L).alive S (i * L)).card * (4 * m + L) := by
    have h := Nat.mul_le_mul_left 2 hw
    have he : 2 * (2 * m + L / 2) = 4 * m + L := by omega
    nlinarith
  have hgap := Accounting.forcing_capacity_gap hm hL halive hcL hcm hscaled
  have hdeficit : (univ.filter (fun v => i * L ≤ S v ∧ S v < i * L + L / 2)).card <
      m * (i * L + L / 2 - i * L) := by
    rw [Nat.add_sub_cancel_left]
    nlinarith
  obtain ⟨t, ht, hidle⟩ := (F.toInstance L).interval_deficit_has_idle hS hdeficit
  apply (F.toInstance L).epochWork_lt_of_idle hS hL (t := t) _ hidle
  have ht' := mem_Ico.mp ht
  exact mem_Ico.mpr ⟨ht'.1, by nlinarith⟩

/-- The full deterministic accounting argument on layered forests.
The remaining adversarial construction must supply `KeyLast` and the
narrow-layer condition; it need not assume any idle-capacity or backlog bound. -/
theorem forcing_flow_lower {m L c : ℕ} {S : Assignment (vertices := jobs * work)}
    (hm : 0 < m) (hL : 0 < L) (hc : 0 < c)
    (hhalf : 2 * (L / 2) = L) (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (hn : jobs = c * (c * (m * L))) (hw : work = m * L)
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    (hwidth : ∀ j l, (F.layerVertices j l).card ≤ 2 * m)
    (hnarrow : ∀ k < c * (m * L),
      F.NewLayersNarrow S L ((c * k) * L) ((c * k) * L + L / 2)) :
    c * L ≤ (F.toInstance L).maxFlow S := by
  by_contra h
  have hf : (F.toInstance L).FlowBound S (c * L) :=
    ((F.toInstance L).flowBound_iff_maxFlow_le S _).mpr (by omega)
  have hb := (F.toInstance L).regular_forcing_flow_lower hm hL hc hn hS
    (by intros; rfl) (by intro j; exact (F.jobVertices_card L j).trans hw) (by
      intro k hk
      exact F.forcing_epoch_idle hm hL hhalf hcL hcm hS hkey hwidth (hnarrow k hk)
        ((F.toInstance L).regular_alive_card_le hL (by intros; rfl) hf (c * k)))
  exact h hb

/-- Quantitative comparison with the attained offline optimum, conditional
only on the stated forest and layer-selection properties. -/
theorem forcing_competitive_lower {m L c : ℕ} {S : Assignment (vertices := jobs * work)}
    (hm : 2 ≤ m) (hL : 0 < L) (hc : 0 < c)
    (hhalf : 2 * (L / 2) = L) (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (hn : jobs = c * (c * (m * L))) (hw : work = m * L)
    (hd : ∀ j, F.depth j ≤ L)
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    (hwidth : ∀ j l, (F.layerVertices j l).card ≤ 2 * m)
    (hnarrow : ∀ k < c * (m * L),
      F.NewLayersNarrow S L ((c * k) * L) ((c * k) * L + L / 2)) :
    c * (F.toInstance L).optimum m (by omega) ≤ 2 * (F.toInstance L).maxFlow S := by
  have hm0 : 0 < m := by omega
  have hj : 0 < jobs := by rw [hn]; exact Nat.mul_pos hc (Nat.mul_pos hc (Nat.mul_pos hm0 hL))
  have ho := (F.optimum_bounds hm hj hw hd).2
  have hf := F.forcing_flow_lower hm0 hL hc hhalf hcL hcm hn hw hS hkey hwidth hnarrow
  have := Nat.mul_le_mul_left c ho
  nlinarith

end Scheduling.LayeredForest
