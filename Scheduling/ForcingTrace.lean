import Scheduling.JobLayers

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

/-- A local trace of contiguous layers during a forcing interval. Each
layer executes between its reveal and closing times; the next layer waits
until the closing time plus one. Newly revealed layers are narrow. -/
inductive ForcingTrace {work : ℕ} (S : Fin work → ℕ) (a b W : ℕ) : ℕ → ℕ → Prop
  | done (e : ℕ) : ForcingTrace S a b W work e
  | layer (s d e t : ℕ) (hsd : s < d) (hd : d ≤ work) (het : e ≤ t)
      (hwidth : d - s ≤ W) (hnarrow : a < e → e < b → d - s ≤ 1)
      (htimes : ∀ v : Fin work, s ≤ v.val → v.val < d → e ≤ S v ∧ S v ≤ t)
      (tail : ForcingTrace S a b W d (t + 1)) : ForcingTrace S a b W s e

noncomputable def suffixService {work : ℕ} (S : Fin work → ℕ) (a b s : ℕ) : ℕ :=
  (univ.filter (fun v => s ≤ v.val ∧ a ≤ S v ∧ S v < b)).card

noncomputable def layerService {work : ℕ} (S : Fin work → ℕ) (a b s d : ℕ) : ℕ :=
  (univ.filter (fun v => s ≤ v.val ∧ v.val < d ∧ a ≤ S v ∧ S v < b)).card

theorem suffixService_split {work : ℕ} (S : Fin work → ℕ) (a b s d : ℕ) (hsd : s ≤ d) :
    suffixService S a b s = layerService S a b s d + suffixService S a b d := by
  classical
  let R := univ.filter (fun v : Fin work => s ≤ v.val ∧ a ≤ S v ∧ S v < b)
  have h := card_filter_add_card_filter_not (s := R) (fun v => v.val < d)
  have h₁ : R.filter (fun v => v.val < d) =
      univ.filter (fun v => s ≤ v.val ∧ v.val < d ∧ a ≤ S v ∧ S v < b) := by
    ext v; simp only [R, mem_filter, mem_univ, true_and]; tauto
  have h₂ : R.filter (fun v => ¬ v.val < d) =
      univ.filter (fun v => d ≤ v.val ∧ a ≤ S v ∧ S v < b) := by
    ext v
    simp only [R, mem_filter, mem_univ, true_and, not_lt]
    constructor
    · rintro ⟨⟨_, ha, hb⟩, hd⟩; exact ⟨hd, ha, hb⟩
    · rintro ⟨hd, ha, hb⟩; exact ⟨⟨hsd.trans hd, ha, hb⟩, hd⟩
  rw [h₁, h₂] at h
  exact h.symm

theorem layerService_le_width {work : ℕ} (S : Fin work → ℕ) (a b s d : ℕ) :
    layerService S a b s d ≤ d - s := by
  classical
  have h := card_le_card_of_injOn Fin.val
    (s := univ.filter (fun v : Fin work => s ≤ v.val ∧ v.val < d ∧ a ≤ S v ∧ S v < b))
    (t := Ico s d) (by intro v hv; exact mem_Ico.mpr ⟨(mem_filter.mp hv).2.1, (mem_filter.mp hv).2.2.1⟩)
    (by intro u _ v _ he; exact Fin.ext he)
  simpa [layerService] using h

namespace ForcingTrace
variable {work a b W s e : ℕ} {S : Fin work → ℕ}

theorem execution_lower (h : ForcingTrace S a b W s e) :
    ∀ v : Fin work, s ≤ v.val → e ≤ S v := by
  induction h with
  | done e => intro v hv; have := v.isLt; omega
  | layer s d e t hsd hd het hwidth hnarrow htimes tail ih =>
    intro v hv
    by_cases hvd : v.val < d
    · exact (htimes v hv hvd).1
    · have ht := ih v (by omega)
      omega

theorem service_zero (h : ForcingTrace S a b W s e) (hb : b ≤ e) : suffixService S a b s = 0 := by
  unfold suffixService
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hh := (mem_filter.mp hv).2
  have ht := h.execution_lower v hh.1
  omega

/-- Initial service is charged to at most one frontier of width `W`;
all later service is charged to distinct sequential slots. -/
theorem service_bounds (h : ForcingTrace S a b W s e) :
    suffixService S a b s ≤ W + (b - a) ∧
      (a < e → suffixService S a b s ≤ b - e) := by
  induction h with
  | done e =>
    have hz : suffixService S a b work = 0 := by
      unfold suffixService
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have := (mem_filter.mp hv).2.1
      have := v.isLt
      omega
    rw [hz]
    omega
  | layer s d e t hsd hd het hwidth hnarrow htimes tail ih =>
    have hsplit := suffixService_split S a b s d hsd.le
    have hhead := layerService_le_width S a b s d
    constructor
    · by_cases ht : t < a
      · have hz : layerService S a b s d = 0 := by
          unfold layerService
          apply card_eq_zero.mpr
          apply eq_empty_iff_forall_notMem.mpr
          intro v hv
          have hh := (mem_filter.mp hv).2
          have htime := (htimes v hh.1 hh.2.1).2
          omega
        omega
      · have htail := ih.2 (by omega)
        omega
    · intro hae
      by_cases hbe : b ≤ e
      · have hz := (ForcingTrace.layer s d e t hsd hd het hwidth hnarrow htimes tail).service_zero hbe
        rw [hz]
        omega
      · have hn := hnarrow hae (by omega)
        have htail := ih.2 (by omega)
        omega

end ForcingTrace
end Scheduling
