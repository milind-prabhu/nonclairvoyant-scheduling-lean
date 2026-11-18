import Scheduling.AdversaryForcing

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

theorem job_interval_card {jobs work : ℕ} (S : Assignment (vertices := jobs * work))
    (j : Fin jobs) (a b : ℕ) :
    (univ.filter (fun v => job v = j ∧ a ≤ S v ∧ S v < b)).card =
      (univ.filter (fun v : Fin work => a ≤ S (finProdFinEquiv (j, v)) ∧
        S (finProdFinEquiv (j, v)) < b)).card := by
  classical
  let R := univ.filter (fun v : Fin work => a ≤ S (finProdFinEquiv (j, v)) ∧ S (finProdFinEquiv (j, v)) < b)
  have he : univ.filter (fun v => job v = j ∧ a ≤ S v ∧ S v < b) =
      R.image (fun v => finProdFinEquiv (j, v)) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨ho, ht⟩
      have hv : finProdFinEquiv (j, position v) = v := by
        rw [← ho]; exact finProdFinEquiv.apply_symm_apply v
      exact ⟨position v, by simpa only [R, mem_filter, mem_univ, true_and, hv] using ht, hv⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨LayeredForest.job_pair _ _, (mem_filter.mp hu).2⟩
  rw [he, card_image_of_injective]
  intro u v huv
  exact congrArg Prod.snd (finProdFinEquiv.injective huv)

namespace LayeredPrefix
variable {jobs work m c L : ℕ} {hm : 0 < m} {hwpos : 0 < work}
  {A : DeterministicScheduler m} {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}

theorem RecordedRun.forcing_interval_work
    (h : RecordedRun (L := L) hwpos A (forcingLayerRule jobs work m c L hm) (initial m hm) Q records)
    (hc : 0 < c) (hL : 0 < L)
    (hflow : (Q.toInstance L hwpos).FlowBound (A.schedule (Q.toInstance L hwpos)) (c * L)) (k : ℕ) :
    (univ.filter (fun v => (c * k) * L ≤ A.schedule (Q.toInstance L hwpos) v ∧
      A.schedule (Q.toInstance L hwpos) v < (c * k) * L + L / 2)).card ≤
      ((Q.toInstance L hwpos).alive (A.schedule (Q.toInstance L hwpos)) ((c * k) * L)).card * (2 * m + L / 2) := by
  let I := Q.toInstance L hwpos
  let S := A.schedule I
  let a := (c * k) * L
  let R := univ.filter (fun v : Fin (jobs * work) => a ≤ S v ∧ S v < a + L / 2)
  have hf : ∀ v ∈ R, job v ∈ I.alive S a := by
    intro v hv
    have ht := (mem_filter.mp hv).2
    have hhalf : L / 2 ≤ L := Nat.div_le_self _ _
    have hr := I.regular_epoch_no_arrivals (A.valid I) hL (by intros; rfl) v
      (show S v < (c * k + 1) * L by dsimp [a] at ht; nlinarith)
    exact mem_filter.mpr ⟨mem_univ _, hr, v, rfl, ht.1⟩
  have he := card_eq_sum_card_fiberwise hf
  change R.card ≤ (I.alive S a).card * (2 * m + L / 2)
  rw [he]
  calc
    _ ≤ ∑ _j ∈ I.alive S a, (2 * m + L / 2) := by
      apply sum_le_sum
      intro j hj
      have hstart := I.alive_firstForcingTime hc hL (by intros; rfl) hflow j hj
      have harrive : j.val * L ≤ a := (mem_filter.mp hj).2.1
      have hset : R.filter (fun v => job v = j) =
          univ.filter (fun v => job v = j ∧ a ≤ S v ∧ S v < a + L / 2) := by
        ext v; simp only [R, mem_filter, mem_univ, true_and]; tauto
      rw [hset, job_interval_card]
      exact h.local_forcing_work j a hstart harrive
    _ = _ := by simp

theorem RecordedRun.forcing_epoch_deficit
    (h : RecordedRun (L := L) hwpos A (forcingLayerRule jobs work m c L hm) (initial m hm) Q records)
    (hc : 0 < c) (hL : 0 < L) (hhalf : 2 * (L / 2) = L)
    (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (hflow : (Q.toInstance L hwpos).FlowBound (A.schedule (Q.toInstance L hwpos)) (c * L)) (k : ℕ) :
    (Q.toInstance L hwpos).epochWork (A.schedule (Q.toInstance L hwpos)) L (c * k) < m * L := by
  let I := Q.toInstance L hwpos
  let S := A.schedule I
  let a := (c * k) * L
  have hwork := h.forcing_interval_work hc hL hflow k
  have halive := I.regular_alive_card_le hL (by intros; rfl) hflow (c * k)
  have hscaled : 2 * (univ.filter (fun v => a ≤ S v ∧ S v < a + L / 2)).card ≤
      (I.alive S a).card * (4 * m + L) := by
    have hh := Nat.mul_le_mul_left 2 hwork
    change 2 * (univ.filter (fun v => a ≤ S v ∧ S v < a + L / 2)).card ≤
      2 * ((I.alive S a).card * (2 * m + L / 2)) at hh
    nlinarith
  have hgap := Accounting.forcing_capacity_gap hm hL halive hcL hcm hscaled
  have hdeficit : (univ.filter (fun v => a ≤ S v ∧ S v < a + L / 2)).card < m * (a + L / 2 - a) := by
    rw [Nat.add_sub_cancel_left]
    nlinarith
  obtain ⟨t, ht, hidle⟩ := I.interval_deficit_has_idle (A.valid I) hdeficit
  apply I.epochWork_lt_of_idle (A.valid I) hL (t := t) _ hidle
  have ht' := mem_Ico.mp ht
  have hhalf_le : L / 2 ≤ L := Nat.div_le_self _ _
  apply mem_Ico.mpr
  refine ⟨ht'.1, ?_⟩
  dsimp [a] at ht' ⊢
  nlinarith

theorem RecordedRun.flow_lower
    (h : RecordedRun (L := L) hwpos A (forcingLayerRule jobs work m c L hm) (initial m hm) Q records)
    (hc : 0 < c) (hL : 0 < L) (hhalf : 2 * (L / 2) = L)
    (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (hn : jobs = c * (c * (m * L))) (hw : work = m * L) :
    c * L ≤ (Q.toInstance L hwpos).maxFlow (A.schedule (Q.toInstance L hwpos)) := by
  let I := Q.toInstance L hwpos
  let S := A.schedule I
  by_contra hnflow
  change ¬ c * L ≤ I.maxFlow S at hnflow
  have hflow : I.FlowBound S (c * L) := (I.flowBound_iff_maxFlow_le S _).mpr (by omega)
  have hbound := I.regular_forcing_flow_lower hm hL hc hn (A.valid I) (by intros; rfl)
    (by intro j; exact (Q.jobVertices_card L hwpos j).trans hw)
    (by intro k _; exact h.forcing_epoch_deficit hc hL hhalf hcL hcm hflow k)
  exact hnflow hbound

end LayeredPrefix

/-- Deterministic part of Theorem 1, with explicit parameters and finite
instance size. There are no adversarial trace or offline schedule hypotheses. -/
theorem deterministic_lower_bound {m c L : ℕ} (hm : 2 ≤ m) (hc : 0 < c) (hL : 0 < L)
    (hhalf : 2 * (L / 2) = L) (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (A : DeterministicScheduler m) :
    ∃ I : Instance (c * (c * (m * L))) ((c * (c * (m * L))) * (m * L)),
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      L ≤ I.optimum m (by omega) ∧ I.optimum m (by omega) ≤ 2 * L ∧
      c * L ≤ I.maxFlow (A.schedule I) := by
  have hm0 : 0 < m := by omega
  have hw : 0 < m * L := Nat.mul_pos hm0 hL
  obtain ⟨Q, records, hrun, _, hforest⟩ := LayeredPrefix.exists_recorded_forcing_forest
    (jobs := c * (c * (m * L))) (work := m * L) (L := L) (c := c) hm0 hw A
  have hj : 0 < c * (c * (m * L)) := Nat.mul_pos hc (Nat.mul_pos hc hw)
  have ho := hrun.optimum_bounds hm hj rfl hhalf
  exact ⟨Q.toInstance L hw, hforest, ho.1, ho.2, hrun.flow_lower hc hL hhalf hcL hcm rfl rfl⟩

/-- An explicit absolute constant in the deterministic
`Ω(min(m, OPT))` lower bound. The scale `L` may be any positive multiple
of sixteen, so the instances exist at arbitrarily large flow scales. -/
theorem deterministic_competitive_lower {m L : ℕ} (hm : 2 ≤ m)
    (hL : 16 ≤ L) (hdiv : 16 ∣ L) (A : DeterministicScheduler m) :
    ∃ jobs vertices, ∃ I : Instance jobs vertices,
      (∀ u v w, I.edge u w → I.edge v w → u = v) ∧
      L ≤ I.optimum m (by omega) ∧ I.optimum m (by omega) ≤ 2 * L ∧
      min m (I.optimum m (by omega)) * I.optimum m (by omega) ≤ 64 * I.maxFlow (A.schedule I) := by
  let c := min (m / 2) (L / 16)
  have hc : 0 < c := by dsimp [c]; omega
  have hcL : 16 * c ≤ L := by dsimp [c]; omega
  have hcm : 2 * c ≤ m := by dsimp [c]; omega
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hhalf : 2 * (L / 2) = L := by omega
  obtain ⟨I, hforest, hlo, hhi, hflow⟩ := deterministic_lower_bound hm hc (by omega) hhalf hcL hcm A
  refine ⟨_, _, I, hforest, hlo, hhi, ?_⟩
  have hmin : min m (I.optimum m (by omega)) ≤ 32 * c := by
    by_cases hh : m / 2 ≤ L / 16
    · have he : c = m / 2 := min_eq_left hh
      omega
    · have he : c = L / 16 := min_eq_right (by omega)
      omega
  have h₁ := Nat.mul_le_mul_right (I.optimum m (by omega)) hmin
  have h₂ := Nat.mul_le_mul_left c hhi
  nlinarith

end Scheduling
