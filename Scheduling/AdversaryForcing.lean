import Scheduling.AdversaryOffline
import Scheduling.ForcingTrace
import Scheduling.RegularBacklog

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

namespace LayeredPrefix
variable {jobs work m c L : ℕ} {hm : 0 < m} {hw : 0 < work}
  {A : DeterministicScheduler m} {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}

/-- The local forcing trace is supplied by the constructed instance's
actual parents, final key times, and layer-size rule. -/
theorem RecordedRun.forcing_trace
    (h : RecordedRun (L := L) hw A (forcingLayerRule jobs work m c L hm) (initial m hm) Q records)
    (j : Fin jobs) (a : ℕ) (hstart : firstForcingTime c L j.val = a) (harrive : j.val * L ≤ a) :
    ForcingTrace (fun v => A.schedule (Q.toInstance L hw) (finProdFinEquiv (j, v)))
      a (a + L / 2) (2 * m) 0 (j.val * L) := by
  let I := Q.toInstance L hw
  let S := fun v : Fin work => A.schedule I (finProdFinEquiv (j, v))
  let rule := forcingLayerRule jobs work m c L hm
  have aux : ∀ s w rs, JobLayers rule j s w rs →
      (∀ r ∈ rs, r ∈ records) → ∀ e,
      (∀ v : Fin work, s ≤ v.val → v.val < s + w → e ≤ S v) →
      w ≤ 2 * m → (a < e → e < a + L / 2 → w ≤ 1) →
      ForcingTrace S a (a + L / 2) (2 * m) s e := by
    intro s w rs hl
    induction hl with
    | done => intro _ e _ _ _; exact ForcingTrace.done e
    | step s w r rs ho ha hb hp hf tail ih =>
      intro hsub e hready hwide hnarrow
      have hr := hsub r List.mem_cons_self
      have hfinal := h.final_times r hr
      have hkeylo : s ≤ r.key.val := by omega
      have hkeyhi : r.key.val < s + w := by omega
      have hkeyTime : S r.key = r.time := by
        simpa only [S, I, ho] using hfinal.2.2.2.1
      have het : e ≤ r.time := by rw [← hkeyTime]; exact hready r.key hkeylo hkeyhi
      apply ForcingTrace.layer s (s + w) e r.time (by omega) (by omega) het (by omega) (by intros; omega)
      · intro v hvlo hvhi
        refine ⟨hready v hvlo hvhi, ?_⟩
        have ht := hfinal.2.2.2.2 (finProdFinEquiv (j, v))
          (by simpa only [LayeredForest.job_pair] using ho.symm)
          (by simp only [LayeredForest.position_pair]; omega)
          (by simp only [LayeredForest.position_pair]; omega)
        exact ht
      · rw [← hb]
        apply ih (by intro u hu; exact hsub u (List.mem_cons_of_mem _ hu)) (r.time + 1)
        · intro v hvlo hvhi
          have hparent := h.next_parents r hr v hvlo (by rwa [ho])
          have hvisible : v.val < Q.boundary j := by
            have := v.isLt
            simp only [boundary, h.completion.finished]
            omega
          have hedge : I.edge (finProdFinEquiv (r.owner, r.key)) (finProdFinEquiv (j, v)) := by
            constructor
            · simpa only [LayeredForest.job_pair] using ho
            · simp only [LayeredForest.job_pair, LayeredForest.position_pair]
              rw [if_pos hvisible]
              simpa only [ho] using hparent
          have htime := (A.valid I).precedence hedge
          have hk : A.schedule I (finProdFinEquiv (r.owner, r.key)) = r.time := hfinal.2.2.2.1
          change r.time + 1 ≤ A.schedule I (finProdFinEquiv (j, v))
          omega
        · dsimp only [rule, forcingLayerRule]
          split_ifs
          · exact (min_le_right _ _).trans (by omega)
          · exact min_le_right _ _
        · intro hae heb
          have hwin : firstForcingTime c L j.val ≤ r.time + 1 ∧
              r.time + 1 < firstForcingTime c L j.val + L / 2 := by rw [hstart]; omega
          dsimp only [rule, forcingLayerRule]
          rw [if_pos hwin]
          exact min_le_right _ _
  apply aux 0 (min (2 * m) work) (records.filter (fun r => r.owner = j)) (h.job_layers j)
    (by intro r hr; exact (List.mem_filter.mp hr).1) (j.val * L)
  · intro v _ _
    simpa only [S, I, toInstance, LayeredForest.job_pair] using (A.valid I).release (finProdFinEquiv (j, v))
  · exact min_le_left _ _
  · intros; omega

theorem RecordedRun.local_forcing_work
    (h : RecordedRun (L := L) hw A (forcingLayerRule jobs work m c L hm) (initial m hm) Q records)
    (j : Fin jobs) (a : ℕ) (hstart : firstForcingTime c L j.val = a) (harrive : j.val * L ≤ a) :
    (univ.filter (fun v : Fin work => a ≤ A.schedule (Q.toInstance L hw) (finProdFinEquiv (j, v)) ∧
      A.schedule (Q.toInstance L hw) (finProdFinEquiv (j, v)) < a + L / 2)).card ≤ 2 * m + L / 2 := by
  have hb := (h.forcing_trace j a hstart harrive).service_bounds.1
  simpa [suffixService] using hb

end LayeredPrefix

theorem firstForcingTime_eq {c L j k : ℕ} (hc : 0 < c)
    (hlo : c * k < j + c) (hhi : j ≤ c * k) : firstForcingTime c L j = (c * k) * L := by
  have hs : 0 < j + c := by omega
  have hsub : j + c - 1 + 1 = j + c := by omega
  have hlow : k * c ≤ j + c - 1 := by nlinarith
  have hhigh : j + c - 1 < (k + 1) * c := by nlinarith
  have hdiv : (j + c - 1) / c = k := by
    have h₁ := (Nat.le_div_iff_mul_le hc).mpr hlow
    have h₂ := (Nat.div_lt_iff_lt_mul hc).mpr hhigh
    omega
  unfold firstForcingTime
  rw [hdiv]
  ac_rfl

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

theorem alive_firstForcingTime {c L k : ℕ} {S : Assignment (vertices := vertices)}
    (hc : 0 < c) (hL : 0 < L) (hrelease : ∀ j, I.release j = j.val * L)
    (hflow : I.FlowBound S (c * L)) (j : Fin jobs) (hj : j ∈ I.alive S ((c * k) * L)) :
    firstForcingTime c L j.val = (c * k) * L := by
  obtain ⟨hr, v, ho, ht⟩ := (mem_filter.mp hj).2
  rw [hrelease] at hr
  have hf := hflow v
  rw [ho, hrelease] at hf
  apply firstForcingTime_eq hc
  · by_contra hn
    have := Nat.mul_le_mul_right L (show j.val + c ≤ c * k by omega)
    nlinarith
  · by_contra hn
    have := Nat.mul_le_mul_right L (show c * k + 1 ≤ j.val by omega)
    nlinarith

end Instance
end Scheduling
