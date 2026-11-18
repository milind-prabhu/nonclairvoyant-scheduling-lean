import Scheduling.LayerRecords

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

/-- A job's recorded layers tile its remaining vertex interval. The next
width is exactly the adversary's rule evaluated at the previous layer's
closing time plus one. -/
inductive JobLayers {jobs work : ℕ} (rule : LayerSizeRule jobs work) (j : Fin jobs) :
    ℕ → ℕ → List (LayerRecord jobs work) → Prop
  | done : JobLayers rule j work 0 []
  | step (a w : ℕ) (r : LayerRecord jobs work) (rs : List (LayerRecord jobs work))
      (ho : r.owner = j) (ha : r.start = a) (hb : r.stop = a + w)
      (hp : 0 < w) (hf : r.stop ≤ work)
      (tail : JobLayers rule j r.stop (rule.size j r.stop (r.time + 1)) rs) :
      JobLayers rule j a w (r :: rs)

namespace LayeredPrefix
variable {jobs work : ℕ}

theorem RecordedRun.job_layers {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ j, JobLayers rule j (P.closed j) (P.width j) (records.filter (fun r => r.owner = j)) := by
  induction h with
  | done P hd =>
    intro j
    have hz : P.width j = 0 := by have := P.fits j; rw [hd] at this; omega
    rw [hd, hz]
    exact JobLayers.done
  | step P Q j key hk hmax hearliest records tail ih =>
    intro i
    by_cases he : i = j
    · subst i
      simp only [List.filter_cons, record, decide_true, ite_true]
      refine JobLayers.step (rule := rule) (j := j) (P.closed j) (P.width j)
        (P.record (L := L) hw A j key) _ rfl rfl rfl ?_ ?_ ?_
      · dsimp [boundary] at hk; omega
      · exact P.fits j
      · simpa [advance, record] using ih j
    · have hne : j ≠ i := Ne.symm he
      simp only [List.filter_cons, record, hne, decide_false, Bool.false_eq_true, ite_false]
      simpa only [advance, if_neg he] using ih i

/-- A fixed out-forest and its complete layer trace exist for every
deterministic causal scheduler. This theorem uses the paper's actual
forcing-window size rule; the quantitative layer-count and forcing-window
analysis are separate obligations. -/
theorem exists_recorded_forcing_forest {m L c : ℕ} (hm : 0 < m) (hw : 0 < work)
    (A : DeterministicScheduler m) :
    ∃ Q : LayeredPrefix jobs work, ∃ records : List (LayerRecord jobs work),
      RecordedRun (L := L) hw A (forcingLayerRule jobs work m c L hm) (initial m hm) Q records ∧
      (∀ j, JobLayers (forcingLayerRule jobs work m c L hm) j 0 (min (2 * m) work)
        (records.filter (fun r => r.owner = j))) ∧
      (∀ u v w, (Q.toInstance L hw).edge u w → (Q.toInstance L hw).edge v w → u = v) := by
  obtain ⟨Q, hQ⟩ := (initial (jobs := jobs) (work := work) m hm).exists_completion (L := L) hw A
    (forcingLayerRule jobs work m c L hm)
  obtain ⟨records, hr⟩ := hQ.records
  exact ⟨Q, records, hr, hr.job_layers, fun _ _ _ hu hv => hQ.outForest hu hv⟩

end LayeredPrefix

namespace JobLayers
variable {jobs work : ℕ} {rule : LayerSizeRule jobs work} {j : Fin jobs}

theorem fits {a w : ℕ} {rs : List (LayerRecord jobs work)} (h : JobLayers rule j a w rs) :
    a + w ≤ work := by
  cases h with
  | done => omega
  | step a w r rs ho ha hb hp hf tail => omega

theorem nonempty_iff {a w : ℕ} {rs : List (LayerRecord jobs work)} (h : JobLayers rule j a w rs) :
    rs ≠ [] ↔ a < work := by
  cases h with
  | done => simp
  | step a w r rs ho ha hb hp hf tail => simp; omega

theorem total_size {a w : ℕ} {rs : List (LayerRecord jobs work)} (h : JobLayers rule j a w rs) :
    (rs.map (fun r => r.stop - r.start)).sum = work - a := by
  induction h with
  | done => simp
  | step a w r rs ho ha hb hp hf tail ih =>
    simp only [List.map_cons, List.sum_cons, ha, hb, Nat.add_sub_cancel_left]
    rw [ih]
    omega

theorem intervals {a w : ℕ} {rs : List (LayerRecord jobs work)} (h : JobLayers rule j a w rs) :
    ∀ r ∈ rs, r.owner = j ∧ a ≤ r.start ∧ r.start < r.stop ∧ r.stop ≤ work := by
  induction h with
  | done => simp
  | step a w r rs ho ha hb hp hf tail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨ho, by omega, by omega, hf⟩
    · have hh := ih s hs
      exact ⟨hh.1, by omega, hh.2.2⟩

theorem head_width {a w : ℕ} {r : LayerRecord jobs work} {rs : List (LayerRecord jobs work)}
    (h : JobLayers rule j a w (r :: rs)) : r.stop - r.start = w := by
  cases h with
  | step a w r rs ho ha hb hp hf tail => omega

theorem tail_rule {a w : ℕ} {r : LayerRecord jobs work} {rs : List (LayerRecord jobs work)}
    (h : JobLayers rule j a w (r :: rs)) :
    JobLayers rule j r.stop (rule.size j r.stop (r.time + 1)) rs := by
  cases h with
  | step a w r rs ho ha hb hp hf tail => exact tail

theorem head_endpoints {a w : ℕ} {r : LayerRecord jobs work} {rs : List (LayerRecord jobs work)}
    (h : JobLayers rule j a w (r :: rs)) : r.start = a ∧ r.stop = a + w := by
  cases h with
  | step a w r rs ho ha hb hp hf tail => exact ⟨ha, hb⟩

theorem times_pairwise {a w : ℕ} {rs : List (LayerRecord jobs work)}
    (h : JobLayers rule j a w rs)
    (hstep : ∀ r ∈ rs, ∀ s ∈ rs, s.start = r.stop →
      s.stop = r.stop + rule.size j r.stop (r.time + 1) → r.time < s.time) :
    rs.Pairwise (fun r s => r.time < s.time) := by
  induction h with
  | done => exact List.Pairwise.nil
  | step a w r rs ho ha hb hp hf tail ih =>
    have hsub : ∀ s ∈ rs, ∀ u ∈ rs, u.start = s.stop →
        u.stop = s.stop + rule.size j s.stop (s.time + 1) → s.time < u.time := by
      intro s hs u hu
      exact hstep s (List.mem_cons_of_mem _ hs) u (List.mem_cons_of_mem _ hu)
    have hi := ih hsub
    rw [List.pairwise_cons]
    refine ⟨?_, hi⟩
    intro s hs
    cases rs with
    | nil => simp at hs
    | cons first rest =>
      have hbounds : first.start = r.stop ∧
          first.stop = r.stop + rule.size j r.stop (r.time + 1) := tail.head_endpoints
      have hfirst := hstep r List.mem_cons_self first (List.mem_cons_of_mem _ List.mem_cons_self)
        hbounds.1 hbounds.2
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hfirst
      · exact hfirst.trans ((List.pairwise_cons.mp hi).1 s hs)

end JobLayers

namespace LayeredPrefix
variable {jobs work : ℕ}

/-- Distinct layers of one job close at strictly increasing times in the
final schedule. This supplies the injection used to count narrow layers
inside a bounded forcing interval. -/
theorem RecordedRun.job_times_pairwise {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) (j : Fin jobs) :
    (records.filter (fun r => r.owner = j)).Pairwise (fun r s => r.time < s.time) := by
  apply (h.job_layers j).times_pairwise
  intro r hr s hs hstart hstop
  have hrmem := (List.mem_filter.mp hr).1
  have hsmem := (List.mem_filter.mp hs).1
  have hro : r.owner = j := of_decide_eq_true (List.mem_filter.mp hr).2
  have hso : s.owner = j := of_decide_eq_true (List.mem_filter.mp hs).2
  have hrf := h.final_times r hrmem
  have hsf := h.final_times s hsmem
  have hp := h.next_parents r hrmem s.key (by omega) (by rw [hro]; omega)
  have hedge : (Q.toInstance L hw).edge (finProdFinEquiv (r.owner, r.key))
      (finProdFinEquiv (s.owner, s.key)) := by
    constructor
    · simpa only [LayeredForest.job_pair] using hro.trans hso.symm
    · have hvis : s.key.val < Q.boundary s.owner := by
        have := s.key.isLt
        simp only [boundary, h.completion.finished]
        omega
      simp only [LayeredForest.job_pair, LayeredForest.position_pair]
      rw [if_pos hvis]
      simpa only [hro, hso] using hp
  have ht := (A.valid (Q.toInstance L hw)).precedence hedge
  rw [hrf.2.2.2.1, hsf.2.2.2.1] at ht
  exact ht

end LayeredPrefix
end Scheduling
