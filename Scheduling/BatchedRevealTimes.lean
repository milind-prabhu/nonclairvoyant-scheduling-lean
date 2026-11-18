import Scheduling.BatchedRecordCredit

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

namespace LayeredPrefix
variable {jobs work m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}

theorem RecordedRun.nodup {rule : LayerSizeRule jobs work}
    {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) : records.Nodup := by
  apply h.ordered_intervals.imp_of_mem
  intro r s hr _ horder he
  subst s
  have ht := h.final_times r hr
  have hh := horder rfl
  omega

end LayeredPrefix

namespace BatchedAdversary
open LayeredPrefix
variable {jobs m L : ℕ}

def CertifiedReveals (m L : ℕ) (records : List (LayerRecord jobs (m * L)))
    (S : Assignment (vertices := jobs * (m * L))) (E : LayerRecord jobs (m * L) → ℕ) : Prop :=
  ∀ before r after, records = before ++ r :: after → RecordCredit m L before r S (E r)

theorem CertifiedReveals.layer_after {records : List (LayerRecord jobs (m * L))}
    {S : Assignment (vertices := jobs * (m * L))} {E : LayerRecord jobs (m * L) → ℕ}
    (h : CertifiedReveals m L records S E) (r : LayerRecord jobs (m * L)) (hr : r ∈ records)
    (v : Fin (jobs * (m * L))) (ho : LayeredForest.job v = r.owner)
    (hlo : r.start ≤ (LayeredForest.position v).val) (hhi : (LayeredForest.position v).val < r.stop) :
    E r ≤ S v := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp hr
  exact (h before r after he).layer_after v ho hlo hhi

/-- One fixed reveal time for each actual layer. The certificate is
valid at its unique position in the chronological record list. -/
theorem exists_record_reveal_times (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records) :
    ∃ E : LayerRecord jobs (m * L) → ℕ,
      CertifiedReveals m L records (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) E := by
  obtain ⟨staticRule, hr⟩ := h.flexible.recorded
  have hn := hr.nodup
  have hex : ∀ r : LayerRecord jobs (m * L), ∃ e,
      ∀ before after, records = before ++ r :: after →
        RecordCredit m L before r (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) e := by
    intro r
    by_cases hmemb : r ∈ records
    · obtain ⟨before, after, heq⟩ := List.mem_iff_append.mp hmemb
      obtain ⟨e, hc⟩ := initial_record_credit hm hL heven A h before r after heq
      refine ⟨e, ?_⟩
      intro before' after' heq'
      have hn' : (before ++ r :: after).Nodup := heq ▸ hn
      have hparts := List.nodup_append'.mp hn'
      have hnb : r ∉ before := fun hh => hparts.2.2 hh List.mem_cons_self
      have hna : r ∉ after := (List.nodup_cons.mp hparts.2.1).1
      have he := (List.append_cons_inj_of_notMem hnb hna).mp (heq.symm.trans heq')
      simpa only [← he.1] using hc
    · refine ⟨0, ?_⟩
      intro before after heq
      exact False.elim (hmemb (heq ▸ List.mem_append_right before List.mem_cons_self))
  choose E hE using hex
  exact ⟨E, fun before r after he => hE r before after he⟩

end BatchedAdversary
end Scheduling
