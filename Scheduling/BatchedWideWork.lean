import Scheduling.BatchedHistory
import Scheduling.RegularBacklog

namespace Scheduling.LayeredPrefix
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}

theorem RecordedRun.record_time_injective {rule : LayerSizeRule jobs work}
    {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records)
    {r s : LayerRecord jobs work} (hr : r ∈ records) (hs : s ∈ records)
    (ho : r.owner = s.owner) (ht : r.time = s.time) : r = s := by
  let rs := records.filter (fun x => x.owner = r.owner)
  have hpair : rs.Pairwise (fun a b => a.time ≠ b.time) :=
    (h.job_times_pairwise r.owner).imp (fun h => ne_of_lt h)
  let : Std.Symm (fun a b : LayerRecord jobs work => a.time ≠ b.time) :=
    ⟨fun _ _ hh => Ne.symm hh⟩
  by_contra hne
  apply (hpair.forall (by simp [rs, hr]) (by simp [rs, hs, ho]) hne) ht

end Scheduling.LayeredPrefix

namespace Scheduling.BatchedAdversary
open Finset
open LayeredForest (job position)
open LayeredPrefix
attribute [local instance] Classical.propDecidable
variable {jobs m L : ℕ}

theorem nonwide_is_narrow_key (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records)
    (v : Fin (jobs * (m * L))) (hv : ¬ WideRecorded m records (job v) v) :
    ∃ r ∈ records, r.owner = job v ∧ r.stop - r.start = 1 ∧
      v = finProdFinEquiv (r.owner, r.key) := by
  obtain ⟨staticRule, hr⟩ := h.flexible.recorded
  obtain ⟨r, hmem, ho, hlo, hhi⟩ := hr.covers (job v) (position v) (by simp [initial])
  have hwidth := history_widths hm hL heven A h (initial_budget hm hL heven) r hmem
  have hn : r.stop - r.start = 1 := hwidth.resolve_left (by
    intro hw
    exact hv ⟨rfl, r, hmem, ho, hw, hlo, hhi⟩)
  have ht := hr.final_times r hmem
  have hkey : (position v).val = r.key.val := by omega
  refine ⟨r, hmem, ho, hn, ?_⟩
  apply LayeredForest.coordinates_injective
  simp only [LayeredForest.job_pair, LayeredForest.position_pair]
  exact Prod.ext ho.symm hkey

theorem nonwide_same_slot_injective (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records)
    {u v : Fin (jobs * (m * L))}
    (hu : ¬ WideRecorded m records (job u) u) (hv : ¬ WideRecorded m records (job v) v)
    (ho : job u = job v)
    (ht : A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)) u =
      A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)) v) : u = v := by
  obtain ⟨staticRule, hr⟩ := h.flexible.recorded
  obtain ⟨r, hr', hro, _, hu'⟩ := nonwide_is_narrow_key hm hL heven A h u hu
  obtain ⟨s, hs', hso, _, hv'⟩ := nonwide_is_narrow_key hm hL heven A h v hv
  have hrt := (hr.final_times r hr').2.2.2.1
  have hst := (hr.final_times s hs').2.2.2.1
  have he : r = s := hr.record_time_injective hr' hs' (hro.trans (ho.trans hso.symm)) (by
    rw [hu', hv', hrt, hst] at ht
    exact ht)
  rw [hu', hv', he]

theorem narrow_slot_le (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records)
    {c i t : ℕ}
    (hflow : (Q.toInstance L (Nat.mul_pos (by omega) hL)).FlowBound
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) (c * L))
    (ht : i * L ≤ t ∧ t < (i + 1) * L) :
    (univ.filter (fun v => ¬ WideRecorded m records (job v) v ∧
      A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)) v = t)).card ≤ c := by
  let I := Q.toInstance L (Nat.mul_pos (by omega) hL)
  let S := A.schedule I
  have hS := A.valid I
  have hc := card_le_card_of_injOn job
    (s := univ.filter (fun v => ¬ WideRecorded m records (job v) v ∧ S v = t))
    (t := I.alive S (i * L)) (by
      intro v hv
      have htime := (mem_filter.mp hv).2.2
      have hr := I.regular_epoch_no_arrivals (i := i) hS hL (by intros; rfl) v
        (show S v < (i + 1) * L from by omega)
      exact mem_filter.mpr ⟨mem_univ _, hr, v, rfl, by omega⟩) (by
      intro u hu v hv ho
      obtain ⟨hnu, htu⟩ := (mem_filter.mp hu).2
      obtain ⟨hnv, htv⟩ := (mem_filter.mp hv).2
      exact nonwide_same_slot_injective hm hL heven A h hnu hnv ho (htu.trans htv.symm))
  exact hc.trans (I.regular_alive_card_le hL (by intros; rfl) hflow i)

noncomputable def wideService {jobs work : ℕ} (m : ℕ) (records : List (LayerRecord jobs work))
    (S : Assignment (vertices := jobs * work)) (a b : ℕ) : ℕ :=
  (univ.filter (fun v => WideRecorded m records (job v) v ∧ a ≤ S v ∧ S v < b)).card

theorem wideService_eq_sum {jobs work : ℕ} (m : ℕ) (records : List (LayerRecord jobs work))
    (S : Assignment (vertices := jobs * work)) (a b : ℕ) :
    wideService m records S a b = ∑ t ∈ Ico a b,
      (univ.filter (fun v => WideRecorded m records (job v) v ∧ S v = t)).card := by
  unfold wideService
  rw [card_eq_sum_card_fiberwise (f := S) (fun v hv => mem_Ico.mpr (mem_filter.mp hv).2.2)]
  apply sum_congr rfl
  intro t ht
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hw, _⟩, htime⟩; exact ⟨hw, htime⟩
  · rintro ⟨hw, htime⟩
    exact ⟨⟨hw, by rw [htime]; exact mem_Ico.mp ht⟩, htime⟩

theorem full_epoch_wide_lower (hm : 2 ≤ m) (hL : 0 < L) (heven : 2 * (L / 2) = L)
    (A : DeterministicScheduler m) {records : List (LayerRecord jobs (m * L))}
    {Q : LayeredPrefix jobs (m * L)}
    (h : HistoryRun (Nat.mul_pos (by omega) hL) A L (rule jobs m L hm hL A) []
      (initial jobs m L hm) Q records)
    {c i a b : ℕ}
    (hflow : (Q.toInstance L (Nat.mul_pos (by omega) hL)).FlowBound
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) (c * L))
    (ha : i * L ≤ a) (hb : b ≤ (i + 1) * L)
    (hfull : ∀ t ∈ Ico a b,
      (univ.filter (fun v => A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL)) v = t)).card = m) :
    (m - c) * (b - a) ≤ wideService m records
      (A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))) a b := by
  let S := A.schedule (Q.toInstance L (Nat.mul_pos (by omega) hL))
  rw [wideService_eq_sum]
  have hs : ∀ t ∈ Ico a b,
      m - c ≤ (univ.filter (fun v => WideRecorded m records (job v) v ∧ S v = t)).card := by
    intro t ht
    have hn := narrow_slot_le hm hL heven A h hflow (i := i) (t := t)
      ⟨ha.trans (mem_Ico.mp ht).1, (mem_Ico.mp ht).2.trans_le hb⟩
    have hp := card_filter_add_card_filter_not (s := univ.filter (fun v => S v = t))
      (fun v => WideRecorded m records (job v) v)
    have hwide : (univ.filter (fun v => S v = t)).filter (fun v => WideRecorded m records (job v) v) =
        univ.filter (fun v => WideRecorded m records (job v) v ∧ S v = t) := by
      ext v; simp only [mem_filter, mem_univ, true_and]; tauto
    have hnarrow : (univ.filter (fun v => S v = t)).filter (fun v => ¬ WideRecorded m records (job v) v) =
        univ.filter (fun v => ¬ WideRecorded m records (job v) v ∧ S v = t) := by
      ext v; simp only [mem_filter, mem_univ, true_and]; tauto
    rw [hwide, hnarrow, hfull t ht] at hp
    change (univ.filter (fun v => ¬ WideRecorded m records (job v) v ∧ S v = t)).card ≤ c at hn
    omega
  have hh := sum_le_sum hs
  simpa only [sum_const, Nat.card_Ico, Nat.nsmul_eq_mul, Nat.mul_comm] using hh

end Scheduling.BatchedAdversary
