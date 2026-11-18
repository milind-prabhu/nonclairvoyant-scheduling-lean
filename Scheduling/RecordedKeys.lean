import Scheduling.AdversaryOffline

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

theorem recordedKeys_append {jobs work : ℕ} (a b : List (LayerRecord jobs work)) (j : Fin jobs) :
    recordedKeys (a ++ b) j = recordedKeys a j ∪ recordedKeys b j := by
  simp [recordedKeys, List.filter_append, image_union]

theorem recordedKeys_prefix_le {jobs work p : ℕ} (a b : List (LayerRecord jobs work)) (j : Fin jobs)
    (hb : ∀ k ∈ recordedKeys b j, p ≤ k.val) :
    ((recordedKeys (a ++ b) j).filter (fun k => k.val < p)).card ≤
      (a.filter (fun r => r.owner = j)).length := by
  have hs : (recordedKeys (a ++ b) j).filter (fun k => k.val < p) ⊆ recordedKeys a j := by
    intro k hk
    obtain ⟨hk, hlt⟩ := mem_filter.mp hk
    rw [recordedKeys_append] at hk
    rcases mem_union.mp hk with h | h
    · exact h
    · have hh := hb k h
      omega
  exact (card_le_card hs).trans (recordedKeys_card_le a j)

namespace LayeredPrefix
variable {jobs work m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
variable {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work}
variable {records : List (LayerRecord jobs work)}

theorem RecordedRun.keys_lower (h : RecordedRun (L := L) hw A rule P Q records)
    (j : Fin jobs) (k : Fin work) (hk : k ∈ recordedKeys records j) : P.closed j ≤ k.val := by
  obtain ⟨r, hr, hkey⟩ := mem_image.mp hk
  obtain ⟨hr, ho⟩ := List.mem_filter.mp (List.mem_toFinset.mp hr)
  have ho' : r.owner = j := of_decide_eq_true ho
  have hs := h.start_lower r hr
  have ht := (h.final_times r hr).1
  rw [ho'] at hs
  rw [hkey] at ht
  omega

theorem RecordedRun.keys_card (h : RecordedRun (L := L) hw A rule P Q records) (j : Fin jobs) :
    (recordedKeys records j).card = (records.filter (fun r => r.owner = j)).length := by
  let rs := records.filter (fun r => r.owner = j)
  have hpair : rs.Pairwise (fun a b => a.key < b.key) := by
    have hp := h.ordered_intervals.filter (fun r => r.owner = j)
    apply hp.imp_of_mem
    intro a b ha hb hab
    obtain ⟨ha', hoa⟩ := List.mem_filter.mp ha
    obtain ⟨hb', hob⟩ := List.mem_filter.mp hb
    have hoa' : a.owner = j := of_decide_eq_true hoa
    have hob' : b.owner = j := of_decide_eq_true hob
    have hstop := hab (hoa'.trans hob'.symm)
    have hka := (h.final_times a ha').2.1
    have hkb := (h.final_times b hb').1
    change a.key.val < b.key.val
    omega
  have hn : (rs.map LayerRecord.key).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hpair.imp (fun h => ne_of_lt h)
  change (rs.toFinset.image LayerRecord.key).card = rs.length
  have he : rs.toFinset.image LayerRecord.key = (rs.map LayerRecord.key).toFinset := by
    ext k
    simp
  rw [he, List.toFinset_card_of_nodup hn, List.length_map]

end LayeredPrefix
end Scheduling
