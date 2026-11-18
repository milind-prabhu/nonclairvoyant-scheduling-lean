import Scheduling.JobLayers

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

def inForcingWindow (c L j t : ℕ) : Prop :=
  firstForcingTime c L j ≤ t ∧ t < firstForcingTime c L j + L / 2

noncomputable def narrowEvents {jobs work : ℕ} (c L j : ℕ)
    (rs : List (LayerRecord jobs work)) : ℕ :=
  (rs.filter (fun r => inForcingWindow c L j (r.time + 1))).length

/-- The distinct times at which narrow layers are requested lie in a
single half-epoch. Counting requests also counts a harmless possible
request after the job's final layer. -/
theorem narrowEvents_le {jobs work c L j : ℕ} {rs : List (LayerRecord jobs work)}
    (h : rs.Pairwise (fun a b => a.time < b.time)) : narrowEvents c L j rs ≤ L / 2 := by
  classical
  let selected := rs.filter (fun r => inForcingWindow c L j (r.time + 1))
  let times := selected.map (fun r => r.time + 1)
  have hp : times.Pairwise (fun a b => a < b) := by
    rw [List.pairwise_map]
    exact (h.filter _).imp (by intro a b hab; omega)
  have hn : times.Nodup := hp.imp (by intro a b hab; omega)
  have hsub : times.toFinset ⊆ Ico (firstForcingTime c L j) (firstForcingTime c L j + L / 2) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    have hwin := of_decide_eq_true (List.mem_filter.mp hr).2
    exact mem_Ico.mpr hwin
  have hc := card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at hc
  simpa [times, selected, narrowEvents] using hc

namespace JobLayers
variable {jobs work m c L : ℕ} {hm : 0 < m} {j : Fin jobs}

/-- Charge every full wide layer `2m` units of work. A narrow-layer
request pays for one extra layer, and one partial final layer is allowed. -/
theorem forcing_budget {a w : ℕ} {rs : List (LayerRecord jobs work)}
    (h : JobLayers (forcingLayerRule jobs work m c L hm) j a w rs)
    (narrow : Bool)
    (hwidth : w = min (work - a) (if narrow then 1 else 2 * m)) :
    2 * m * rs.length + a + 1 ≤
      work + 2 * m * (1 + (if narrow then 1 else 0) + narrowEvents c L j.val rs) := by
  induction h generalizing narrow with
  | done =>
    simp only [List.length_nil, Nat.mul_zero, narrowEvents, List.filter_nil, Nat.add_zero]
    split_ifs <;> nlinarith
  | step a w r rs ho ha hb hp hf tail ih =>
    by_cases hempty : rs = []
    · subst rs
      have haw : a < work := by omega
      simp only [List.length_cons, List.length_nil]
      have hn : 0 ≤ narrowEvents c L j.val [r] := Nat.zero_le _
      have hh : 1 ≤ 1 + (if narrow then 1 else 0) + narrowEvents c L j.val [r] := by omega
      have hm' := Nat.mul_le_mul_left (2 * m) hh
      nlinarith
    · have hrem : r.stop < work := tail.nonempty_iff.mp hempty
      let next : Bool := decide (inForcingWindow c L j.val (r.time + 1))
      have hwNext : (forcingLayerRule jobs work m c L hm).size j r.stop (r.time + 1) =
          min (work - r.stop) (if next then 1 else 2 * m) := by
        dsimp only [forcingLayerRule]
        by_cases hwin : inForcingWindow c L j.val (r.time + 1)
        · have hn : next = true := decide_eq_true hwin
          have hh : firstForcingTime c L j.val ≤ r.time + 1 ∧
              r.time + 1 < firstForcingTime c L j.val + L / 2 := hwin
          rw [if_pos hh, hn]
          rfl
        · have hn : next = false := decide_eq_false hwin
          have hh : ¬ (firstForcingTime c L j.val ≤ r.time + 1 ∧
              r.time + 1 < firstForcingTime c L j.val + L / 2) := hwin
          rw [if_neg hh, hn]
          rfl
      have hi := ih next hwNext
      have hwExact : w = if narrow then 1 else 2 * m := by
        have : w < work - a := by omega
        omega
      have hcount : narrowEvents c L j.val (r :: rs) =
          (if next then 1 else 0) + narrowEvents c L j.val rs := by
        simp only [narrowEvents, List.filter_cons, next]
        split_ifs <;> simp [Nat.add_comm]
      simp only [List.length_cons, hcount]
      rw [hb] at hi
      cases narrow <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hwExact ⊢ <;>
        nlinarith

/-- The adversary's job has at most `L` layers: at most `L/2` wide or
final partial layers, plus at most `L/2` narrow-layer requests. -/
theorem forcing_length_le {rs : List (LayerRecord jobs work)}
    (h : JobLayers (forcingLayerRule jobs work m c L hm) j 0 (min (2 * m) work) rs)
    (hw : work = m * L) (hhalf : 2 * (L / 2) = L)
    (htimes : rs.Pairwise (fun a b => a.time < b.time)) : rs.length ≤ L := by
  have hb := h.forcing_budget false (by simp [Nat.min_comm])
  have hn := narrowEvents_le (c := c) (L := L) (j := j.val) htimes
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hb
  have hscale := Nat.mul_le_mul_left (2 * m) hn
  have hm0 : 0 < 2 * m := by omega
  have hwork : 2 * m * (L / 2) = work := by rw [hw]; nlinarith
  have hbound : rs.length ≤ L / 2 + narrowEvents c L j.val rs := by
    by_contra hnot
    have hge := Nat.mul_le_mul_left (2 * m)
      (show L / 2 + narrowEvents c L j.val rs + 1 ≤ rs.length by omega)
    nlinarith
  omega

end JobLayers

namespace LayeredPrefix
variable {jobs work m c L : ℕ} {hm : 0 < m} {hwpos : 0 < work}
  {A : DeterministicScheduler m} {Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}

theorem RecordedRun.forcing_layer_count
    (h : RecordedRun (L := L) hwpos A (forcingLayerRule jobs work m c L hm)
      (initial m hm) Q records)
    (hw : work = m * L) (hhalf : 2 * (L / 2) = L) (j : Fin jobs) :
    (records.filter (fun r => r.owner = j)).length ≤ L :=
  (h.job_layers j).forcing_length_le hw hhalf (h.job_times_pairwise j)

end LayeredPrefix
end Scheduling
