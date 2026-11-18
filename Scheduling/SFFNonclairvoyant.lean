import Scheduling.SFFHistory

namespace Scheduling
open Finset

/-- Batch and delay a raw ready observation using only public release times,
the supplied guess, and the current clock. -/
def batchObservation (L t : ℕ) (Q : FIFOObservation) : PublicSnapshot where
  support := (Q.filter (fun x => 2 * L * ((ofLex x).1 / (2 * L) + 1) ≤ t)).image
    (fun x => (ofLex x).1 / (2 * L))
  ready := fun b => ((Q.filter (fun x => 2 * L * ((ofLex x).1 / (2 * L) + 1) ≤ t)).filter
    (fun x => (ofLex x).1 / (2 * L) = b)).image (fun x => (ofLex x).2)
  supported := by
    intro b
    simp only [mem_image, image_nonempty, filter_nonempty_iff]

theorem mem_batchObservation (L t b n : ℕ) (Q : FIFOObservation) :
    n ∈ (batchObservation L t Q).ready b ↔
      ∃ x ∈ Q, (ofLex x).1 / (2 * L) = b ∧ 2 * L * (b + 1) ≤ t ∧ (ofLex x).2 = n := by
  simp only [batchObservation, mem_image, mem_filter]
  constructor
  · rintro ⟨x, ⟨⟨hx, he⟩, hb⟩, hn⟩
    exact ⟨x, hx, hb, by simpa [hb] using he, hn⟩
  · rintro ⟨x, hx, hb, he, hn⟩
    exact ⟨x, ⟨⟨hx, by simpa [hb] using he⟩, hb⟩, hn⟩

def sffRawPolicy (m L : ℕ) : OnlinePolicy FIFOObservation SFFMemory (Finset ℕ) where
  initial := none
  step := fun t Q state => sffStep m t (batchObservation L t Q) state

theorem sffRawPolicy_state (m L : ℕ) (history : ℕ → FIFOObservation) (t : ℕ) :
    (sffRawPolicy m L).state history t =
      (sffPolicy m).state (fun u => batchObservation L u (history u)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [OnlinePolicy.state]
    rw [ih]
    rfl

theorem sffRawPolicy_decision (m L : ℕ) (history : ℕ → FIFOObservation) (t : ℕ) :
    (sffRawPolicy m L).decision history t =
      (sffPolicy m).decision (fun u => batchObservation L u (history u)) t := by
  unfold OnlinePolicy.decision
  rw [sffRawPolicy_state]
  rfl

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices) [DecidableRel I.edge]

/-- All currently ready vertices, labeled by their release time and public
identifier. No future job or unrevealed vertex is present. -/
def readyObservation (S : Assignment (vertices := vertices)) (t : ℕ) : FIFOObservation :=
  (univ.filter (fun v => I.release (I.owner v) ≤ t ∧ t ≤ S v ∧
    ∀ u, I.edge u v → S u < t)).image I.fifoPriority

theorem mem_readyObservation (S : Assignment (vertices := vertices)) (t : ℕ) (x : ℕ ×ₗ ℕ) :
    x ∈ I.readyObservation S t ↔ ∃ v, I.Ready S t v ∧ I.fifoPriority v = x := by
  simp only [readyObservation, mem_image, mem_filter, mem_univ, true_and, Ready]

theorem fifo_readyObservation {m : ℕ} (hm : 0 < m) (t : ℕ) :
    I.readyObservation (I.fifoSchedule m hm) t = I.fifoObservation m t := by
  unfold readyObservation fifoObservation
  congr 1
  ext v
  simpa only [mem_filter, mem_univ, true_and, Ready] using (I.fifo_ready_iff hm v t).symm

theorem fifoSchedule_publicPolicy {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (univ.filter (fun v => I.fifoSchedule m hm v = t)).image Fin.val =
      fifoPolicy m (I.readyObservation (I.fifoSchedule m hm) t) := by
  rw [I.fifo_readyObservation hm, ← I.fifo_action_eq hm, I.fifoAction_public]

end Instance

namespace Batching
variable {jobs vertices batches L : ℕ} {I : Instance jobs vertices}
variable (B : Batching I L batches) [DecidableRel I.edge]

theorem observe_schedule_ready (S : Assignment (vertices := vertices)) (t : ℕ)
    (b : Fin batches) (v : Fin vertices) :
    v ∈ (B.observe ⟨t, fun u => if S u < t then some (S u) else none⟩).ready b ↔
      B.vertexBatch v = b ∧ B.eligible b ≤ t ∧ I.Ready S t v := by
  have hnone (u : Fin vertices) : (if S u < t then some (S u) else none) = none ↔ t ≤ S u := by
    split_ifs <;> simp_all
  have hdone (u : Fin vertices) : (if S u < t then some (S u) else none) ≠ none ↔ S u < t := by
    split_ifs <;> simp_all
  simp only [observe, mem_filter, mem_univ, true_and, hnone, hdone, Instance.Ready]
  constructor
  · rintro ⟨hb, he, hv, hp⟩
    have hr := B.released_by_eligible hb
    exact ⟨hb, he, by omega, hv, hp⟩
  · rintro ⟨hb, he, _, hv, hp⟩
    exact ⟨hb, he, hv, hp⟩

end Batching

namespace Instance
variable {jobs vertices : ℕ} (I : Instance jobs vertices) [DecidableRel I.edge]

/-- The SFF environment's admitted frontiers are computable from the raw
ready observation; the finite batch count does not add information. -/
theorem sff_publicHistory_eq (m L : ℕ) (hL : 0 < L) (t : ℕ) :
    (I.canonicalBatching L hL).publicHistory m t =
      batchObservation L t (I.readyObservation (I.sffSchedule m L hL) t) := by
  let B := I.canonicalBatching L hL
  apply PublicSnapshot.ext_ready
  funext b
  ext n
  rw [mem_batchObservation]
  change n ∈ (B.observe ⟨t, fun v => if B.execution m v < t
    then some (B.execution m v) else none⟩).expose.ready b ↔ _
  rw [ReadySnapshot.mem_expose_ready]
  constructor
  · rintro ⟨c, hc, v, hv, hn⟩
    have hv' := (B.observe_schedule_ready _ t c v).mp hv
    refine ⟨I.fifoPriority v, (I.mem_readyObservation _ _ _).mpr ⟨v, hv'.2.2, rfl⟩, ?_, ?_, hn⟩
    · have he := congrArg Fin.val hv'.1
      change I.release (I.owner v) / (2 * L) = c.val at he
      exact he.trans hc
    · have he := hv'.2.1
      change 2 * L * (c.val + 1) ≤ t at he
      simpa [hc] using he
  · rintro ⟨x, hx, hb, he, hn⟩
    obtain ⟨v, hv, rfl⟩ := (I.mem_readyObservation _ _ _).mp hx
    let c := B.vertexBatch v
    have hc : c.val = b := hb
    refine ⟨c, hc, v, (B.observe_schedule_ready _ _ _ _).mpr ⟨rfl, ?_, hv⟩, hn⟩
    change 2 * L * (c.val + 1) ≤ t
    simpa [hc] using he

/-- SFF is non-clairvoyant with respect to ordinary ready observations,
even across instances with different hidden jobs, vertices, and batches. -/
theorem sffSchedule_nonclairvoyant {otherJobs otherVertices m L : ℕ}
    (J : Instance otherJobs otherVertices) [DecidableRel J.edge]
    (hm : 0 < m) (hL : 0 < L) (t : ℕ)
    (h : ∀ u ≤ t, I.readyObservation (I.sffSchedule m L hL) u =
      J.readyObservation (J.sffSchedule m L hL) u) :
    (univ.filter (fun v => I.sffSchedule m L hL v = t)).image Fin.val =
      (univ.filter (fun v => J.sffSchedule m L hL v = t)).image Fin.val := by
  apply (I.canonicalBatching L hL).execution_nonclairvoyant (J.canonicalBatching L hL) hm t
  intro u hu
  rw [I.sff_publicHistory_eq, J.sff_publicHistory_eq, h u hu]

/-- The constructed SFF schedule realizes a single stateful policy whose
inputs are raw ready observations, the processor count, and the guess. -/
theorem sffSchedule_publicPolicy {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (t : ℕ) :
    (univ.filter (fun v => I.sffSchedule m L hL v = t)).image Fin.val =
      (sffRawPolicy m L).decision (I.readyObservation (I.sffSchedule m L hL)) t := by
  rw [sffRawPolicy_decision]
  have he : (I.canonicalBatching L hL).publicHistory m =
      fun u => batchObservation L u (I.readyObservation (I.sffSchedule m L hL) u) :=
    funext (fun u => I.sff_publicHistory_eq m L hL u)
  rw [← he]
  exact (I.canonicalBatching L hL).execution_publicPolicy hm t

end Instance
end Scheduling
