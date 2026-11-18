import Scheduling.Packing
import Scheduling.BatchedRecords
import Mathlib.Data.Prod.Lex

/-! A deterministic FIFO executor. Its state is just the set of completed
vertices. The environment exposes a ready set; the selection routine orders
that set by release time, with vertex identifiers breaking ties. -/
namespace Scheduling.Instance
open Finset
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

def fifoPriority (v : Fin vertices) : ℕ ×ₗ ℕ :=
  toLex (I.release (I.owner v), v.val)

theorem fifoPriority_injective : Function.Injective I.fifoPriority := by
  intro u v he
  exact Fin.ext (congrArg (fun x : ℕ ×ₗ ℕ => (ofLex x).2) he)

/-- This planner reads only the exposed ready vertices and their release
times. Hidden vertices and edges are used only by the environment below. -/
def fifoSelect (m : ℕ) (ready : Finset (Fin vertices)) : Finset (Fin vertices) :=
  ready.filter (fun v => I.fifoPriority v ∈ Packing.slice (ready.image I.fifoPriority) 0 m)

theorem fifoSelect_subset (m : ℕ) (ready : Finset (Fin vertices)) :
    I.fifoSelect m ready ⊆ ready := filter_subset _ _

theorem fifoSelect_image (m : ℕ) (ready : Finset (Fin vertices)) :
    (I.fifoSelect m ready).image I.fifoPriority =
      Packing.slice (ready.image I.fifoPriority) 0 m := by
  ext x
  constructor
  · rintro hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hv).2
  · intro hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp (Packing.slice_subset _ _ _ hx)
    exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hx⟩, rfl⟩

theorem fifoSelect_card (m : ℕ) (ready : Finset (Fin vertices)) :
    (I.fifoSelect m ready).card = min m ready.card := by
  rw [← card_image_of_injective _ I.fifoPriority_injective, I.fifoSelect_image,
    Packing.slice_card, Nat.sub_zero, card_image_of_injective _ I.fifoPriority_injective]

theorem fifoSelect_full {m : ℕ} {ready : Finset (Fin vertices)} {v : Fin vertices}
    (hv : v ∈ ready) (hn : v ∉ I.fifoSelect m ready) : (I.fifoSelect m ready).card = m := by
  have hnot : I.fifoPriority v ∉ Packing.slice (ready.image I.fifoPriority) 0 m := by
    intro h; exact hn (mem_filter.mpr ⟨hv, h⟩)
  have hf := Packing.first_slice_full (mem_image.mpr ⟨v, hv, rfl⟩) hnot
  rw [← I.fifoSelect_image, card_image_of_injective _ I.fifoPriority_injective] at hf
  exact hf

theorem fifoSelect_priority {m : ℕ} {ready : Finset (Fin vertices)} {u v : Fin vertices}
    (hu : u ∈ I.fifoSelect m ready) (hv : v ∈ ready) (hn : v ∉ I.fifoSelect m ready) :
    I.release (I.owner u) ≤ I.release (I.owner v) := by
  have hnot : I.fifoPriority v ∉ Packing.slice (ready.image I.fifoPriority) 0 m := by
    intro h; exact hn (mem_filter.mpr ⟨hv, h⟩)
  have hlt := Packing.first_slice_lt (mem_filter.mp hu).2 (mem_image.mpr ⟨v, hv, rfl⟩) hnot
  exact Prod.Lex.monotone_fst _ _ hlt.le

/-- Changing hidden DAGs, job ownership, or releases outside the exposed
frontier cannot affect the planner when the ready vertices and their public
release times agree. The two instances may have different numbers of jobs. -/
theorem fifoSelect_observation_eq {otherJobs : ℕ} (J : Instance otherJobs vertices)
    (m : ℕ) (ready : Finset (Fin vertices))
    (hr : ∀ v ∈ ready, I.release (I.owner v) = J.release (J.owner v)) :
    I.fifoSelect m ready = J.fifoSelect m ready := by
  have hp : ∀ v ∈ ready, I.fifoPriority v = J.fifoPriority v := by
    intro v hv
    simp only [fifoPriority, hr v hv]
  have him : ready.image I.fifoPriority = ready.image J.fifoPriority := by
    apply image_congr
    intro v hv
    exact hp v hv
  apply filter_congr
  intro v hv
  rw [hp v hv, him]

variable [DecidableRel I.edge]

def fifoReady (done : Finset (Fin vertices)) (t : ℕ) : Finset (Fin vertices) :=
  univ.filter (fun v => I.release (I.owner v) ≤ t ∧ v ∉ done ∧
    ∀ u, I.edge u v → u ∈ done)

def fifoRun (m : ℕ) : ℕ → Finset (Fin vertices)
  | 0 => ∅
  | t + 1 => fifoRun m t ∪ I.fifoSelect m (I.fifoReady (fifoRun m t) t)

def fifoAction (m t : ℕ) : Finset (Fin vertices) :=
  I.fifoSelect m (I.fifoReady (I.fifoRun m t) t)

theorem fifoRun_mono (m : ℕ) : Monotone (I.fifoRun m) := by
  apply monotone_nat_of_le_succ
  intro t
  exact subset_union_left

theorem fifoAction_ready {m t : ℕ} {v : Fin vertices} (hv : v ∈ I.fifoAction m t) :
    I.release (I.owner v) ≤ t ∧ v ∉ I.fifoRun m t ∧
      ∀ u, I.edge u v → u ∈ I.fifoRun m t :=
  (mem_filter.mp (I.fifoSelect_subset _ _ hv)).2

theorem fifoAction_card (m t : ℕ) : (I.fifoAction m t).card ≤ m := by
  unfold fifoAction
  rw [I.fifoSelect_card]
  exact min_le_left _ _

def fifoHorizon : ℕ := univ.sup I.release + vertices

theorem fifo_ready_exists {done : Finset (Fin vertices)} {t : ℕ}
    (hr : ∀ j, I.release j ≤ t) (hu : ∃ v, v ∉ done) : (I.fifoReady done t).Nonempty := by
  have aux : ∀ n v, I.rank v = n → v ∉ done → (I.fifoReady done t).Nonempty := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hn
      by_cases hp : ∀ u, I.edge u v → u ∈ done
      · exact ⟨v, mem_filter.mpr ⟨mem_univ _, hr _, hn, hp⟩⟩
      · push Not at hp
        obtain ⟨u, he, hu⟩ := hp
        exact ih (I.rank u) (by have := I.rank_increases he; omega) u rfl hu
  obtain ⟨v, hv⟩ := hu
  exact aux _ v rfl hv

theorem fifo_step_progress {m t : ℕ} (hm : 0 < m)
    (hr : ∀ j, I.release j ≤ t) (hu : ∃ v, v ∉ I.fifoRun m t) :
    (I.fifoRun m t).card + 1 ≤ (I.fifoRun m (t + 1)).card := by
  have hready := I.fifo_ready_exists hr hu
  have hpos : 0 < (I.fifoAction m t).card := by
    rw [fifoAction, I.fifoSelect_card]
    exact lt_min hm (card_pos.mpr hready)
  obtain ⟨v, hv⟩ := card_pos.mp hpos
  have hn := (I.fifoAction_ready hv).2.1
  have hsub : insert v (I.fifoRun m t) ⊆ I.fifoRun m (t + 1) := by
    apply insert_subset_iff.mpr
    exact ⟨mem_union_right _ hv, I.fifoRun_mono m (by omega)⟩
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hn] at hc
  exact hc

theorem fifo_terminates {m : ℕ} (hm : 0 < m) (v : Fin vertices) :
    v ∈ I.fifoRun m I.fifoHorizon := by
  by_contra hv
  have hcount : ∀ k, k ≤ vertices → k ≤ (I.fifoRun m (univ.sup I.release + k)).card := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hn : v ∉ I.fifoRun m (univ.sup I.release + k) := by
        intro hvk
        exact hv (I.fifoRun_mono m (by unfold fifoHorizon; omega) hvk)
      have hr : ∀ j, I.release j ≤ univ.sup I.release + k := by
        intro j; have : I.release j ≤ univ.sup I.release := le_sup (mem_univ j); omega
      have hstep := I.fifo_step_progress hm hr ⟨v, hn⟩
      simpa [Nat.add_assoc] using (show k + 1 ≤ _ from (Nat.add_le_add_right hp 1).trans hstep)
  have hc := hcount vertices le_rfl
  have heq : I.fifoRun m I.fifoHorizon = univ :=
    eq_of_subset_of_card_le (subset_univ _) (by simpa [fifoHorizon] using hc)
  exact hv (heq ▸ mem_univ v)


theorem fifo_exists_done {m : ℕ} (hm : 0 < m) (v : Fin vertices) :
    ∃ t, v ∈ I.fifoRun m t := ⟨I.fifoHorizon, I.fifo_terminates hm v⟩

/-- The execution slot is one less than the first completed-state index.
The search uses just the operational run; the finite horizon only proves
that the search terminates. -/
def fifoSchedule (m : ℕ) (hm : 0 < m) : Assignment (vertices := vertices) :=
  fun v => Nat.find (I.fifo_exists_done hm v) - 1

theorem fifo_first_done_pos {m : ℕ} (hm : 0 < m) (v : Fin vertices) :
    0 < Nat.find (I.fifo_exists_done hm v) := by
  have hv := Nat.find_spec (I.fifo_exists_done hm v)
  by_contra hn
  have he : Nat.find (I.fifo_exists_done hm v) = 0 := by omega
  rw [he] at hv
  simp [fifoRun] at hv

theorem fifo_done_iff {m : ℕ} (hm : 0 < m) (v : Fin vertices) (t : ℕ) :
    v ∈ I.fifoRun m t ↔ I.fifoSchedule m hm v < t := by
  have hp := I.fifo_first_done_pos hm v
  constructor
  · intro hv
    have hf := Nat.find_min' (I.fifo_exists_done hm v) hv
    dsimp [fifoSchedule]
    omega
  · intro hv
    have hf : Nat.find (I.fifo_exists_done hm v) ≤ t := by
      dsimp [fifoSchedule] at hv
      omega
    exact I.fifoRun_mono m hf (Nat.find_spec (I.fifo_exists_done hm v))

theorem fifo_action_iff {m : ℕ} (hm : 0 < m) (v : Fin vertices) (t : ℕ) :
    v ∈ I.fifoAction m t ↔ I.fifoSchedule m hm v = t := by
  constructor
  · intro hv
    have hn := (I.fifoAction_ready hv).2.1
    have hd : v ∈ I.fifoRun m (t + 1) := mem_union_right _ hv
    rw [I.fifo_done_iff hm] at hn hd
    omega
  · intro hv
    have hd : v ∈ I.fifoRun m (t + 1) := (I.fifo_done_iff hm _ _).mpr (by omega)
    have hn : v ∉ I.fifoRun m t := by rw [I.fifo_done_iff hm]; omega
    change v ∈ I.fifoRun m t ∪ I.fifoAction m t at hd
    exact (mem_union.mp hd).resolve_left hn

theorem fifo_action_eq {m : ℕ} (hm : 0 < m) (t : ℕ) :
    I.fifoAction m t = univ.filter (fun v => I.fifoSchedule m hm v = t) := by
  ext v
  simpa only [mem_filter, mem_univ, true_and] using I.fifo_action_iff hm v t

theorem fifoSchedule_valid {m : ℕ} (hm : 0 < m) : I.Valid m (I.fifoSchedule m hm) := by
  constructor
  · intro v
    exact (I.fifoAction_ready ((I.fifo_action_iff hm _ _).mpr rfl)).1
  · intro u v he
    have hready := I.fifoAction_ready ((I.fifo_action_iff hm v _).mpr rfl)
    exact (I.fifo_done_iff hm _ _).mp (hready.2.2 u he)
  · intro t
    rw [← I.fifo_action_eq hm t]
    exact I.fifoAction_card m t

theorem fifo_ready_iff {m : ℕ} (hm : 0 < m) (v : Fin vertices) (t : ℕ) :
    v ∈ I.fifoReady (I.fifoRun m t) t ↔ I.Ready (I.fifoSchedule m hm) t v := by
  simp only [fifoReady, mem_filter, mem_univ, true_and, Ready, I.fifo_done_iff hm,
    Nat.not_lt]

theorem fifoSchedule_isFIFO {m : ℕ} (hm : 0 < m) : I.IsFIFO m (I.fifoSchedule m hm) := by
  constructor
  · intro t v hv hn
    rw [← I.fifo_action_eq hm t]
    exact I.fifoSelect_full ((I.fifo_ready_iff hm _ _).mpr hv)
      (by change v ∉ I.fifoAction m t; rw [I.fifo_action_iff hm]; exact hn)
  · intro t v u hv hn hu
    exact I.fifoSelect_priority ((I.fifo_action_iff hm _ _).mpr hu)
      ((I.fifo_ready_iff hm _ _).mpr hv)
      (by change v ∉ I.fifoAction m t; rw [I.fifo_action_iff hm]; exact hn)

/-- The general FIFO bound now applies to an explicitly constructed schedule. -/
theorem fifoSchedule_competitive {m : ℕ} (hm : 0 < m) :
    m * I.maxFlow (I.fifoSchedule m hm) ≤ (m * m + m - 1) * I.optimum m hm :=
  I.fifo_competitive hm (I.fifoSchedule_valid hm) (I.fifoSchedule_isFIFO hm)

theorem fifoSchedule_batched_bound {m : ℕ} (hm : 0 < m) (hj : 0 < jobs)
    (hb : I.BatchedArrivals (I.optimum m hm)) :
    I.maxFlow (I.fifoSchedule m hm) ≤
      (Nat.clog 2 (I.optimum m hm) + 2) * I.optimum m hm :=
  I.batched_fifo_competitive hm hj hb (I.fifoSchedule_valid hm) (I.fifoSchedule_isFIFO hm)

end Scheduling.Instance
