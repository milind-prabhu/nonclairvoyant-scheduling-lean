import Scheduling.FIFO

namespace Scheduling.Instance
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices : ℕ} (I : Instance jobs vertices)

/-- A serial feasible schedule. The rank and vertex index are used only for
the offline existence proof. They are not given to FIFO. -/
noncomputable def serialSchedule : Assignment (vertices := vertices) :=
  fun v => univ.sup I.release + I.rank v * (vertices + 1) + v.val

theorem serialSchedule_injective : Function.Injective I.serialSchedule := by
  intro u v huv
  have hu := u.isLt
  have hv := v.isLt
  have he : I.rank u * (vertices + 1) + u.val = I.rank v * (vertices + 1) + v.val := by
    dsimp [serialSchedule] at huv
    omega
  have hr : I.rank u = I.rank v := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hm := Nat.mul_le_mul_right (vertices + 1) (show I.rank u + 1 ≤ I.rank v by omega)
      nlinarith
    · have hm := Nat.mul_le_mul_right (vertices + 1) (show I.rank v + 1 ≤ I.rank u by omega)
      nlinarith
  apply Fin.ext
  rw [hr] at he
  omega

theorem serialSchedule_valid {m : ℕ} (hm : 0 < m) : I.Valid m I.serialSchedule := by
  classical
  constructor
  · intro v
    have hr : I.release (I.owner v) ≤ univ.sup I.release := le_sup (mem_univ _)
    dsimp [serialSchedule]
    omega
  · intro u v he
    have hr := I.rank_increases he
    have hu := u.isLt
    have hm := Nat.mul_le_mul_right (vertices + 1) (show I.rank u + 1 ≤ I.rank v by omega)
    dsimp [serialSchedule]
    nlinarith
  · intro t
    have hc : (univ.filter (fun v => I.serialSchedule v = t)).card ≤ 1 := by
      apply card_le_one.mpr
      intro u hu v hv
      exact I.serialSchedule_injective ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
    omega

theorem exists_offline_bound {m : ℕ} (hm : 0 < m) :
    ∃ L, ∃ O : Assignment (vertices := vertices), I.Valid m O ∧ I.FlowBound O L := by
  classical
  refine ⟨univ.sup (fun v => I.serialSchedule v + 1), I.serialSchedule,
    I.serialSchedule_valid hm, ?_⟩
  intro v
  have h : I.serialSchedule v + 1 ≤ univ.sup (fun v => I.serialSchedule v + 1) := le_sup (f := fun v => I.serialSchedule v + 1) (mem_univ v)
  omega

/-- The minimum possible maximum flow time, whose existence is proved above. -/
noncomputable def optimum (m : ℕ) (hm : 0 < m) : ℕ := Nat.find (I.exists_offline_bound hm)

theorem optimum_attained {m : ℕ} (hm : 0 < m) :
    ∃ O : Assignment (vertices := vertices), I.Valid m O ∧ I.FlowBound O (I.optimum m hm) :=
  Nat.find_spec (I.exists_offline_bound hm)

theorem optimum_pos {m : ℕ} (hm : 0 < m) (hj : 0 < jobs) : 0 < I.optimum m hm := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  obtain ⟨v, _⟩ := I.nonempty_job ⟨0, hj⟩
  exact I.flowBound_pos hO hL v

theorem optimum_le {m L : ℕ} (hm : 0 < m) {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) : I.optimum m hm ≤ L :=
  Nat.find_min' (I.exists_offline_bound hm) ⟨O, hO, hL⟩

theorem optimum_le_maxFlow {m : ℕ} (hm : 0 < m) {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) : I.optimum m hm ≤ I.maxFlow O :=
  I.optimum_le hm hO ((I.flowBound_iff_maxFlow_le O _).mpr le_rfl)

theorem optimum_eq_minimum {m : ℕ} (hm : 0 < m) :
    ∃ O : Assignment (vertices := vertices), I.Valid m O ∧ I.maxFlow O = I.optimum m hm := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  exact ⟨O, hO, Nat.le_antisymm ((I.flowBound_iff_maxFlow_le O _).mp hL) (I.optimum_le_maxFlow hm hO)⟩

/-- The paper's exact FIFO competitive factor relative to the actual minimum
offline maximum flow, expressed without division. -/
theorem fifo_competitive {m : ℕ} {S : Assignment (vertices := vertices)}
    (hm : 0 < m) (hS : I.Valid m S) (hF : I.IsFIFO m S) :
    m * I.maxFlow S ≤ (m * m + m - 1) * I.optimum m hm := by
  obtain ⟨O, hO, hL⟩ := I.optimum_attained hm
  exact I.fifo_maxFlow_bound hm hS hF hO hL

end Scheduling.Instance
