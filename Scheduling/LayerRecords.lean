import Scheduling.LayerChronology

namespace Scheduling
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable

structure LayerRecord (jobs work : ℕ) where
  owner : Fin jobs
  start : ℕ
  stop : ℕ
  key : Fin work
  time : ℕ
  deriving DecidableEq

namespace LayeredPrefix
variable {jobs work : ℕ}

noncomputable def record (P : LayeredPrefix jobs work) {m L : ℕ}
    (hw : 0 < work) (A : DeterministicScheduler m) (j : Fin jobs) (key : Fin work) : LayerRecord jobs work :=
  ⟨j, P.closed j, P.boundary j, key, A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key))⟩

inductive RecordedRun {m L : ℕ} (hw : 0 < work) (A : DeterministicScheduler m)
    (rule : LayerSizeRule jobs work) :
    LayeredPrefix jobs work → LayeredPrefix jobs work → List (LayerRecord jobs work) → Prop
  | done (P : LayeredPrefix jobs work) (h : ∀ j, P.closed j = work) :
      RecordedRun (L := L) hw A rule P P []
  | step (P Q : LayeredPrefix jobs work) (j : Fin jobs) (key : Fin work)
      (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
      (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
      (hearliest : ∀ i, P.closed i < work →
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) ≤ P.finishTime (L := L) hw A i)
      (records : List (LayerRecord jobs work))
      (tail : RecordedRun (L := L) hw A rule
        (P.advance j key hk
          (rule.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
          (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)) Q records) :
      RecordedRun (L := L) hw A rule P Q (P.record (L := L) hw A j key :: records)

theorem RecordedRun.completion {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) : CompletionRun (L := L) hw A rule P Q := by
  induction h with
  | done P hd => exact CompletionRun.done P hd
  | step P Q j key hk hmax hearliest records tail ih =>
    exact CompletionRun.step P Q j key hk hmax hearliest ih

theorem CompletionRun.records {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work}
    (h : CompletionRun (L := L) hw A rule P Q) :
    ∃ records, RecordedRun (L := L) hw A rule P Q records := by
  induction h with
  | done P hd => exact ⟨[], RecordedRun.done P hd⟩
  | step P Q j key hk hmax hearliest tail ih =>
    obtain ⟨records, hr⟩ := ih
    exact ⟨_, RecordedRun.step P Q j key hk hmax hearliest records hr⟩

/-- Every committed layer really has its selected key last in the final,
fixed instance. Both the layer interval and its exact closing time are
retained by the certificate. -/
theorem RecordedRun.final_times {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ r ∈ records,
      r.start ≤ r.key.val ∧ r.key.val < r.stop ∧ r.stop ≤ work ∧
      A.schedule (Q.toInstance L hw) (finProdFinEquiv (r.owner, r.key)) = r.time ∧
      ∀ v : Fin (jobs * work), job v = r.owner → r.start ≤ (position v).val → (position v).val < r.stop →
        A.schedule (Q.toInstance L hw) v ≤ r.time := by
  induction h with
  | done P hd => simp
  | step P Q j key hk hmax hearliest records tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have htimes := P.head_times_in_final hw A rule Q j key hk hmax hearliest tail.completion
      refine ⟨hk.1, hk.2, P.fits j, htimes _ le_rfl, ?_⟩
      intro v hj hlo hhi
      have hv : v ∈ P.frontier j := mem_filter.mpr ⟨mem_univ _, hj, hlo, hhi⟩
      have hvtime := hmax v hv
      rw [htimes v hvtime]
      exact hvtime
    · exact ih r hr

theorem RecordedRun.start_lower {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ r ∈ records, P.closed r.owner ≤ r.start := by
  induction h with
  | done P hd => simp
  | step P Q j key hk hmax hearliest records tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · have hh := ih r hr
      by_cases he : r.owner = j
      · simp only [advance, he] at hh
        dsimp [boundary] at hh
        rw [he]
        omega
      · simpa only [advance, if_neg he] using hh

/-- The recorded layer intervals cover exactly the suffix that was not
already closed when the construction started. -/
theorem RecordedRun.covers {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ j (k : Fin work), P.closed j ≤ k.val →
      ∃ r ∈ records, r.owner = j ∧ r.start ≤ k.val ∧ k.val < r.stop := by
  induction h with
  | done P hd =>
    intro j k hk
    have := k.isLt
    rw [hd] at hk
    omega
  | step P Q j key hk hmax hearliest records tail ih =>
    intro i k hki
    by_cases he : i = j
    · subst i
      by_cases hc : k.val < P.boundary j
      · exact ⟨P.record hw A j key, List.mem_cons_self, rfl, hki, hc⟩
      · obtain ⟨r, hr, ho, hlo, hhi⟩ := ih j k (by rw [advance_closed]; omega)
        exact ⟨r, List.mem_cons_of_mem _ hr, ho, hlo, hhi⟩
    · obtain ⟨r, hr, ho, hlo, hhi⟩ := ih i k (by simpa only [advance, if_neg he] using hki)
      exact ⟨r, List.mem_cons_of_mem _ hr, ho, hlo, hhi⟩

theorem RecordedRun.ordered_intervals {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    records.Pairwise (fun a b => a.owner = b.owner → a.stop ≤ b.start) := by
  induction h with
  | done P hd => exact List.Pairwise.nil
  | step P Q j key hk hmax hearliest records tail ih =>
    rw [List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro r hr he
    have hl := tail.start_lower r hr
    change j = r.owner at he
    rw [← he, advance_closed] at hl
    exact hl

theorem RecordedRun.next_parents {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ r ∈ records, ∀ v : Fin work, r.stop ≤ v.val →
      v.val < r.stop + rule.size r.owner r.stop (r.time + 1) →
      Q.parent r.owner v = some r.key := by
  induction h with
  | done P hd => simp
  | step P Q j key hk hmax hearliest records tail ih =>
    intro r hr v hlo hhi
    rcases List.mem_cons.mp hr with rfl | hr
    · have hp := tail.completion.parent_visible j v (by rw [advance_boundary]; exact hhi)
      change Q.parent j v = some key
      rw [hp]
      change (if j = j ∧ P.boundary j ≤ v.val ∧
        v.val < P.boundary j + rule.size j (P.boundary j)
          (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1) then some key else _) = some key
      rw [if_pos ⟨rfl, hlo, hhi⟩]
    · exact ih r hr v hlo hhi

/-- Every newly installed parent is one of the committed layer keys. -/
theorem RecordedRun.parent_origins {m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}
    {rule : LayerSizeRule jobs work} {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records) :
    ∀ j v u, Q.parent j v = some u →
      P.parent j v = some u ∨ ∃ r ∈ records, r.owner = j ∧ r.key = u := by
  induction h with
  | done P hd => intro j v u hp; exact Or.inl hp
  | step P Q j key hk hmax hearliest records tail ih =>
    intro i v u hp
    rcases ih i v u hp with hprev | ⟨r, hr, ho, hkey⟩
    · change (if i = j ∧ P.boundary j ≤ v.val ∧ v.val < P.boundary j + _ then some key else P.parent i v) =
        some u at hprev
      split_ifs at hprev with hnew
      · exact Or.inr ⟨P.record hw A j key, List.mem_cons_self, hnew.1.symm, Option.some.inj hprev⟩
      · exact Or.inl hprev
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, ho, hkey⟩

end LayeredPrefix
end Scheduling
