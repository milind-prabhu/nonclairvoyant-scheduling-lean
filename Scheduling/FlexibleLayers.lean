import Scheduling.LayerRecords

namespace Scheduling.LayeredPrefix
open Finset
open LayeredForest (job position)
attribute [local instance] Classical.propDecidable
variable {jobs work m L : ℕ} {hw : 0 < work} {A : DeterministicScheduler m}

/-- Replacing rule entries for already closed prefixes cannot affect a
recorded run. Every future query is strictly beyond the current closed
prefix of its job. -/
theorem RecordedRun.change_rule {rule : LayerSizeRule jobs work}
    {P Q : LayeredPrefix jobs work} {records : List (LayerRecord jobs work)}
    (h : RecordedRun (L := L) hw A rule P Q records)
    (rule' : LayerSizeRule jobs work)
    (hagree : ∀ j p t, P.closed j < p → p ≤ work → rule.size j p t = rule'.size j p t) :
    RecordedRun (L := L) hw A rule' P Q records := by
  induction h with
  | done P hd => exact RecordedRun.done P hd
  | step P Q j key hk hmax hearliest records tail ih =>
    let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1
    have he : rule.size j (P.boundary j) t = rule'.size j (P.boundary j) t :=
      hagree j _ t (by omega) (P.fits j)
    have ht := ih (by
      intro i p u hp hwork
      apply hagree i p u ?_ hwork
      have hclosed : P.closed i ≤
          (P.advance j key hk (rule.size j (P.boundary j) t)
            (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _)).closed i := by
        by_cases hi : i = j
        · subst i
          rw [advance_closed]
          dsimp [boundary]
          omega
        · simp only [advance, if_neg hi, le_refl]
      dsimp [t] at hclosed
      omega)
    have hstate : P.advance j key hk (rule.size j (P.boundary j) t)
        (rule.fits _ _ _ (P.fits j)) (rule.positive _ _ _) =
      P.advance j key hk (rule'.size j (P.boundary j) t)
        (rule'.fits _ _ _ (P.fits j)) (rule'.positive _ _ _) := by
      congr 1
    change RecordedRun (L := L) hw A rule' _ Q records at ht
    rw [hstate] at ht
    exact RecordedRun.step P Q j key hk hmax hearliest records ht

/-- A chronological hidden-key construction whose next width can depend
on the entire current state and execution history, rather than just the
job, prefix length, and reveal time. -/
inductive FlexibleRun (hw : 0 < work) (A : DeterministicScheduler m) (L : ℕ) :
    LayeredPrefix jobs work → LayeredPrefix jobs work → List (LayerRecord jobs work) → Prop
  | done (P : LayeredPrefix jobs work) (h : ∀ j, P.closed j = work) :
      FlexibleRun hw A L P P []
  | step (P Q : LayeredPrefix jobs work) (j : Fin jobs) (key : Fin work)
      (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
      (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
      (hearliest : ∀ i, P.closed i < work →
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) ≤ P.finishTime (L := L) hw A i)
      (q : ℕ) (hq : P.boundary j + q ≤ work) (hp : P.boundary j < work → 0 < q)
      (records : List (LayerRecord jobs work))
      (tail : FlexibleRun hw A L (P.advance j key hk q hq hp) Q records) :
      FlexibleRun hw A L P Q (P.record (L := L) hw A j key :: records)

/-- After a finite adaptive construction, its choices can be encoded in
a static rule. This transfers all previously proved chronological,
parent-edge, coverage, and key-last certificates to history-dependent
width choices. -/
theorem FlexibleRun.recorded {P Q : LayeredPrefix jobs work}
    {records : List (LayerRecord jobs work)} (h : FlexibleRun hw A L P Q records) :
    ∃ rule : LayerSizeRule jobs work, RecordedRun (L := L) hw A rule P Q records := by
  induction h with
  | done P hd =>
    let rule : LayerSizeRule jobs work := {
      size := fun _ p _ => min 1 (work - p)
      fits := by intro j p t hp; have := min_le_right 1 (work - p); omega
      positive := by intro j p t hp; exact lt_min (by omega) (by omega) }
    exact ⟨rule, RecordedRun.done P hd⟩
  | step P Q j key hk hmax hearliest q hq hp records tail ih =>
    obtain ⟨rule, hr⟩ := ih
    let rule' : LayerSizeRule jobs work := {
      size := fun i p t => if i = j ∧ p = P.boundary j then q else rule.size i p t
      fits := by
        intro i p t hwork
        split_ifs with he
        · simpa only [he.2] using hq
        · exact rule.fits i p t hwork
      positive := by
        intro i p t hwork
        split_ifs with he
        · exact hp (by omega)
        · exact rule.positive i p t hwork }
    have hr' := hr.change_rule rule' (by
      intro i p t hclosed hwork
      have hn : ¬ (i = j ∧ p = P.boundary j) := by
        rintro ⟨rfl, rfl⟩
        rw [advance_closed] at hclosed
        omega
      simp only [rule', if_neg hn])
    have hsize : rule'.size j (P.boundary j)
        (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1) = q := by
      simp only [rule', and_self, if_true]
    have hstate : P.advance j key hk q hq hp =
      P.advance j key hk
        (rule'.size j (P.boundary j) (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
        (rule'.fits _ _ _ (P.fits j)) (rule'.positive _ _ _) := by
      congr 1
      exact hsize.symm
    rw [hstate] at hr'
    exact ⟨rule', RecordedRun.step P Q j key hk hmax hearliest records hr'⟩

/-- The history supplied to the rule includes the layer just completed.
Its records contain the actual key timestamps, so a rule can reset its
counters at epoch boundaries and inspect earlier layer types. -/
structure HistoryLayerRule (jobs work : ℕ) where
  size : List (LayerRecord jobs work) → LayeredPrefix jobs work → Fin jobs → ℕ → ℕ
  fits : ∀ history P j t, P.boundary j + size history P j t ≤ work
  positive : ∀ history P j t, P.boundary j < work → 0 < size history P j t

inductive HistoryRun (hw : 0 < work) (A : DeterministicScheduler m) (L : ℕ)
    (rule : HistoryLayerRule jobs work) : List (LayerRecord jobs work) →
    LayeredPrefix jobs work → LayeredPrefix jobs work → List (LayerRecord jobs work) → Prop
  | done (history : List (LayerRecord jobs work)) (P : LayeredPrefix jobs work)
      (h : ∀ j, P.closed j = work) : HistoryRun hw A L rule history P P []
  | step (history : List (LayerRecord jobs work)) (P Q : LayeredPrefix jobs work)
      (j : Fin jobs) (key : Fin work)
      (hk : P.closed j ≤ key.val ∧ key.val < P.boundary j)
      (hmax : ∀ v ∈ P.frontier j, A.schedule (P.toInstance L hw) v ≤
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)))
      (hearliest : ∀ i, P.closed i < work →
        A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) ≤ P.finishTime (L := L) hw A i)
      (records : List (LayerRecord jobs work))
      (tail : HistoryRun hw A L rule (history ++ [P.record (L := L) hw A j key])
        (P.advance j key hk
          (rule.size (history ++ [P.record (L := L) hw A j key]) P j
            (A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1))
          (rule.fits _ _ _ _) (rule.positive _ _ _ _)) Q records) :
      HistoryRun hw A L rule history P Q (P.record (L := L) hw A j key :: records)

theorem HistoryRun.flexible {rule : HistoryLayerRule jobs work}
    {history records : List (LayerRecord jobs work)} {P Q : LayeredPrefix jobs work}
    (h : HistoryRun hw A L rule history P Q records) : FlexibleRun hw A L P Q records := by
  induction h with
  | done history P hd => exact FlexibleRun.done P hd
  | step history P Q j key hk hmax hearliest records tail ih =>
    exact FlexibleRun.step P Q j key hk hmax hearliest _ _ _ records ih

/-- Arbitrary history-dependent width rules terminate, provided every
unfinished job receives a nonempty frontier within its remaining budget. -/
theorem exists_history_run (rule : HistoryLayerRule jobs work)
    (history : List (LayerRecord jobs work)) (P : LayeredPrefix jobs work)
    (hw : 0 < work) (A : DeterministicScheduler m) (L : ℕ) :
    ∃ Q records, HistoryRun hw A L rule history P Q records := by
  have aux : ∀ n : ℕ, ∀ history (P : LayeredPrefix jobs work), P.remainingMass = n →
      ∃ Q records, HistoryRun hw A L rule history P Q records := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro history P hn
      by_cases ha : ∃ j, P.closed j < work
      · obtain ⟨j, key, hk, hmax, hearliest⟩ := P.exists_earliest (L := L) hw A ha
        let next := history ++ [P.record (L := L) hw A j key]
        let t := A.schedule (P.toInstance L hw) (finProdFinEquiv (j, key)) + 1
        let q := rule.size next P j t
        let R := P.advance j key hk q (rule.fits _ _ _ _) (rule.positive _ _ _ _)
        have hlt : R.remainingMass < n := by
          rw [← hn]
          exact P.advance_mass_lt j key hk q _ _
        obtain ⟨Q, records, hQ⟩ := ih R.remainingMass hlt next R rfl
        exact ⟨Q, _, HistoryRun.step history P Q j key hk hmax hearliest records hQ⟩
      · have hd : ∀ j, P.closed j = work := by
          intro j
          have hf := P.fits j
          have hh : ¬ P.closed j < work := fun h => ha ⟨j, h⟩
          omega
        exact ⟨P, [], HistoryRun.done history P hd⟩
  exact aux P.remainingMass history P rfl

theorem exists_history_certificates (rule : HistoryLayerRule jobs work)
    (P : LayeredPrefix jobs work) (hw : 0 < work) (A : DeterministicScheduler m) (L : ℕ) :
    ∃ Q records, HistoryRun hw A L rule [] P Q records ∧
      ∃ staticRule, RecordedRun (L := L) hw A staticRule P Q records := by
  obtain ⟨Q, records, h⟩ := exists_history_run rule [] P hw A L
  exact ⟨Q, records, h, h.flexible.recorded⟩

end Scheduling.LayeredPrefix
