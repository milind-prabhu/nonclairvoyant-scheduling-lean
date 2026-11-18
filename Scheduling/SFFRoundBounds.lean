import Scheduling.SFFModel

namespace Scheduling.SFFRounds
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches m L : ℕ} {I : Instance jobs vertices}
variable {B : Batching I L batches} {S O : Assignment (vertices := vertices)}
variable (R : SFFRounds B m S)

theorem small_round_count (hO : I.Valid m O) (hL : I.FlowBound O L)
    (b : Fin batches) (K : ℕ) :
    (Instance.markedRounds (fun k => b ∈ B.small m S (R.boundary k)) K).card ≤ L := by
  classical
  apply I.frontier_round_count_bound hO hL (B.batchVertices b) (B.predecessor_closed b)
    R.boundary R.strict.monotone (fun k => b ∈ B.small m S (R.boundary k))
  · intro k hk v hv
    have ha := (mem_filter.mp hk).2.1.1
    exact (B.released_by_eligible (mem_filter.mp hv).2).le.trans ha
  · intro k hk v hv hr
    exact R.clear_small k b hk v (mem_filter.mp hv).2 hr
  · intro k hk
    obtain ⟨v, hv, hu⟩ := (mem_filter.mp hk).2.1.2
    exact ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩, hu⟩

theorem small_rounds_before_lt (hO : I.Valid m O) (hL : I.FlowBound O L)
    {b : Fin batches} {K : ℕ} (hb : b ∈ B.small m S (R.boundary K)) :
    (Instance.markedRounds (fun k => b ∈ B.small m S (R.boundary k)) K).card < L := by
  classical
  obtain ⟨v, hv, hu⟩ := (mem_filter.mp hb).2.1.2
  have hp := I.frontier_round_progress hO (B.batchVertices b) (B.predecessor_closed b)
    R.boundary R.strict.monotone (fun k => b ∈ B.small m S (R.boundary k))
    (by
      intro k hk w hw
      have ha := (mem_filter.mp hk).2.1.1
      exact (B.released_by_eligible (mem_filter.mp hw).2).le.trans ha)
    (by intro k hk w hw hr; exact R.clear_small k b hk w (mem_filter.mp hw).2 hr)
    K v (mem_filter.mpr ⟨mem_univ _, hv⟩) hu
  have hl := hL v
  omega

noncomputable def switches (k : ℕ) : Finset (Fin batches) :=
  (B.large m S (R.boundary k)).filter (fun b => b ∈ B.small m S (R.boundary (k + 1)))

/-- A batch can shrink from large to small only if one of its vertices is
processed during the round. Readiness depends only on its own predecessors. -/
theorem switch_has_service {k : ℕ} {b : Fin batches} (hb : b ∈ R.switches k) :
    ∃ v, B.vertexBatch v = b ∧ R.boundary k ≤ S v ∧ S v < R.boundary (k + 1) := by
  classical
  have hl := (mem_filter.mp (mem_filter.mp hb).1).2.2
  have hs := (mem_filter.mp (mem_filter.mp hb).2).2.2
  by_contra hn
  push Not at hn
  have hsub : B.frontier S (R.boundary k) b ⊆ B.frontier S (R.boundary (k + 1)) b := by
    intro v hv
    have hv' := (mem_filter.mp hv).2
    have ht := hn v hv'.1 hv'.2.2.1
    refine mem_filter.mpr ⟨mem_univ _, hv'.1, hv'.2.1.trans (R.strict.monotone (by omega)), ?_, ?_⟩
    · omega
    · intro u he
      exact (hv'.2.2.2 u he).trans_le (R.strict.monotone (by omega))
  have hc := card_le_card hsub
  omega

theorem switches_card_le_one (k : ℕ) : (R.switches k).card ≤ 1 := by
  apply card_le_one.mpr
  intro b hb c hc
  obtain ⟨v, hv, hv₁, hv₂⟩ := R.switch_has_service hb
  obtain ⟨w, hw, hw₁, hw₂⟩ := R.switch_has_service hc
  have hf₁ := R.large_service k v hv₁ hv₂ (by simpa [hv] using (mem_filter.mp hb).1)
  have hf₂ := R.large_service k w hw₁ hw₂ (by simpa [hw] using (mem_filter.mp hc).1)
  rw [hv] at hf₁
  rw [hw] at hf₂
  exact Option.some.inj (hf₁.symm.trans hf₂)

theorem round_length_le_small_count (hm : 0 < m) (k : ℕ) :
    R.boundary (k + 1) - R.boundary k ≤ max 1 (B.small m S (R.boundary k)).card := by
  classical
  let P := univ.filter (fun v => B.vertexBatch v ∈ B.small m S (R.boundary k) ∧ I.Ready S (R.boundary k) v)
  have heq : P.card = ∑ b ∈ B.small m S (R.boundary k), (P.filter (fun v => B.vertexBatch v = b)).card :=
    card_eq_sum_card_fiberwise (by intro v hv; exact (mem_filter.mp hv).2.1)
  have hc : P.card ≤ (B.small m S (R.boundary k)).card * m := by
    rw [heq]
    calc
      _ ≤ ∑ _b ∈ B.small m S (R.boundary k), m := by
        apply sum_le_sum
        intro b hb
        have hsub : P.filter (fun v => B.vertexBatch v = b) ⊆ B.frontier S (R.boundary k) b := by
          intro v hv
          have hv' := mem_filter.mp hv
          exact mem_filter.mpr ⟨mem_univ _, hv'.2, (mem_filter.mp hv'.1).2.2⟩
        exact (card_le_card hsub).trans (mem_filter.mp hb).2.2
      _ = _ := by simp
  have hdiv : (P.card + m - 1) / m ≤ (B.small m S (R.boundary k)).card := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    have hminus : P.card + m - 1 + 1 = P.card + m := by omega
    nlinarith
  rw [R.length_eq k]
  exact max_le_max le_rfl hdiv

/-- Sum a bound on earlier round lengths over any suffix of the past. -/
theorem boundary_span {K a D : ℕ} (ha : a ≤ K)
    (hprev : ∀ k < K, R.boundary (k + 1) - R.boundary k ≤ D) :
    R.boundary K ≤ R.boundary a + (K - a) * D := by
  have h : ∀ n, a ≤ n → n ≤ K → R.boundary n ≤ R.boundary a + (n - a) * D := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; simp
    | succ n hn ih =>
      intro hnK
      have hip := ih (by omega)
      have hd := hprev n (by omega)
      have hm := R.strict.monotone (show n ≤ n + 1 by omega)
      have he : n + 1 - a = n - a + 1 := by omega
      rw [he, Nat.add_mul]
      omega
  exact h K ha le_rfl

/-- Every currently small batch either became eligible recently or crossed
from large to small at one of the recent boundaries. The depth argument
rules out an old batch that was small in every one of the preceding L rounds. -/
theorem small_cover (hO : I.Valid m O) (hL : I.FlowBound O L) (hLp : 0 < L) (K : ℕ) :
    B.small m S (R.boundary K) ⊆
      univ.filter (fun b => R.boundary (K - L) < B.eligible b ∧ B.eligible b ≤ R.boundary K) ∪
      (Ico (K - L) K).biUnion R.switches := by
  classical
  intro b hb
  have ha := (mem_filter.mp hb).2.1
  by_cases hnew : R.boundary (K - L) < B.eligible b
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hnew, ha.1⟩)
  · apply mem_union_right
    by_contra hn
    have hold : B.eligible b ≤ R.boundary (K - L) := by omega
    have hLK : L ≤ K := by
      by_contra hh
      have he : K - L = 0 := by omega
      rw [he, R.starts_zero] at hold
      have := B.eligible_positive hLp b
      omega
    have hnoswitch : ∀ r, K - L ≤ r → r < K → b ∉ R.switches r := by
      intro r hr hrK hsw
      exact hn (mem_biUnion.mpr ⟨r, mem_Ico.mpr ⟨hr, hrK⟩, hsw⟩)
    have back : ∀ d r, r + d = K → K - L ≤ r → b ∈ B.small m S (R.boundary r) := by
      intro d
      induction d with
      | zero =>
        intro r he _
        have her : r = K := by omega
        rw [her]
        exact hb
      | succ d ih =>
        intro r he hr
        have hnext := ih (r + 1) (by omega) (by omega)
        have har : B.Active S (R.boundary r) b :=
          B.active_at_earlier (hold.trans (R.strict.monotone hr))
            (R.strict.monotone (by omega)) ha
        rcases B.active_small_or_large (m := m) har with hs | hl
        · exact hs
        · exfalso
          exact hnoswitch r hr (by omega) (mem_filter.mpr ⟨hl, hnext⟩)
    have hsub : Ico (K - L) K ⊆ Instance.markedRounds
        (fun r => b ∈ B.small m S (R.boundary r)) K := by
      intro r hr
      have hr' := mem_Ico.mp hr
      simp only [Instance.markedRounds, mem_filter, mem_range]
      exact ⟨hr'.2, back (K - r) r (by omega) hr'.1⟩
    have hc := card_le_card hsub
    have hcL : (Ico (K - L) K).card = L := by simp; omega
    rw [hcL] at hc
    have hs := R.small_rounds_before_lt hO hL hb
    omega

/-- Lemma 12. Both bounds are proved simultaneously by strong induction on
the round index, from the operational fixed-frontier routine. -/
theorem round_bounds (hm : 0 < m) (hLp : 0 < L)
    (hO : I.Valid m O) (hL : I.FlowBound O L) (K : ℕ) :
    (B.small m S (R.boundary K)).card ≤ 4 * L ∧
    R.boundary (K + 1) - R.boundary K ≤ 4 * L := by
  classical
  induction K using Nat.strong_induction_on with
  | h K ih =>
    have hprev : ∀ k < K, R.boundary (k + 1) - R.boundary k ≤ 4 * L :=
      fun k hk => (ih k hk).2
    have hspan := R.boundary_span (a := K - L) (Nat.sub_le K L) hprev
    have hwin : R.boundary K ≤ R.boundary (K - L) + 4 * L ^ 2 := by
      have hd : K - (K - L) ≤ L := by omega
      have hmul := Nat.mul_le_mul_right (4 * L) hd
      nlinarith
    have hnew := B.eligible_count_bound hLp hwin
    have hturn : ((Ico (K - L) K).biUnion R.switches).card ≤ L := by
      calc
        _ ≤ ∑ r ∈ Ico (K - L) K, (R.switches r).card := card_biUnion_le
        _ ≤ ∑ _r ∈ Ico (K - L) K, 1 := by
          apply sum_le_sum
          intro r _
          exact R.switches_card_le_one r
        _ ≤ L := by simp; omega
    have hcover := card_le_card (R.small_cover hO hL hLp K)
    have hu := card_union_le
      (univ.filter (fun b => R.boundary (K - L) < B.eligible b ∧ B.eligible b ≤ R.boundary K))
      ((Ico (K - L) K).biUnion R.switches)
    have hsmall : (B.small m S (R.boundary K)).card ≤ 4 * L := by omega
    refine ⟨hsmall, (R.round_length_le_small_count hm K).trans ?_⟩
    exact max_le (by omega) hsmall

end Scheduling.SFFRounds
