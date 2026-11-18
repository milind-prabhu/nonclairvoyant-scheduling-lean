import Scheduling.FrontierProgress

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs vertices batches : ℕ}

/-- Canonical batching into half-open windows of length 2L. Empty windows
are allowed. Indices are attached to jobs, so predecessors stay in a batch. -/
structure Batching (I : Instance jobs vertices) (L batches : ℕ) where
  index : Fin jobs → Fin batches
  lower : ∀ j, 2 * L * (index j).val ≤ I.release j
  upper : ∀ j, I.release j < 2 * L * ((index j).val + 1)

namespace Batching
variable {I : Instance jobs vertices} {L : ℕ} (B : Batching I L batches)

def vertexBatch (v : Fin vertices) : Fin batches := B.index (I.owner v)
def eligible (_B : Batching I L batches) (b : Fin batches) : ℕ := 2 * L * (b.val + 1)
noncomputable def batchVertices (b : Fin batches) : Finset (Fin vertices) :=
  univ.filter (fun v => B.vertexBatch v = b)
noncomputable def frontier (S : Assignment (vertices := vertices)) (t : ℕ) (b : Fin batches) : Finset (Fin vertices) :=
  univ.filter (fun v => B.vertexBatch v = b ∧ I.Ready S t v)
def Active (S : Assignment (vertices := vertices)) (t : ℕ) (b : Fin batches) : Prop :=
  B.eligible b ≤ t ∧ ∃ v, B.vertexBatch v = b ∧ t ≤ S v
noncomputable def small (m : ℕ) (S : Assignment (vertices := vertices)) (t : ℕ) : Finset (Fin batches) :=
  univ.filter (fun b => B.Active S t b ∧ (B.frontier S t b).card ≤ m)
noncomputable def large (m : ℕ) (S : Assignment (vertices := vertices)) (t : ℕ) : Finset (Fin batches) :=
  univ.filter (fun b => B.Active S t b ∧ m < (B.frontier S t b).card)

theorem predecessor_closed (b : Fin batches) : I.PredecessorClosed (B.batchVertices b) := by
  intro u v hv he
  have ho := I.same_job he
  have h := (mem_filter.mp hv).2
  exact mem_filter.mpr ⟨mem_univ _, by simpa [vertexBatch, ho] using h⟩

theorem released_by_eligible {v : Fin vertices} {b : Fin batches} (hv : B.vertexBatch v = b) :
    I.release (I.owner v) < B.eligible b := by
  have h := B.upper (I.owner v)
  change B.index (I.owner v) = b at hv
  rw [hv] at h
  exact h

theorem active_small_or_large {m : ℕ} {S : Assignment (vertices := vertices)} {t : ℕ} {b : Fin batches}
    (ha : B.Active S t b) : b ∈ B.small m S t ∨ b ∈ B.large m S t := by
  by_cases h : (B.frontier S t b).card ≤ m
  · exact Or.inl (mem_filter.mpr ⟨mem_univ _, ha, h⟩)
  · exact Or.inr (mem_filter.mpr ⟨mem_univ _, ha, by omega⟩)

theorem small_large_disjoint (m : ℕ) (S : Assignment (vertices := vertices)) (t : ℕ) :
    Disjoint (B.small m S t) (B.large m S t) := by
  apply disjoint_left.mpr
  intro b hs hl
  have hs' := (mem_filter.mp hs).2.2
  have hl' := (mem_filter.mp hl).2.2
  omega

theorem active_at_earlier {S : Assignment (vertices := vertices)} {a t : ℕ} {b : Fin batches}
    (ha : B.eligible b ≤ a) (hat : a ≤ t) (ht : B.Active S t b) : B.Active S a b := by
  obtain ⟨v, hv, hs⟩ := ht.2
  exact ⟨ha, v, hv, by omega⟩

theorem eligible_positive (hL : 0 < L) (b : Fin batches) : 0 < B.eligible b := by
  dsimp [eligible]
  positivity

theorem batch_work_bound {m : ℕ} {O : Assignment (vertices := vertices)}
    (hO : I.Valid m O) (hL : I.FlowBound O L) (b : Fin batches) :
    (B.batchVertices b).card ≤ 3 * m * L := by
  classical
  let a := 2 * L * b.val
  let z := 2 * L * (b.val + 1)
  have h := card_le_slots O m a (z + L) (B.batchVertices b) hO.capacity (by
    intro v hv
    have hi := (mem_filter.mp hv).2
    have hl := B.lower (I.owner v)
    have hu := B.upper (I.owner v)
    change 2 * L * (B.vertexBatch v).val ≤ _ at hl
    change _ < 2 * L * ((B.vertexBatch v).val + 1) at hu
    rw [hi] at hl hu
    have hr := hO.release v
    have hf := hL v
    exact ⟨by dsimp [a]; omega, by dsimp [z]; omega⟩)
  have hz : z = a + 2 * L := by dsimp [z, a]; ring
  have he : z + L - a = 3 * L := by rw [hz]; omega
  rw [he] at h
  nlinarith

/-- The number of batch eligibility times in a bounded interval. The +1
allows either position of the endpoints relative to the eligibility grid. -/
theorem eligible_count_bound {u v : ℕ} (hL : 0 < L) (hspan : v ≤ u + 4 * L ^ 2) :
    (univ.filter (fun b : Fin batches => u < B.eligible b ∧ B.eligible b ≤ v)).card ≤ 2 * L + 1 := by
  classical
  let A := univ.filter (fun b : Fin batches => u < B.eligible b ∧ B.eligible b ≤ v)
  let lo := u / (2 * L)
  have hmod := Nat.mod_lt u (show 0 < 2 * L by omega)
  have hdiv := Nat.mod_add_div u (2 * L)
  have hsub : A.image Fin.val ⊆ Ico lo (lo + (2 * L + 1)) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have ht := (mem_filter.mp hb).2
    dsimp [eligible] at ht
    apply mem_Ico.mpr
    constructor
    · dsimp [lo]
      by_contra hn
      have hm := Nat.mul_le_mul_left (2 * L) (show b.val + 1 ≤ u / (2 * L) by omega)
      have hu : 2 * L * (u / (2 * L)) ≤ u := by omega
      exact Nat.not_lt_of_ge (hm.trans hu) ht.1
    · dsimp [lo]
      by_contra hn
      have hm := Nat.mul_le_mul_left (2 * L)
        (show u / (2 * L) + (2 * L + 1) ≤ b.val by omega)
      nlinarith
  have he : (A.image Fin.val).card = A.card := card_image_of_injective A Fin.val_injective
  have hc := card_le_card hsub
  rw [he] at hc
  simpa [A, Nat.card_Ico] using hc

/-- Denominator-free eligibility counting, for interference over any interval. -/
theorem eligible_count_scaled {u v : ℕ} (hL : 0 < L) (huv : u ≤ v) :
    2 * L * (univ.filter (fun b : Fin batches => u < B.eligible b ∧ B.eligible b ≤ v)).card
      ≤ v - u + 2 * L := by
  classical
  let A := univ.filter (fun b : Fin batches => u < B.eligible b ∧ B.eligible b ≤ v)
  have hd : 0 < 2 * L := by omega
  have hu := Nat.mod_add_div u (2 * L)
  have hv := Nat.mod_add_div v (2 * L)
  have hum := Nat.mod_lt u hd
  have hvm := Nat.mod_lt v hd
  have hsub : A.image Fin.val ⊆ Ico (u / (2 * L)) (v / (2 * L)) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have ht := (mem_filter.mp hb).2
    change u < 2 * L * (b.val + 1) ∧ 2 * L * (b.val + 1) ≤ v at ht
    apply mem_Ico.mpr
    constructor
    · by_contra hn
      have hm := Nat.mul_le_mul_left (2 * L) (show b.val + 1 ≤ u / (2 * L) by omega)
      have hle : 2 * L * (u / (2 * L)) ≤ u := by omega
      exact Nat.not_lt_of_ge (hm.trans hle) ht.1
    · have hle : b.val + 1 ≤ v / (2 * L) := by
        apply (Nat.le_div_iff_mul_le hd).mpr
        simpa [Nat.mul_comm] using ht.2
      omega
  have hc := card_le_card hsub
  rw [card_image_of_injective A Fin.val_injective, Nat.card_Ico] at hc
  have hmul := Nat.mul_le_mul_left (2 * L) hc
  have hq : u / (2 * L) ≤ v / (2 * L) := Nat.div_le_div_right huv
  have hsum := Nat.sub_add_cancel hq
  have hscaled := congrArg (fun n => 2 * L * n) hsum
  have hvu : v - u + u = v := Nat.sub_add_cancel huv
  try dsimp only at hscaled
  rw [Nat.mul_add] at hscaled
  change 2 * L * A.card ≤ _
  omega

end Batching

/-- Operational round specification for SFF. There is no small-batch-count,
round-length upper bound, depth-drop assumption, or backlog bound in this
structure. Its fields describe the paper's fixed-frontier round routine. -/
structure SFFRounds {I : Instance jobs vertices} {L : ℕ}
    (B : Batching I L batches) (m : ℕ) (S : Assignment (vertices := vertices)) where
  boundary : ℕ → ℕ
  starts_zero : boundary 0 = 0
  strict : StrictMono boundary
  clear_small : ∀ k b, b ∈ B.small m S (boundary k) →
    ∀ v, B.vertexBatch v = b → I.Ready S (boundary k) v → S v < boundary (k + 1)
  filler : ℕ → Option (Fin batches)
  large_service : ∀ k v, boundary k ≤ S v → S v < boundary (k + 1) →
    B.vertexBatch v ∈ B.large m S (boundary k) → filler k = some (B.vertexBatch v)
  length_eq : ∀ k, boundary (k + 1) - boundary k =
    max 1 (((univ.filter (fun v => B.vertexBatch v ∈ B.small m S (boundary k) ∧
      I.Ready S (boundary k) v)).card + m - 1) / m)
  eligible_service : ∀ v, B.eligible (B.vertexBatch v) ≤ S v
  packed : ∀ k t, boundary k ≤ t → t + 1 < boundary (k + 1) →
    (univ.filter (fun v => S v = t)).card = m
  fill_last : ∀ k, (B.large m S (boundary k)).Nonempty →
    ∀ t, boundary k ≤ t → t < boundary (k + 1) →
      (univ.filter (fun v => S v = t)).card = m
  service_scope : ∀ k v, boundary k ≤ S v → S v < boundary (k + 1) →
    (B.vertexBatch v ∈ B.small m S (boundary k) ∧ I.Ready S (boundary k) v) ∨
      filler k = some (B.vertexBatch v)
  filler_oldest : ∀ k b c, filler k = some b → c ∈ B.large m S (boundary k) →
    B.eligible b ≤ B.eligible c

end Scheduling
