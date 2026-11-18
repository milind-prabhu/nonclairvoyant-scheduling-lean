import Scheduling.LayeredForest

namespace Scheduling.LayeredForest
open Finset
attribute [local instance] Classical.propDecidable
variable {jobs work : ℕ} (F : LayeredForest jobs work)

def key (j : Fin jobs) (l : Fin (F.depth j)) : Fin (jobs * work) :=
  finProdFinEquiv (j, ⟨l.val, l.isLt.trans_le (F.depth_le j)⟩)

def vertexLevel (v : Fin (jobs * work)) : ℕ := F.level (job v) (position v)

@[simp] theorem job_key (j : Fin jobs) (l : Fin (F.depth j)) : job (F.key j l) = j := by
  simp [key]

@[simp] theorem position_key (j : Fin jobs) (l : Fin (F.depth j)) :
    (position (F.key j l)).val = l.val := by simp [key]

@[simp] theorem vertexLevel_key (j : Fin jobs) (l : Fin (F.depth j)) :
    F.vertexLevel (F.key j l) = l.val := by
  simp [vertexLevel, key, level, l.isLt]

theorem key_parent {L : ℕ} (v : Fin (jobs * work))
    (hp : 0 < F.vertexLevel v) :
    (F.toInstance L).edge
      (F.key (job v) ⟨F.vertexLevel v - 1, by have := F.level_lt (job v) (position v); unfold vertexLevel at *; omega⟩) v := by
  constructor
  · simp
  · simp only [position_key]
    change F.vertexLevel v - 1 + 1 = F.vertexLevel v
    omega

theorem keyTime_mono {m L : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (j : Fin jobs) :
    Monotone (fun l : Fin (F.depth j) => S (F.key j l)) := by
  have aux : ∀ b, ∀ hb : b < F.depth j, ∀ a, ∀ ha : a < F.depth j,
      a ≤ b → S (F.key j ⟨a, ha⟩) ≤ S (F.key j ⟨b, hb⟩) := by
    intro b
    induction b with
    | zero =>
      intro hb a ha hab
      have : a = 0 := by omega
      subst a
      rfl
    | succ b ih =>
      intro hb a ha hab
      by_cases he : a = b + 1
      · subst a; rfl
      · have hb' : b < F.depth j := by omega
        have hi := ih hb' a ha (by omega)
        have hedge : (F.toInstance L).edge (F.key j ⟨b, hb'⟩) (F.key j ⟨b + 1, hb⟩) := by
          constructor
          · simp
          · change (position (F.key j ⟨b, hb'⟩)).val + 1 =
              F.vertexLevel (F.key j ⟨b + 1, hb⟩)
            simp
        exact hi.trans (hS.precedence hedge).le
  intro a b hab
  exact aux b.val b.isLt a.val a.isLt hab

/-- This is the property supplied by hidden-key selection: the key is
processed in the last slot used by its layer. -/
def KeyLast (S : Assignment (vertices := jobs * work)) : Prop :=
  ∀ v, S v ≤ S (F.key (job v) ⟨F.vertexLevel v, F.level_lt (job v) (position v)⟩)

theorem earlier_layer_before_parent {m L : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    {u v : Fin (jobs * work)} (hj : job u = job v)
    (hl : F.vertexLevel u < F.vertexLevel v) :
    ∃ p, (F.toInstance L).edge p v ∧ S u ≤ S p := by
  have hp : 0 < F.vertexLevel v := by omega
  let p := F.key (job v) ⟨F.vertexLevel v - 1, by
    have := F.level_lt (job v) (position v); change F.vertexLevel v < F.depth (job v) at this; omega⟩
  refine ⟨p, F.key_parent v hp, ?_⟩
  have hk := hkey u
  have hu : F.vertexLevel u < F.depth (job v) := by
    rw [← hj]; exact F.level_lt (job u) (position u)
  have he : F.key (job u) ⟨F.vertexLevel u, F.level_lt (job u) (position u)⟩ =
      F.key (job v) ⟨F.vertexLevel u, hu⟩ := by
    apply congrArg finProdFinEquiv
    exact Prod.ext hj (Fin.ext rfl)
  rw [he] at hk
  exact hk.trans (F.keyTime_mono hS (job v) (show (⟨F.vertexLevel u, hu⟩ : Fin (F.depth (job v))) ≤
    ⟨F.vertexLevel v - 1, by have := F.level_lt (job v) (position v); unfold vertexLevel at *; omega⟩ by
      change F.vertexLevel u ≤ F.vertexLevel v - 1; omega))

theorem layer_execution_order {m L : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    {u v : Fin (jobs * work)} (hj : job u = job v)
    (hl : F.vertexLevel u < F.vertexLevel v) : S u < S v := by
  obtain ⟨p, hp, hu⟩ := F.earlier_layer_before_parent hS hkey hj hl
  exact hu.trans_lt (hS.precedence hp)

theorem ready_same_layer {m L t : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    {u v : Fin (jobs * work)} (hj : job u = job v)
    (hu : (F.toInstance L).Ready S t u) (hv : (F.toInstance L).Ready S t v) :
    F.vertexLevel u = F.vertexLevel v := by
  rcases lt_trichotomy (F.vertexLevel u) (F.vertexLevel v) with h | h | h
  · obtain ⟨p, hp, hup⟩ := F.earlier_layer_before_parent hS hkey hj h
    have := hv.2.2 p hp
    have := hu.2.1
    omega
  · exact h
  · obtain ⟨p, hp, hvp⟩ := F.earlier_layer_before_parent hS hkey hj.symm h
    have := hu.2.2 p hp
    have := hv.2.1
    omega

theorem simultaneous_same_layer {m L : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    {u v : Fin (jobs * work)} (hj : job u = job v) (ht : S u = S v) :
    F.vertexLevel u = F.vertexLevel v := by
  rcases lt_trichotomy (F.vertexLevel u) (F.vertexLevel v) with h | h | h
  · have := F.layer_execution_order hS hkey hj h; omega
  · exact h
  · have := F.layer_execution_order hS hkey hj.symm h; omega

noncomputable def layerVertices (j : Fin jobs) (l : ℕ) : Finset (Fin (jobs * work)) :=
  univ.filter (fun v => job v = j ∧ F.vertexLevel v = l)

theorem ready_card_le_width {m L t W : ℕ} {S : Assignment (vertices := jobs * work)}
    (hS : (F.toInstance L).Valid m S) (hkey : F.KeyLast S)
    (hwidth : ∀ j l, (F.layerVertices j l).card ≤ W) (j : Fin jobs) :
    (univ.filter (fun v => job v = j ∧ (F.toInstance L).Ready S t v)).card ≤ W := by
  classical
  let R := univ.filter (fun v => job v = j ∧ (F.toInstance L).Ready S t v)
  by_cases hR : R.Nonempty
  · obtain ⟨v, hv⟩ := hR
    have hv' := (mem_filter.mp hv).2
    have hsub : R ⊆ F.layerVertices j (F.vertexLevel v) := by
      intro u hu
      have hu' := (mem_filter.mp hu).2
      exact mem_filter.mpr ⟨mem_univ _, hu'.1,
        F.ready_same_layer hS hkey (hu'.1.trans hv'.1.symm) hu'.2 hv'.2⟩
    exact (card_le_card hsub).trans (hwidth _ _)
  · have he : R = ∅ := not_nonempty_iff_eq_empty.mp hR
    change R.card ≤ W
    rw [he, card_empty]
    omega

end Scheduling.LayeredForest
