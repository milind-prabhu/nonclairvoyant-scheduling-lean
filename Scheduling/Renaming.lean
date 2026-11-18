import Scheduling.SFFNonclairvoyant

namespace Scheduling
open Finset

def renameKey (f : ℕ → ℕ) (x : ℕ ×ₗ ℕ) : ℕ ×ₗ ℕ := toLex ((ofLex x).1, f (ofLex x).2)
def renameObservation (f : ℕ → ℕ) (Q : FIFOObservation) : FIFOObservation := Q.image (renameKey f)

theorem renameKey_strictMono {f : ℕ → ℕ} (hf : StrictMono f) : StrictMono (renameKey f) := by
  intro x y h
  rw [Prod.Lex.lt_iff] at h ⊢
  rcases h with h | ⟨he, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨he, hf h⟩

theorem fifoPolicy_rename {f : ℕ → ℕ} (hf : StrictMono f) (m : ℕ) (Q : FIFOObservation) :
    fifoPolicy m (renameObservation f Q) = (fifoPolicy m Q).image f := by
  unfold fifoPolicy renameObservation
  rw [← Packing.slice_image _ _ (renameKey_strictMono hf), image_image, image_image]
  rfl

namespace PublicSnapshot

def rename (Q : PublicSnapshot) (f : ℕ → ℕ) : PublicSnapshot where
  support := Q.support
  ready := fun b => (Q.ready b).image f
  supported := by intro b; simpa only [image_nonempty] using Q.supported b

theorem rename_small (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : Function.Injective f) (m : ℕ) :
    (Q.rename f).small m = Q.small m := by
  simp only [small, rename, card_image_of_injective _ hf]

theorem rename_large (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : Function.Injective f) (m : ℕ) :
    (Q.rename f).large m = Q.large m := by
  simp only [large, rename, card_image_of_injective _ hf]

theorem rename_smallFront (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : Function.Injective f) (m : ℕ) :
    (Q.rename f).smallFront m = (Q.smallFront m).image f := by
  unfold smallFront
  rw [Q.rename_small hf, biUnion_image]
  rfl

theorem rename_filler (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : Function.Injective f) (m : ℕ) :
    (Q.rename f).filler m = Q.filler m := by
  unfold filler
  simp only [Q.rename_large hf]

theorem rename_fillerFront (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : Function.Injective f) (m : ℕ) :
    (Q.rename f).fillerFront m = (Q.fillerFront m).image f := by
  unfold fillerFront
  rw [Q.rename_filler hf]
  cases Q.filler m <;> simp only [rename, image_empty]

theorem rename_duration (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : Function.Injective f) (m : ℕ) :
    (Q.rename f).duration m = Q.duration m := by
  unfold duration
  rw [Q.rename_smallFront hf, card_image_of_injective _ hf]

theorem rename_action (Q : PublicSnapshot) {f : ℕ → ℕ} (hf : StrictMono f) (m k : ℕ) :
    (Q.rename f).action m k = (Q.action m k).image f := by
  unfold action
  rw [Q.rename_smallFront hf.injective, Q.rename_fillerFront hf.injective,
    Q.rename_duration hf.injective, ← Packing.slot_image _ _ hf,
    card_image_of_injective _ hf.injective, image_union]
  split_ifs <;> simp only [Packing.slice_image _ _ hf, image_empty]

end PublicSnapshot

def renameMemory (f : ℕ → ℕ) (state : SFFMemory) : SFFMemory :=
  state.map (fun plan => (plan.1.rename f, plan.2))

theorem sffStep_rename {f : ℕ → ℕ} (hf : StrictMono f) (m t : ℕ)
    (Q : PublicSnapshot) (state : SFFMemory) :
    sffStep m t (Q.rename f) (renameMemory f state) =
      ((sffStep m t Q state).1.image f, renameMemory f (sffStep m t Q state).2) := by
  cases state with
  | none =>
    simp only [sffStep, renameMemory, Option.map_none, Option.getD_none,
      PublicSnapshot.rename_action _ hf, PublicSnapshot.rename_duration _ hf.injective]
    split_ifs <;> rfl
  | some plan =>
    rcases plan with ⟨R, k⟩
    simp only [sffStep, renameMemory, Option.map_some, Option.getD_some,
      PublicSnapshot.rename_action _ hf, PublicSnapshot.rename_duration _ hf.injective]
    split_ifs <;> rfl

theorem sffPolicy_state_rename {f : ℕ → ℕ} (hf : StrictMono f) (m : ℕ)
    (history : ℕ → PublicSnapshot) (t : ℕ) :
    (sffPolicy m).state (fun u => (history u).rename f) t =
      renameMemory f ((sffPolicy m).state history t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [OnlinePolicy.state]
    rw [ih]
    exact congrArg Prod.snd (sffStep_rename hf m t (history t) _)

theorem sffPolicy_decision_rename {f : ℕ → ℕ} (hf : StrictMono f) (m : ℕ)
    (history : ℕ → PublicSnapshot) (t : ℕ) :
    (sffPolicy m).decision (fun u => (history u).rename f) t =
      ((sffPolicy m).decision history t).image f := by
  unfold OnlinePolicy.decision
  rw [sffPolicy_state_rename hf]
  exact congrArg Prod.fst (sffStep_rename hf m t (history t) _)

theorem batchObservation_rename (f : ℕ → ℕ) (L t : ℕ) (Q : FIFOObservation) :
    batchObservation L t (renameObservation f Q) = (batchObservation L t Q).rename f := by
  apply PublicSnapshot.ext_ready
  funext b
  ext n
  rw [mem_batchObservation]
  change _ ↔ n ∈ ((batchObservation L t Q).ready b).image f
  constructor
  · rintro ⟨x, hx, hb, he, hn⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨(ofLex y).2,
      (mem_batchObservation _ _ _ _ _).mpr ⟨y, hy, hb, he, rfl⟩, hn⟩
  · intro hn
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
    obtain ⟨y, hy, hb, he, rfl⟩ := (mem_batchObservation _ _ _ _ _).mp hv
    exact ⟨renameKey f y, mem_image.mpr ⟨y, hy, rfl⟩, hb, he, rfl⟩

theorem sffRawPolicy_decision_rename {f : ℕ → ℕ} (hf : StrictMono f) (m L : ℕ)
    (history : ℕ → FIFOObservation) (t : ℕ) :
    (sffRawPolicy m L).decision (fun u => renameObservation f (history u)) t =
      ((sffRawPolicy m L).decision history t).image f := by
  rw [sffRawPolicy_decision, sffRawPolicy_decision]
  simp_rw [batchObservation_rename]
  exact sffPolicy_decision_rename hf m _ t

end Scheduling
