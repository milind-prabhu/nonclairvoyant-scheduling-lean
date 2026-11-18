import Scheduling.HardContinuation
import Mathlib.Data.List.Induction

namespace Scheduling
open Finset
attribute [local instance] Classical.propDecidable

/-- A finite instance together with its dimensions, for concatenations
whose number of jobs grows with the sampled word. -/
structure PackedInstance where
  jobs : ℕ
  vertices : ℕ
  graph : Instance jobs vertices

namespace PackedInstance

def empty : PackedInstance where
  jobs := 0
  vertices := 0
  graph := {
    owner := Fin.elim0
    release := Fin.elim0
    edge := fun _ _ => False
    same_job := by intros; contradiction
    rank := Fin.elim0
    rank_increases := by intros; contradiction
    nonempty_job := by intro j; exact Fin.elim0 j }

def append (P Q : PackedInstance) (d : ℕ) : PackedInstance :=
  ⟨P.jobs + Q.jobs, P.vertices + Q.vertices, P.graph.append Q.graph d⟩

noncomputable def onlineFlow (P : PackedInstance) {m : ℕ} (A : DeterministicScheduler m) : ℕ :=
  P.graph.maxFlow (A.schedule P.graph)

theorem empty_offline (m B : ℕ) : ∃ O, empty.graph.Valid m O ∧ empty.graph.FlowBound O B := by
  dsimp only [empty]
  refine ⟨fun v => Fin.elim0 v, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v; exact Fin.elim0 v
  · intro u; exact Fin.elim0 u
  · intro t; simp
  · intro v; exact Fin.elim0 v

end PackedInstance

namespace InstanceSequence
variable {α : Type*}

/-- Append successive copies at offsets `0,D,2D,...`. -/
def concatenate (G : α → PackedInstance) (D : ℕ) (xs : List α) : PackedInstance :=
  xs.reverseRecOn PackedInstance.empty (fun ys x P => P.append (G x) (ys.length * D))

@[simp] theorem concatenate_nil (G : α → PackedInstance) (D : ℕ) :
    concatenate G D [] = PackedInstance.empty := by simp [concatenate]

@[simp] theorem concatenate_snoc (G : α → PackedInstance) (D : ℕ) (xs : List α) (x : α) :
    concatenate G D (xs ++ [x]) = (concatenate G D xs).append (G x) (xs.length * D) := by
  simp [concatenate]

theorem release_gap (G : α → PackedInstance) (D B : ℕ)
    (hlocal : ∀ x j, (G x).graph.release j + B ≤ D) (xs : List α) :
    ∀ j, (concatenate G D xs).graph.release j + B ≤ xs.length * D := by
  induction xs using List.reverseRecOn with
  | nil => rw [concatenate_nil]; intro j; exact Fin.elim0 j
  | append_singleton xs x ih =>
    rw [concatenate_snoc]
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro j
    · have hj := ih j
      simp only [PackedInstance.append, Instance.append, Fin.addCases_left,
        List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
      omega
    · have hj := hlocal x j
      simp only [PackedInstance.append, Instance.append, Fin.addCases_right,
        List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
      omega

theorem offline (G : α → PackedInstance) (D B m : ℕ)
    (hlocal : ∀ x, ∃ O, (G x).graph.Valid m O ∧ (G x).graph.FlowBound O B)
    (hgap : ∀ x j, (G x).graph.release j + B ≤ D) (xs : List α) :
    ∃ O, (concatenate G D xs).graph.Valid m O ∧ (concatenate G D xs).graph.FlowBound O B := by
  induction xs using List.reverseRecOn with
  | nil => rw [concatenate_nil]; exact PackedInstance.empty_offline m B
  | append_singleton xs x ih =>
    rw [concatenate_snoc]
    exact (concatenate G D xs).graph.append_offline (G x).graph ih (hlocal x)
      (release_gap G D B hgap xs)

theorem outForest (G : α → PackedInstance) (D : ℕ)
    (hlocal : ∀ x u v w, (G x).graph.edge u w → (G x).graph.edge v w → u = v) (xs : List α) :
    ∀ u v w, (concatenate G D xs).graph.edge u w → (concatenate G D xs).graph.edge v w → u = v := by
  induction xs using List.reverseRecOn with
  | nil => rw [concatenate_nil]; intro u; exact Fin.elim0 u
  | append_singleton xs x ih =>
    rw [concatenate_snoc]
    exact (concatenate G D xs).graph.append_outForest (G x).graph _ ih (hlocal x)

theorem batched_releases (G : α → PackedInstance) (D L : ℕ) (hD : L ∣ D)
    (hlocal : ∀ x j, L ∣ (G x).graph.release j) (xs : List α) :
    ∀ j, L ∣ (concatenate G D xs).graph.release j := by
  induction xs using List.reverseRecOn with
  | nil => rw [concatenate_nil]; intro j; exact Fin.elim0 j
  | append_singleton xs x ih =>
    rw [concatenate_snoc]
    exact (concatenate G D xs).graph.append_batched_releases (G x).graph ih (hlocal x)
      (dvd_mul_of_dvd_right hD _)

theorem optimum_ge (G : α → PackedInstance) (D L : ℕ) {m : ℕ} (hm : 0 < m)
    (hlocal : ∀ x, L ≤ (G x).graph.optimum m hm) (xs : List α) (hne : xs ≠ []) :
    L ≤ (concatenate G D xs).graph.optimum m hm := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton xs x _ =>
    rw [concatenate_snoc]
    exact (hlocal x).trans ((concatenate G D xs).graph.append_optimum_ge_right (G x).graph hm _)

theorem bad_persists (G : α → PackedInstance) (D F : ℕ) {m : ℕ} (A : DeterministicScheduler m)
    (hgap : ∀ x j, (G x).graph.release j + F ≤ D) (xs : List α) (x : α)
    (hbad : F ≤ (concatenate G D xs).onlineFlow A) :
    F ≤ (concatenate G D (xs ++ [x])).onlineFlow A := by
  rw [concatenate_snoc]
  exact A.append_flow_lower (concatenate G D xs).graph (G x).graph hbad (release_gap G D F hgap xs)

theorem exists_bad_next (G : α → PackedInstance) (D F : ℕ) {m : ℕ} (A : DeterministicScheduler m)
    (hhard : ∀ P : PackedInstance, ∀ d, ∃ x, F ≤ (P.append (G x) d).onlineFlow A)
    (xs : List α) : ∃ x, F ≤ (concatenate G D (xs ++ [x])).onlineFlow A := by
  obtain ⟨x, hx⟩ := hhard (concatenate G D xs) (xs.length * D)
  exact ⟨x, by simpa only [concatenate_snoc] using hx⟩

end InstanceSequence
end Scheduling
