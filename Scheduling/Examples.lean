import Scheduling.SFFConstruction
import Scheduling.FIFOConstruction

namespace Scheduling.Examples

/-- A three-vertex chain alongside a three-vertex fork, both released at 0. -/
def forkAndChain : Instance 2 6 where
  owner := fun v => if v.val < 3 then 0 else 1
  release := fun _ => 0
  edge := fun u v => (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 2) ∨
    (u.val = 3 ∧ v.val = 4) ∨ (u.val = 3 ∧ v.val = 5)
  same_job := by decide
  rank := Fin.val
  rank_increases := by decide
  nonempty_job := by decide

instance : DecidableRel forkAndChain.edge := by
  intro u v
  dsimp [forkAndChain]
  infer_instance

def sampleSchedule : Assignment (vertices := 6) := forkAndChain.sffSchedule 2 3 (by decide)

theorem sample_valid : forkAndChain.Valid 2 sampleSchedule :=
  forkAndChain.sffSchedule_valid (by decide) (by decide)

-- Runtime regression: the chain and fork both complete at time 9. This
-- checks compiled execution output, while `sample_valid` uses the general
-- kernel-checked theorem. It is not a native-evaluation proof shortcut.
/-- info: [6, 7, 8, 6, 7, 8] -/
#guard_msgs in
#eval (List.finRange 6).map sampleSchedule

/-- info: [0, 1, 2, 0, 1, 2] -/
#guard_msgs in
#eval (List.finRange 6).map (forkAndChain.fifoSchedule 2 (by decide))

end Scheduling.Examples
