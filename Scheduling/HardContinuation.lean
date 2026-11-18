import Scheduling.AppendContinuation

namespace Scheduling.HardFamily
attribute [local instance] Classical.propDecidable
variable {m c L jobs vertices : ℕ}

/-- After any fixed preceding instance, some member of the same finite
general family still forces the target flow. This does not assume that
the preceding jobs have completed. -/
theorem general_hard_after (hm : 2 ≤ m) (hc : 0 < c) (hL : 0 < L)
    (heven : 2 * (L / 2) = L) (hcL : 16 * c ≤ L) (hcm : 2 * c ≤ m)
    (A : DeterministicScheduler m) (I : Instance jobs vertices) (d : ℕ) :
    ∃ P ∈ general (c * (c * (m * L))) m L (by omega) hL,
      c * L ≤ (I.append (P.toInstance L (Nat.mul_pos (by omega) hL)) d).maxFlow
        (A.schedule (I.append (P.toInstance L (Nat.mul_pos (by omega) hL)) d)) := by
  obtain ⟨P, hP, hbad⟩ := general_hard hm hc hL heven hcL hcm (A.continuation I d)
  exact ⟨P, hP, hbad.trans (A.continuation_flow_le I d _)⟩

theorem batched_hard_after (hm : 2 ≤ m) (hc : 0 < c) (hL : 0 < L)
    (heven : 2 * (L / 2) = L) (hcm : 2 * c ≤ m) (hscale : L = 8 * c * 5 ^ c)
    (A : DeterministicScheduler m) (I : Instance jobs vertices) (d : ℕ) :
    ∃ P ∈ batched (c * (m * L)) m L (by omega) hL,
      c * L ≤ (I.append (P.toInstance L (Nat.mul_pos (by omega) hL)) d).maxFlow
        (A.schedule (I.append (P.toInstance L (Nat.mul_pos (by omega) hL)) d)) := by
  obtain ⟨P, hP, hbad⟩ := batched_hard hm hc hL heven hcm hscale (A.continuation I d)
  exact ⟨P, hP, hbad.trans (A.continuation_flow_le I d _)⟩

end Scheduling.HardFamily
