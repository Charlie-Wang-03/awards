import JSP000404Research.ElevenPhaseCNFModel
import JSP000404Research.ElevenPhaseSATHelpers

/-! A generic semantic proof for the unary sequential counters in the CNF. -/

namespace JSP000404Research.ElevenPhase

theorem sequentialClauses_satisfied (v : Sat.Valuation) (input : ℕ → Bool)
    (inputVar : ℕ → ℕ) (offset count limit : ℕ) (hcount : 0 < count)
    (hinput : ∀ i, i < count → (v (inputVar i) ↔ input i = true))
    (hcounter : ∀ i j, i < count → j ≤ limit →
      (v (offset + i * (limit + 1) + j) ↔ j + 1 ≤ prefixCount input (i + 1)))
    (hbound : prefixCount input count ≤ limit) :
    v.satisfies_fmla (sequentialClauses inputVar offset count limit) := by
  classical
  constructor
  intro clause hc
  unfold sequentialClauses at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨j, hj, hc⟩ := List.mem_flatMap.mp hc
    have hi : i < count := List.mem_range.mp hi
    have hjle : j ≤ limit := by have := List.mem_range.mp hj; omega
    rcases List.mem_append.mp hc with hprev | hstep
    · by_cases hi0 : i = 0
      · rw [if_pos hi0] at hprev
        exact (List.not_mem_nil hprev).elim
      · rw [if_neg hi0] at hprev
        have hprev := List.mem_singleton.mp hprev
        subst clause
        change v (offset + (i - 1) * (limit + 1) + j) →
          ¬v (offset + i * (limit + 1) + j) → False
        intro hp hn
        apply hn
        apply (hcounter i j hi hjle).mpr
        have hpre : i - 1 < count := by omega
        have hpv := (hcounter (i - 1) j hpre hjle).mp hp
        have hstep := prefixCount_succ input (i - 1)
        have hnext := prefixCount_succ input i
        have heq : i - 1 + 1 = i := by omega
        rw [heq] at hpv hstep
        omega
    · by_cases hj0 : j = 0
      · rw [if_pos hj0] at hstep
        have hstep := List.mem_singleton.mp hstep
        subst clause
        change v (inputVar i) → ¬v (offset + i * (limit + 1)) → False
        intro hp hn
        apply hn
        apply (hcounter i 0 hi (by omega)).mpr
        have hv := (hinput i hi).mp hp
        have hstep := prefixCount_succ input i
        simp only [hv, ↓reduceIte] at hstep
        omega
      · by_cases hi0 : i = 0
        · rw [if_neg hj0, if_pos hi0] at hstep
          exact (List.not_mem_nil hstep).elim
        · rw [if_neg hj0, if_neg hi0] at hstep
          have hstep := List.mem_singleton.mp hstep
          subst clause
          change v (inputVar i) → v (offset + (i - 1) * (limit + 1) + j - 1) →
            ¬v (offset + i * (limit + 1) + j) → False
          intro hp hprev hn
          apply hn
          apply (hcounter i j hi hjle).mpr
          have hv := (hinput i hi).mp hp
          have heq : offset + (i - 1) * (limit + 1) + j - 1 =
              offset + (i - 1) * (limit + 1) + (j - 1) := by omega
          rw [heq] at hprev
          have hpre : i - 1 < count := by omega
          have hjpre : j - 1 ≤ limit := by omega
          have hpv := (hcounter (i - 1) (j - 1) hpre hjpre).mp hprev
          have hstep := prefixCount_succ input (i - 1)
          have hnext := prefixCount_succ input i
          have hi' : i - 1 + 1 = i := by omega
          rw [hi'] at hpv hstep
          simp only [hv, ↓reduceIte] at hnext
          omega
  · have hc := List.mem_singleton.mp hc
    subst clause
    change v (offset + (count - 1) * (limit + 1) + limit) → False
    intro hp
    have hcpre : count - 1 < count := by omega
    have h := (hcounter (count - 1) limit hcpre le_rfl).mp hp
    have heq : count - 1 + 1 = count := by omega
    rw [heq] at h
    omega

#print axioms sequentialClauses_satisfied

end JSP000404Research.ElevenPhase
