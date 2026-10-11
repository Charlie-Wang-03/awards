import JSP000404Research.ZeroCarry
import Mathlib.Tactic

/-!
# Counterexamples to the unrestricted historical BoundaryExcess equivalences

The historical statement omitted the geometric arithmetic premise
  ∑ i, q i ≤ n.
Without it, natural-number truncated subtraction loses cancellation.

Concrete counterexample on Fin 1: n=0, b(0)=0, q(0)=2.
Then support(b)=0, floorExcess(b)=0 and floorExcess(q)=1.
Both originally unqualified iff statements are false.

This refutes the overly broad AUXILIARY lemmas, NOT JSP-000404.
The repaired statements in BoundaryExcess.lean explicitly require
the geometrically justified bound ∑q ≤ n.
-/

namespace JSP000404Research

private def excessAuditQ : Fin 1 → ℕ := fun _ => 2
private def excessAuditB : Fin 1 → ℕ := fun _ => 0

private theorem excessAudit_q : floorExcess excessAuditQ = 1 := by
  simp [floorExcess, excessAuditQ]

private theorem excessAudit_b : floorExcess excessAuditB = 0 := by
  simp [floorExcess, excessAuditB]

private theorem excessAudit_support : positiveSupport excessAuditB = 0 := by
  simp [positiveSupport, excessAuditB]

private theorem excessAudit_sum : (∑ i, excessAuditB i) = 0 := by
  simp [excessAuditB]

/-- False without the absent sum-q bound: the weak budget does not
imply the comparison of floor-excess numbers. -/
theorem unrestricted_support_budget_equivalence_refuted :
    ¬ (∀ (q b : Fin 1 → ℕ) (n : ℕ),
      (∑ i, b i) = n →
      (positiveSupport b ≤ n - floorExcess q ↔
        floorExcess q ≤ floorExcess b)) := by
  intro h
  have hiff := h excessAuditQ excessAuditB 0 excessAudit_sum
  have hleft :
      positiveSupport excessAuditB ≤
        0 - floorExcess excessAuditQ := by
    rw [excessAudit_support]
    omega
  have hright := hiff.mp hleft
  rw [excessAudit_q, excessAudit_b] at hright
  omega

/-- False without sum-q ≤ n: the historical strict-failure equivalence
is reversed by the same truncated-subtraction example. -/
theorem unrestricted_support_failure_equivalence_refuted :
    ¬ (∀ (q b : Fin 1 → ℕ) (n : ℕ),
      (∑ i, b i) = n →
      (n - floorExcess q < positiveSupport b ↔
        floorExcess b < floorExcess q)) := by
  intro h
  have hiff := h excessAuditQ excessAuditB 0 excessAudit_sum
  have hright :
      floorExcess excessAuditB < floorExcess excessAuditQ := by
    rw [excessAudit_q, excessAudit_b]
  have hleft := hiff.mpr hright
  rw [excessAudit_q, excessAudit_support] at hleft
  omega

#print axioms unrestricted_support_budget_equivalence_refuted
#print axioms unrestricted_support_failure_equivalence_refuted

end JSP000404Research
