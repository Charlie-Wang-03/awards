
import JSP000404Research.CentreProjectiveBandBudget
import Mathlib.Tactic

/-!
# Closed n+1 projective-band capacity

The direct canonical projective-band BinaryEdgePartition has n+1 coordinates.
CentreProjectiveBandBudget proves at every centre i

  active(i).card <= (n+1) - centreExponent(i).

Therefore the weighted Hansel inequality immediately gives

  sum_i 2^(centreExponent(i)) <= 2^(n+1).

This is intentionally one bit weaker than the final JSP-000404 lower-branch
target.  Its role is structural: the full local-to-global bridge from the
genuine centre quotient exponent to one concrete global binary certificate is
now closed.  All remaining work is isolated to eliminating / paying for the
single extra projective band.
-/

namespace JSP000404Research

open scoped BigOperators

theorem projectiveBand_oneLayer_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤
      2 ^ (n + 1) := by
  have htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P : BinaryEdgePartition V (n + 1) :=
    projectiveBandPartition hp hcap htpos hlam n htop
  let exponent : V → ℕ :=
    fun i => centreExponent (C i) t
  let ell : V → ℕ :=
    fun i => (n + 1) - exponent i
  have hactive :
      ∀ i, (BinaryEdgePartition.active P i).card ≤ ell i := by
    intro i
    dsimp [P, ell, exponent]
    exact projectiveBandPartition_active_card_le_deficit
      hp hcap htpos hlam ht hdelta0 hdelta1 C i
  have hexponent :
      ∀ i, exponent i ≤ n + 1 := by
    intro i
    have h := hactive i
    have hnonneg :
        0 ≤ (BinaryEdgePartition.active P i).card :=
      Nat.zero_le _
    dsimp [ell] at h
    omega
  have hell :
      ∀ i, ell i = (n + 1) - exponent i := by
    intro i
    rfl
  have hcapP :=
    BinaryEdgePartition.cluster_capacity_of_active_le
      P exponent ell hexponent hell hactive
  simpa [exponent] using hcapP

#print axioms projectiveBand_oneLayer_capacity

end JSP000404Research
