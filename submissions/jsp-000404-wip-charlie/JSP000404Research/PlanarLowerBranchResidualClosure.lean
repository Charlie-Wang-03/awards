import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.ResidualActiveDrop
import JSP000404Research.ResidualRecolor
import Mathlib.Tactic

/-!
# All-cardinality planar lower-branch closure from residual absorption

This module assembles the genuine planar representation layer with the
residual-recolouring Kraft outlet.

For a finite injective planar configuration under the Sendov normalization

  t = n + delta,  0 <= delta < 1,

the generic-projection standard residual colouring satisfies the one-loss
profile bound

  card(active(v)) <= n - centreExponent(v) + 1.

Thus the full lower-branch dyadic capacity follows as soon as two residual
facts are available:

* every vertex which actually uses the extra one unit is incident to the
  residual colour;
* the residual colour admits an absorbed safe recolouring into the first n
  colours.

The theorem below is arbitrary-cardinality: no six-point hypothesis or finite
terminal classification is used.  It isolates the remaining global residual
certificate needed for CP-1.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

theorem planar_lowerBranch_capacity_of_absorbed_residual
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hbadResidual :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let B :=
        standardResidualColoring D n hwidth
      let exponent : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (C i) t
      ∀ i,
        n - exponent i < (active B i).card →
          residualCoord n ∈ active B i)
    (R :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      ResidualRecoloring (standardResidualColoring D n hwidth))
    (habs :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let B :=
        standardResidualColoring D n hwidth
      R.IsAbsorbed) :
    ∑ i : ProjectionOrdered V, 2 ^ centreExponent (C i) t
      ≤ 2 ^ n := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp

  have htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidthN : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidthN
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (C i) t
  let ell : ProjectionOrdered V → ℕ :=
    fun i => n - exponent i

  have honeLoss :
      ∀ i, (active B i).card ≤ ell i + 1 := by
    intro i
    have h :=
      planarStandardResidual_active_card_le_oneLayer
        hp hcap hn hdelta0 hdelta1 ht hlam i (C i)
    simpa [B, D, ell, exponent] using h

  have hbad :
      ∀ i, ell i < (active B i).card →
        residualCoord n ∈ active B i := by
    intro i hi
    simpa [B, D, ell, exponent] using
      hbadResidual i (by simpa [B, D, ell, exponent] using hi)

  have hretained :
      ∀ i, (retainedActive B i).card ≤ ell i :=
    retainedActive_card_le_of_one_loss_and_bad_implies_residual
      B ell honeLoss hbad

  have hexponent :
      ∀ i, exponent i ≤ n := by
    intro i
    have hlt :=
      centreExponent_lt_n
        (C i) n delta t hn hdelta0 hdelta1 ht
    exact Nat.le_of_lt hlt

  have hell :
      ∀ i, ell i = n - exponent i := by
    intro i
    rfl

  have habs' : R.IsAbsorbed := by
    simpa [B, D] using habs

  have hcap' :=
    R.cluster_capacity_of_absorbed_recoloring
      habs' exponent ell hexponent hell hretained

  simpa [exponent] using hcap'

#print axioms planar_lowerBranch_capacity_of_absorbed_residual

end ProjectionOrdered
end JSP000404Research
