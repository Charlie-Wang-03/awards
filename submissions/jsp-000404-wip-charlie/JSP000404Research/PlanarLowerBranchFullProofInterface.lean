import JSP000404Research.FullDyadicHallProofInterface
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# End-to-end LOWER BRANCH proof of the canonical planar dyadic bound

The authentic planar normalization is t = n + delta,
0 <= delta < 1/2, with lam = pi/t and AngleCap p lam.
The exponent is the actual centreExponent (C i) t, not a surrogate.

After the TWO explicit geometric hypotheses in
FullDyadicHallProofInterface, all steps from a planar projective
configuration to the dyadic inequality are closed, without holes:
  planar points -> projective cycles -> local DirectionData cycles
  -> standard residual colouring -> minimal Hall core
  -> geometric obstruction -> global block expansion -> 2^n.

The hypotheses below are deliberately NOT claimed to follow from
AngleCap alone.  This is not an unconditional JSP-000404 proof.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_lower_branch_dyadic_capacity_of_geometric_gaps
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hNoLossFreeCore :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t := (by
        rw [ht]
        have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith)
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
      let B := standardResidualColoring D n (by exact_mod_cast hwidth)
      EveryMinimalHallCoreHasProjectedLoss B
        (fun i => centreExponent (cycles i) t))
    (hGlobalGeometry :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t := (by
        rw [ht]
        have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith)
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
      let B := standardResidualColoring D n (by exact_mod_cast hwidth)
      MinimalHallLossSharedMassGeometricExclusion B
        (fun i => centreExponent (cycles i) t)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  classical
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    (by
        rw [ht]
        have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith)
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let localCycles :
      ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
  let kLocal : ProjectionOrdered V → ℕ :=
    fun i => (localCycles i).exponent
  let kCanonical : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have hExponentEq : kLocal = kCanonical := by
    funext i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i (cycles i)
  have hLoss' : EveryMinimalHallCoreHasProjectedLoss B kLocal := by
    rw [hExponentEq]
    exact hNoLossFreeCore
  have hGeom' : MinimalHallLossSharedMassGeometricExclusion B kLocal := by
    rw [hExponentEq]
    exact hGlobalGeometry
  have hbound :
      (∑ i : ProjectionOrdered V, 2 ^ kLocal i) ≤ 2 ^ n :=
    dyadic_capacity_of_minimal_hall_geometric_exclusions
      D hwidth localCycles hLoss' hGeom'
  rw [hExponentEq] at hbound
  exact hbound

#print axioms planar_lower_branch_dyadic_capacity_of_geometric_gaps

end ProjectionOrdered
end JSP000404Research
