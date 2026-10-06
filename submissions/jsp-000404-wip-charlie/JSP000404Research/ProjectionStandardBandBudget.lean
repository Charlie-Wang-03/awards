
import JSP000404Research.ProjectionCutLocalCycle
import JSP000404Research.CentreStandardBandBudgetCore
import JSP000404Research.CentreExponentBounds
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Concrete generic-projection one-layer budget

ProjectionCutLocalCycle closes the representation bridge

  localDirectionExponent = centreExponent.

CentreStandardBandBudget already proves the one-dimensional band estimate once
this agreement is supplied.

This file instantiates that abstract agreement with the actual generic
projection construction.

For every centre of a planar configuration under AngleCap, and every Sendov
lower-branch normalization t=n+delta with 0<=delta<1,

  centreExponent < n

and the canonical standard (n+1)-band colouring satisfies

  card(active(v)) <= n - centreExponent(v) + 1.

These are exactly the two profile hypotheses used throughout the residual
projection modules.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

private theorem projectionBudget_scale_pos
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (htEq : t = (n : ℝ) + delta) :
    0 < t := by
  rw [htEq]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem projectionBudget_width_lt_succ
    {n : ℕ} {delta t : ℝ}
    (hdelta1 : delta < 1)
    (htEq : t = (n : ℝ) + delta) :
    t < (n + 1 : ℕ) := by
  rw [htEq]
  exact_mod_cast
    (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)

/-- Direct generic-projection specialization of the one-layer standard-band
budget. -/
theorem genericProjection_standardActive_card_le_centreDeficit_add_one
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htPos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hwidth : t < (n + 1 : ℕ))
    (i : ProjectionOrdered V)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hexp :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent C t ≤ n) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (active
      (standardResidualColoring
        (genericDirectionData_sendov hp hcap htPos hlam)
        n hwidth)
      i).card
      ≤
    n - centreExponent C t + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D :=
    genericDirectionData_sendov hp hcap htPos hlam
  let L :=
    projectionCutLocalCycle hp hcap htPos hlam i C
  have hagree :
      L.exponent = centreExponent C t := by
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htPos hlam i C
  have hwidthR : t < (n : ℝ) + 1 := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    simpa [hcast] using hwidth
  have hbudget :=
    standardActive_card_le_centreDeficit_add_one_of_local_agreement
      D L C hwidthR hexp hagree
  simpa [D, standardResidualColoring] using hbudget

/-- Lower-branch specialization: the concrete centre exponent is automatically
strictly below n, so the one-layer budget needs no extra exponent hypothesis. -/
theorem genericProjection_lowerBranch_oneLayerBudget
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (htEq : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    centreExponent C t < n ∧
    (active
      (standardResidualColoring
        (genericDirectionData_sendov hp hcap
          (projectionBudget_scale_pos hn hdelta0 htEq) hlam)
        n
        (projectionBudget_width_lt_succ hdelta1 htEq))
      i).card
      ≤
    n - centreExponent C t + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htPos :
      0 < t :=
    projectionBudget_scale_pos hn hdelta0 htEq
  have hwidth :
      t < (n + 1 : ℕ) :=
    projectionBudget_width_lt_succ hdelta1 htEq
  have hexpLt :
      centreExponent C t < n :=
    centreExponent_lt_n
      C n delta t hn hdelta0 hdelta1 htEq
  have hexpLe :
      centreExponent C t ≤ n :=
    Nat.le_of_lt hexpLt
  refine ⟨hexpLt, ?_⟩
  exact genericProjection_standardActive_card_le_centreDeficit_add_one
    hp hcap htPos hlam hwidth i C hexpLe

/-- Family form used to instantiate the abstract residual profile hypotheses
for every centre simultaneously. -/
theorem genericProjection_lowerBranch_profile_hypotheses
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (htEq : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∀ i, centreExponent (C i) t < n) ∧
    (∀ i,
      (active
        (standardResidualColoring
          (genericDirectionData_sendov hp hcap
            (projectionBudget_scale_pos hn hdelta0 htEq) hlam)
          n
          (projectionBudget_width_lt_succ hdelta1 htEq))
        i).card
        ≤
      n - centreExponent (C i) t + 1) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  constructor
  · intro i
    exact centreExponent_lt_n
      (C i) n delta t hn hdelta0 hdelta1 htEq
  · intro i
    exact
      (genericProjection_lowerBranch_oneLayerBudget
        hp hcap hn hdelta0 hdelta1 htEq hlam i (C i)).2

#print axioms genericProjection_standardActive_card_le_centreDeficit_add_one
#print axioms genericProjection_lowerBranch_oneLayerBudget
#print axioms genericProjection_lowerBranch_profile_hypotheses

end ProjectionOrdered
end JSP000404Research
