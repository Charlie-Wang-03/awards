import JSP000404Research.ProjectionSupportTwoMiddlePairForcing
import JSP000404Research.SupportTwoThreeMarkedSmallPair
import JSP000404Research.TwoSmallAngleContradiction
import Mathlib.Tactic

/-!
# Two-state ordered terminal in the unique-support-one branch

Assume four second-layer centres have a common consecutive retained palette.

If the support-one centre is the left order extreme

  o < a < b < c

and a,b,c are support-two, then middle-rank forcing gives

  angle(b,a,c) <= delta*lambda,
  angle(o,b,a) <= delta*lambda.

The support-two small-pair theorem at c has three possibilities among
{o,a,b}.  The pair {a,b} would give a second delta-small angle in triangle
a-b-c and is impossible.  Hence only {o,a} or {o,b} remain.

The right-extreme case is symmetric.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem leftSupportOne_threeSupportTwo_two_state_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {o a b c : ProjectionOrdered V}
    (hoa : o < a)
    (hab : a < b)
    (hbc : b < c)
    (haLoss :
      a ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (haSecond : centreExponent (Cfam a) t = n - 2)
    (hbSecond : centreExponent (Cfam b) t = n - 2)
    (hcSecond : centreExponent (Cfam c) t = n - 2)
    (haSupport :
      positiveSupport (centreQuotient (Cfam a) t) = 2)
    (hbSupport :
      positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport :
      positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hpalA :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R a).map Fin.valEmbedding =
        threeNatInterval m)
    (hpalB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R b).map Fin.valEmbedding =
        threeNatInterval m) :
    EuclideanGeometry.angle
        (reindexedPoint p b)
        (reindexedPoint p a)
        (reindexedPoint p c)
      ≤ delta * lam
    ∧
    EuclideanGeometry.angle
        (reindexedPoint p o)
        (reindexedPoint p b)
        (reindexedPoint p a)
      ≤ delta * lam
    ∧
    (
      EuclideanGeometry.angle
          (reindexedPoint p o)
          (reindexedPoint p c)
          (reindexedPoint p a)
        ≤ delta * lam
      ∨
      EuclideanGeometry.angle
          (reindexedPoint p b)
          (reindexedPoint p c)
          (reindexedPoint p o)
        ≤ delta * lam
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hob : o < b := hoa.trans hab
  have hac : a < c := hab.trans hbc
  have hoc : o < c := hob.trans hbc

  have hsmallA :=
    supportTwo_lower_middle_forces_right_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hoa hab hbc haLoss haSecond haSupport hpalA

  have hsmallB :=
    supportTwo_upper_middle_forces_left_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hoa hab hbc hbLoss hbSecond hbSupport hpalB

  have hsmallC :=
    supportTwo_three_other_vertices_has_small_pair
      (reindexedPoint_injective hp)
      (by
        intro x y z hxy hxz hyz
        exact hcap x.toOriginal y.toOriginal z.toOriginal
          (by
            intro h
            apply hxy
            exact ProjectionOrdered.toOriginal_injective h)
          (by
            intro h
            apply hxz
            exact ProjectionOrdered.toOriginal_injective h)
          (by
            intro h
            apply hyz
            exact ProjectionOrdered.toOriginal_injective h))
      (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      (i := c) (a := o) (b := a) (c := b)
      (ne_of_gt hoc) (ne_of_gt hac) (ne_of_gt hbc)
      (ne_of_lt hoa) (ne_of_lt hob) (ne_of_lt hab)
      (Cfam c) hcSecond hcSupport

  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  refine ⟨hsmallA,hsmallB,?_⟩
  rcases hsmallC with hOA | hAB | hBO
  · exact Or.inl hOA
  · have hA :
        EuclideanGeometry.angle
          (reindexedPoint p b)
          (reindexedPoint p a)
          (reindexedPoint p c)
          ≤ delta * lam := hsmallA
    have hC :
        EuclideanGeometry.angle
          (reindexedPoint p a)
          (reindexedPoint p c)
          (reindexedPoint p b)
          ≤ delta * lam := hAB
    exact False.elim
      (two_delta_small_angles_same_triangle_impossible
        (reindexedPoint_injective hp)
        (by
          intro x y z hxy hxz hyz
          exact hcap x.toOriginal y.toOriginal z.toOriginal
            (by
              intro h
              apply hxy
              exact ProjectionOrdered.toOriginal_injective h)
            (by
              intro h
              apply hxz
              exact ProjectionOrdered.toOriginal_injective h)
            (by
              intro h
              apply hyz
              exact ProjectionOrdered.toOriginal_injective h))
        hdeltaHalf hlampos
        (ne_of_lt hab)
        (ne_of_lt hac)
        (ne_of_lt hbc)
        hA hC)
  · exact Or.inr (by
      simpa [EuclideanGeometry.angle_comm] using hBO)

theorem rightSupportOne_threeSupportTwo_two_state_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a b c o : ProjectionOrdered V}
    (hab : a < b)
    (hbc : b < c)
    (hco : c < o)
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hcLoss :
      c ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (haSecond : centreExponent (Cfam a) t = n - 2)
    (hbSecond : centreExponent (Cfam b) t = n - 2)
    (hcSecond : centreExponent (Cfam c) t = n - 2)
    (haSupport :
      positiveSupport (centreQuotient (Cfam a) t) = 2)
    (hbSupport :
      positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport :
      positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hpalB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R b).map Fin.valEmbedding =
        threeNatInterval m)
    (hpalC :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R c).map Fin.valEmbedding =
        threeNatInterval m) :
    EuclideanGeometry.angle
        (reindexedPoint p c)
        (reindexedPoint p b)
        (reindexedPoint p o)
      ≤ delta * lam
    ∧
    EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p c)
        (reindexedPoint p b)
      ≤ delta * lam
    ∧
    (
      EuclideanGeometry.angle
          (reindexedPoint p b)
          (reindexedPoint p a)
          (reindexedPoint p o)
        ≤ delta * lam
      ∨
      EuclideanGeometry.angle
          (reindexedPoint p c)
          (reindexedPoint p a)
          (reindexedPoint p o)
        ≤ delta * lam
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hac : a < c := hab.trans hbc
  have hbo : b < o := hbc.trans hco
  have hao : a < o := hac.trans hco

  have hsmallB :=
    supportTwo_lower_middle_forces_right_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hco hbLoss hbSecond hbSupport hpalB

  have hsmallC :=
    supportTwo_upper_middle_forces_left_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hco hcLoss hcSecond hcSupport hpalC

  have hsmallA :=
    supportTwo_three_other_vertices_has_small_pair
      (reindexedPoint_injective hp)
      (by
        intro x y z hxy hxz hyz
        exact hcap x.toOriginal y.toOriginal z.toOriginal
          (by
            intro h
            apply hxy
            exact ProjectionOrdered.toOriginal_injective h)
          (by
            intro h
            apply hxz
            exact ProjectionOrdered.toOriginal_injective h)
          (by
            intro h
            apply hyz
            exact ProjectionOrdered.toOriginal_injective h))
      (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      (i := a) (a := b) (b := c) (c := o)
      (ne_of_lt hab) (ne_of_lt hac) (ne_of_lt hao)
      (ne_of_lt hbc) (ne_of_lt hbo) (ne_of_lt hco)
      (Cfam a) haSecond haSupport

  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  refine ⟨hsmallB,hsmallC,?_⟩
  rcases hsmallA with hBC | hCO | hOB
  · exact False.elim
      (two_delta_small_angles_same_triangle_impossible
        (reindexedPoint_injective hp)
        (by
          intro x y z hxy hxz hyz
          exact hcap x.toOriginal y.toOriginal z.toOriginal
            (by
              intro h
              apply hxy
              exact ProjectionOrdered.toOriginal_injective h)
            (by
              intro h
              apply hxz
              exact ProjectionOrdered.toOriginal_injective h)
            (by
              intro h
              apply hyz
              exact ProjectionOrdered.toOriginal_injective h))
        hdeltaHalf hlampos
        (ne_of_lt hab)
        (ne_of_lt hac)
        (ne_of_lt hbc)
        hBC hsmallC)
  · exact Or.inr hCO
  · exact Or.inl (by
      simpa [EuclideanGeometry.angle_comm] using hOB)

#print axioms leftSupportOne_threeSupportTwo_two_state_terminal
#print axioms rightSupportOne_threeSupportTwo_two_state_terminal

end ProjectionOrdered
end JSP000404Research
