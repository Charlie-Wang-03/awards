import JSP000404Research.ProjectionSupportTwoMiddlePairForcing
import JSP000404Research.SupportTwoThreeMarkedSmallPair
import JSP000404Research.QTTTSmallPairMatching
import Mathlib.Tactic

/-!
# Direct four-state reduction for three support-two centres in an ordered four

The eleven-state detour is not needed once the two middle ranks have
consecutive three-band palettes.

For d<a<b<c with a,b,c support-two:
* lower-middle a forces the right pair {b,c} to be delta-small;
* upper-middle b forces the left pair {d,a} to be delta-small;
* extreme c has one delta-small pair among {d,a,b}.
The choice {a,b} at c would give two delta-small angles in triangle abc, which
is impossible because 2*delta<1 under the global angle cap.  Hence c chooses
{d,a} or {d,b}: exactly patterns 1 or 2.

The dual order a<b<c<d gives exactly patterns 6 or 11.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem threeSupport_ordered_minFourth_direct_one_or_two
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n ma mb : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {d a b c : ProjectionOrdered V}
    (hda : d < a)
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
    (haSupport : positiveSupport (centreQuotient (Cfam a) t) = 2)
    (hbSupport : positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport : positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hpalA :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R a).map Fin.valEmbedding = threeNatInterval ma)
    (hpalB :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R b).map Fin.valEmbedding = threeNatInterval mb) :
    (
      EuclideanGeometry.angle
        (reindexedPoint p b) (reindexedPoint p a) (reindexedPoint p c)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a) (reindexedPoint p b) (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a) (reindexedPoint p c) (reindexedPoint p d)
        ≤ delta * lam
    )
    ∨
    (
      EuclideanGeometry.angle
        (reindexedPoint p b) (reindexedPoint p a) (reindexedPoint p c)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a) (reindexedPoint p b) (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p b) (reindexedPoint p c) (reindexedPoint p d)
        ≤ delta * lam
    ) := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hdb : d < b := hda.trans hab
  have hdc : d < c := hdb.trans hbc
  have hac : a < c := hab.trans hbc

  have hA :=
    supportTwo_lower_middle_forces_right_pair_small
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hda hab hbc haLoss haSecond haSupport hpalA
  have hBraw :=
    supportTwo_upper_middle_forces_left_pair_small
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hda hab hbc hbLoss hbSecond hbSupport hpalB
  have hB :
      EuclideanGeometry.angle
        (reindexedPoint p a) (reindexedPoint p b) (reindexedPoint p d)
        ≤ delta * lam := by
    simpa [EuclideanGeometry.angle_comm] using hBraw

  have hC :=
    supportTwo_three_other_vertices_has_small_pair
      (reindexedPoint_injective hp)
      (by
        intro x y z hxy hxz hyz
        exact hcap x.toOriginal y.toOriginal z.toOriginal
          (by intro h; apply hxy; exact toOriginal_injective h)
          (by intro h; apply hxz; exact toOriginal_injective h)
          (by intro h; apply hyz; exact toOriginal_injective h))
      hn3 hdelta0 hdeltaHalf ht hlam
      (i := c) (a := d) (b := a) (c := b)
      (ne_of_gt hdc) (ne_of_gt hac) (ne_of_gt hbc)
      (ne_of_lt hda) (ne_of_lt hdb) (ne_of_lt hab)
      (Cfam c) hcSecond hcSupport

  rcases hC with hCad | hCab | hCbd
  · left
    exact ⟨hA,hB,by
      simpa [EuclideanGeometry.angle_comm] using hCad⟩
  · have hlampos : 0 < lam := by
      have htpos := sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
      rw [hlam]
      exact div_pos Real.pi_pos htpos
    exact False.elim
      (two_delta_small_angles_same_triangle_impossible
        (reindexedPoint_injective hp)
        (by
          intro x y z hxy hxz hyz
          exact hcap x.toOriginal y.toOriginal z.toOriginal
            (by intro h; apply hxy; exact toOriginal_injective h)
            (by intro h; apply hxz; exact toOriginal_injective h)
            (by intro h; apply hyz; exact toOriginal_injective h))
        hdeltaHalf hlampos
        (ne_of_lt hab) (ne_of_lt hac) (ne_of_lt hbc)
        hA
        (by simpa [EuclideanGeometry.angle_comm] using hCab))
  · right
    exact ⟨hA,hB,hCbd⟩

theorem threeSupport_ordered_maxFourth_direct_six_or_eleven
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n mb mc : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a b c d : ProjectionOrdered V}
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d)
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
    (haSupport : positiveSupport (centreQuotient (Cfam a) t) = 2)
    (hbSupport : positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport : positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hpalB :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R b).map Fin.valEmbedding = threeNatInterval mb)
    (hpalC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R c).map Fin.valEmbedding = threeNatInterval mc) :
    (
      EuclideanGeometry.angle
        (reindexedPoint p b) (reindexedPoint p a) (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p c) (reindexedPoint p b) (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a) (reindexedPoint p c) (reindexedPoint p b)
        ≤ delta * lam
    )
    ∨
    (
      EuclideanGeometry.angle
        (reindexedPoint p c) (reindexedPoint p a) (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p c) (reindexedPoint p b) (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a) (reindexedPoint p c) (reindexedPoint p b)
        ≤ delta * lam
    ) := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hac : a < c := hab.trans hbc
  have had : a < d := hac.trans hcd
  have hbd : b < d := hbc.trans hcd

  have hB :=
    supportTwo_lower_middle_forces_right_pair_small
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hcd hbLoss hbSecond hbSupport hpalB
  have hC :=
    supportTwo_upper_middle_forces_left_pair_small
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hcd hcLoss hcSecond hcSupport hpalC

  have hA :=
    supportTwo_three_other_vertices_has_small_pair
      (reindexedPoint_injective hp)
      (by
        intro x y z hxy hxz hyz
        exact hcap x.toOriginal y.toOriginal z.toOriginal
          (by intro h; apply hxy; exact toOriginal_injective h)
          (by intro h; apply hxz; exact toOriginal_injective h)
          (by intro h; apply hyz; exact toOriginal_injective h))
      hn3 hdelta0 hdeltaHalf ht hlam
      (i := a) (a := b) (b := c) (c := d)
      (ne_of_lt hab) (ne_of_lt hac) (ne_of_lt had)
      (ne_of_lt hbc) (ne_of_lt hbd) (ne_of_lt hcd)
      (Cfam a) haSecond haSupport

  rcases hA with hAbc | hAcd | hAdb
  · have hlampos : 0 < lam := by
      have htpos := sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
      rw [hlam]
      exact div_pos Real.pi_pos htpos
    exact False.elim
      (two_delta_small_angles_same_triangle_impossible
        (reindexedPoint_injective hp)
        (by
          intro x y z hxy hxz hyz
          exact hcap x.toOriginal y.toOriginal z.toOriginal
            (by intro h; apply hxy; exact toOriginal_injective h)
            (by intro h; apply hxz; exact toOriginal_injective h)
            (by intro h; apply hyz; exact toOriginal_injective h))
        hdeltaHalf hlampos
        (ne_of_lt hab) (ne_of_lt hac) (ne_of_lt hbc)
        hAbc hC)
  · right
    exact ⟨hAcd,hB,hC⟩
  · left
    exact ⟨by
      simpa [EuclideanGeometry.angle_comm] using hAdb,hB,hC⟩

#print axioms threeSupport_ordered_minFourth_direct_one_or_two
#print axioms threeSupport_ordered_maxFourth_direct_six_or_eleven

end ProjectionOrdered
end JSP000404Research
