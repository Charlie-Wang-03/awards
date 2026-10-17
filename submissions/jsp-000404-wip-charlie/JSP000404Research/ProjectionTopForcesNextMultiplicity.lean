import JSP000404Research.TopForcesNextMultiplicity
import JSP000404Research.GenericTopExponentMultiplicity
import Mathlib.Tactic

/-!
# Projection-order transfer of the sharp top-layer next-exponent exclusion

The global six-source payment framework operates on the projection-ordered
finite type. This theorem transfers the genuine original planar AngleCap
high-layer multiplicity exclusion to that exact indexing, without altering
the cycles, geometry, Boolean payment credits, or adding assumptions other
than the already stated cardinality and existence of a top centre.
The original all-n global dyadic conjecture is still open.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem projection_top_forces_next_card_le_one
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : 4 ≤ Fintype.card (ProjectionOrdered V))
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (s : ProjectionOrdered V)
    (hs :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      centreExponent (C s) t = n - 1) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    ((Finset.univ : Finset (ProjectionOrdered V)).filter
      (fun i => centreExponent (C i) t = n - 2)).card ≤ 1 := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcapRe : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  exact actual_next_exponent_card_le_one_of_top
    (reindexedPoint_injective hp) hcapRe
    hcard hn hdelta0 hdeltaHalf ht hlam C s hs

#print axioms projection_top_forces_next_card_le_one

end ProjectionOrdered
end JSP000404Research
