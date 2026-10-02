import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.ProjectionQTTTAllNSupport
import Mathlib.Tactic

/-!
# No top centre survives a four-second-layer Q/T/T/T state

Three distinct deficit-two centres already exclude every top centre by the
sharp second-layer multiplicity theorem.  A Q/T/T/T state contains four such
centres, so its antipode blocker can never lie in the top layer.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem no_top_centre_of_three_secondLayer
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {a b c : ProjectionOrdered V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haSecond : centreExponent (C a) t = n - 2)
    (hbSecond : centreExponent (C b) t = n - 2)
    (hcSecond : centreExponent (C c) t = n - 2) :
    ∀ r : ProjectionOrdered V,
      centreExponent (C r) t ≠ n - 1 := by
  intro r hrTop
  have hra : r ≠ a := by
    intro h
    subst r
    rw [haSecond] at hrTop
    omega
  have hrb : r ≠ b := by
    intro h
    subst r
    rw [hbSecond] at hrTop
    omega
  have hrc : r ≠ c := by
    intro h
    subst r
    rw [hcSecond] at hrTop
    omega
  exact no_top_with_three_deficitTwo_companions
    (p := reindexedPoint p)
    (reindexedPoint_injective hp)
    (angleCap_reindexed hcap)
    hn3 hdelta0 hdeltaHalf ht hlam
    hra hrb hrc
    hab hac hbc
    (C r) (C a) (C b) (C c)
    hrTop haSecond hbSecond hcSecond

#print axioms no_top_centre_of_three_secondLayer

end ProjectionOrdered
end JSP000404Research
