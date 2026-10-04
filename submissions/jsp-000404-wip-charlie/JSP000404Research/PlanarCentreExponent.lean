import JSP000404Research.ProjectionOrderedVertices
import JSP000404Research.CentreExponentBounds

/-!
# Lightweight planar centre exponent family

The concrete centre exponent used by the generic-projection residual route is
a small definition.  Keeping it outside the hard-remainder assembly lets local
projected-loss geometry depend on the genuine centre exponent without
importing the full recursive residual machinery.
-/

namespace JSP000404Research
namespace ProjectionOrdered

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

def planarCentreExponent
    {t : ℝ}
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    ProjectionOrdered V → ℕ :=
  fun i => centreExponent (C i) t

theorem planarCentreExponent_le_n_light
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    ∀ i, planarCentreExponent hp C i ≤ n := by
  intro i
  unfold planarCentreExponent
  exact Nat.le_of_lt
    (centreExponent_lt_n
      (C i) n delta t hn hdelta0 hdelta1 ht)

#print axioms planarCentreExponent_le_n_light

end

end ProjectionOrdered
end JSP000404Research
