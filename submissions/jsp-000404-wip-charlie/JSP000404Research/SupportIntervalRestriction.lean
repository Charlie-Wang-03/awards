import JSP000404Research.SupportIntervalCertificate
import Mathlib.Tactic

/-!
# Restricting support-interval certificates to a subconfiguration

A support interval certificate for a vertex in a large point configuration
remains valid after restricting to any injectively indexed subconfiguration
containing that vertex.  Its angular data and turn length are unchanged.

This simple functoriality lets global high-exponent transition certificates be
combined with four-point convex-separation arguments.
-/

namespace JSP000404Research

namespace SupportIntervalCertificate

def restrict
    {V W : Type*}
    {p : V → Plane}
    (e : W → V)
    {i : W}
    (he : ∀ j, j ≠ i → e j ≠ e i)
    (S : SupportIntervalCertificate (p := p) (e i)) :
    SupportIntervalCertificate (p := fun w => p (e w)) i where
  a := S.a
  width := S.width
  sigma := S.sigma
  width_nonneg := S.width_nonneg
  width_lt_pi := S.width_lt_pi
  repr := by
    intro j hji
    obtain ⟨rho, theta, hrho, hlo, hhi, hrepr⟩ :=
      S.repr (e j) (he j hji)
    exact ⟨rho, theta, hrho, hlo, hhi, hrepr⟩

@[simp] theorem turnLength_restrict
    {V W : Type*}
    {p : V → Plane}
    (e : W → V)
    {i : W}
    (he : ∀ j, j ≠ i → e j ≠ e i)
    (S : SupportIntervalCertificate (p := p) (e i)) :
    (restrict e he S).turnLength = S.turnLength := by
  rfl

/-- Injective maps supply the pointwise noncollision hypothesis automatically. -/
def restrictOfInjective
    {V W : Type*}
    {p : V → Plane}
    (e : W → V)
    (he : Function.Injective e)
    (i : W)
    (S : SupportIntervalCertificate (p := p) (e i)) :
    SupportIntervalCertificate (p := fun w => p (e w)) i :=
  restrict e (fun j hji => he.ne hji) S

@[simp] theorem turnLength_restrictOfInjective
    {V W : Type*}
    {p : V → Plane}
    (e : W → V)
    (he : Function.Injective e)
    (i : W)
    (S : SupportIntervalCertificate (p := p) (e i)) :
    (restrictOfInjective e he i S).turnLength = S.turnLength := by
  rfl

#print axioms turnLength_restrict
#print axioms turnLength_restrictOfInjective

end SupportIntervalCertificate

end JSP000404Research
