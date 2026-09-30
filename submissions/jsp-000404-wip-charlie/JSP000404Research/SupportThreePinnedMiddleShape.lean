import JSP000404Research.CentreExponent
import Mathlib.Tactic

/-!
# Lightweight middle-hidden pinned support-three shape

This module isolates the data-only middle-hidden shape used by the active
JSP-000404 terminal.  It deliberately does not import the concrete deletion
machinery, so sign and angle arguments can depend on the shape without pulling
in unrelated induction infrastructure.
-/

namespace JSP000404Research

def SupportThreePinnedMiddleShape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t : ℝ}
    {s i : V}
    (hsi : s ≠ i)
    (C : CentreProjectiveCycle hp i) : Prop :=
  ∃ first0 : OtherVertex i,
    ∃ rest0 : List (OtherVertex i),
    ∃ k : ℕ,
    ∃ preTop postTop : List (OtherVertex i),
    ∃ r : OtherVertex i,
    ∃ rest : List (OtherVertex i),
    ∃ qFirst qLast qHidden : ℕ,
      C.rays = first0 :: rest0 ∧
      C.rays =
        preTop ++ (⟨s,hsi⟩ : OtherVertex i) :: postTop ∧
      k = preTop.length ∧
      C.rays.rotate k =
        (⟨s,hsi⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t C.gaps).rotate k =
        qFirst :: [0,qHidden,0] ++ [qLast] ∧
      1 ≤ qFirst ∧
      1 ≤ qLast ∧
      qHidden ≠ 0

#print axioms SupportThreePinnedMiddleShape

end JSP000404Research
