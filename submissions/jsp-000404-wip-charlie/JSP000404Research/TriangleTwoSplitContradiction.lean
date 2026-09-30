import JSP000404Research.TriangleSignUniqueness
import Mathlib.Tactic

/-!
# Two canonical sign splits on one triangle are impossible

The exact-one triangle sign theorem immediately rules out any triangle that
splits at two prescribed vertices.

A second corollary packages the crossed two-pair sign pattern naturally
produced by two middle-hidden support-three centres in the six-point
Hamiltonian residual:

* at b, c and x share one sign while y and z share the other;
* at c, b and y share one sign while x and z share the other.

Then triangle b-c-z splits at both b and c, which is impossible.

This is the discrete geometric contradiction targeted by the remaining
Hamiltonian-residual bridge.
-/

namespace JSP000404Research

theorem impossible_two_canonical_sign_splits
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    (ha :
      raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) ≠
        raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a))
    (hb :
      raySignAt hp b (⟨a, hab⟩ : OtherVertex b) ≠
        raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b)) :
    False := by
  rcases triangle_exactly_one_canonical_sign_split
      hp hab hac hbc with hA | hB | hC
  · exact hA.2.1 hb
  · exact hB.1 ha
  · exact hC.1 ha

/-- Crossed same-sign pairs at two centres force two sign splits on the
triangle formed by the two centres and the crossed endpoint z. -/
theorem impossible_crossed_middle_hidden_sign_pattern
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {b c x y z : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x) (hby : b ≠ y) (hbz : b ≠ z)
    (hcx : c ≠ x) (hcy : c ≠ y) (hcz : c ≠ z)
    (hBCX :
      raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b) =
        raySignAt hp b (⟨x, hbx.symm⟩ : OtherVertex b))
    (hBYZ :
      raySignAt hp b (⟨y, hby.symm⟩ : OtherVertex b) =
        raySignAt hp b (⟨z, hbz.symm⟩ : OtherVertex b))
    (hBcross :
      raySignAt hp b (⟨x, hbx.symm⟩ : OtherVertex b) ≠
        raySignAt hp b (⟨y, hby.symm⟩ : OtherVertex b))
    (hCBY :
      raySignAt hp c (⟨b, hbc⟩ : OtherVertex c) =
        raySignAt hp c (⟨y, hcy.symm⟩ : OtherVertex c))
    (hCXZ :
      raySignAt hp c (⟨x, hcx.symm⟩ : OtherVertex c) =
        raySignAt hp c (⟨z, hcz.symm⟩ : OtherVertex c))
    (hCcross :
      raySignAt hp c (⟨y, hcy.symm⟩ : OtherVertex c) ≠
        raySignAt hp c (⟨x, hcx.symm⟩ : OtherVertex c)) :
    False := by
  have hbSplit :
      raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b) ≠
        raySignAt hp b (⟨z, hbz.symm⟩ : OtherVertex b) := by
    intro hEq
    apply hBcross
    calc
      raySignAt hp b (⟨x, hbx.symm⟩ : OtherVertex b)
          =
        raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b) :=
        hBCX.symm
      _ =
        raySignAt hp b (⟨z, hbz.symm⟩ : OtherVertex b) :=
        hEq
      _ =
        raySignAt hp b (⟨y, hby.symm⟩ : OtherVertex b) :=
        hBYZ.symm
  have hcSplit :
      raySignAt hp c (⟨b, hbc⟩ : OtherVertex c) ≠
        raySignAt hp c (⟨z, hcz.symm⟩ : OtherVertex c) := by
    intro hEq
    apply hCcross
    calc
      raySignAt hp c (⟨y, hcy.symm⟩ : OtherVertex c)
          =
        raySignAt hp c (⟨b, hbc⟩ : OtherVertex c) :=
        hCBY.symm
      _ =
        raySignAt hp c (⟨z, hcz.symm⟩ : OtherVertex c) :=
        hEq
      _ =
        raySignAt hp c (⟨x, hcx.symm⟩ : OtherVertex c) :=
        hCXZ.symm
  exact impossible_two_canonical_sign_splits
    hp hbc hbz hcz hbSplit hcSplit

#print axioms impossible_two_canonical_sign_splits
#print axioms impossible_crossed_middle_hidden_sign_pattern

end JSP000404Research
