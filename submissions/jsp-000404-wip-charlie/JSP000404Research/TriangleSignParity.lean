import JSP000404Research.CanonicalRayReversal
import Mathlib.Tactic

/-!
# Canonical sign parity on a triangle

For an unoriented edge, canonical projective theta is the same at both ends
while the Boolean sign flips.

Therefore, for a triangle i,j,k, define a transition at a vertex to mean that
the two incident triangle-edge signs seen from that vertex are different.
The xor of the three transition indicators is true: an odd number of triangle
vertices are transition vertices.

In particular, if the two triangle rays at i have the same canonical sign,
then exactly one of j and k sees its two triangle rays with opposite signs.

This is the discrete parity mechanism needed to transfer a same-sign positive
gap at a separated support-two centre to an opposite-sign projective
separation at one of the other two triangle vertices.
-/

namespace JSP000404Research

/-- Boolean xor, used only as a readable triangle-transition indicator. -/
def boolXor (a b : Bool) : Bool :=
  a != b

@[simp] theorem boolXor_eq_true_iff
    (a b : Bool) :
    boolXor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp [boolXor]

@[simp] theorem boolXor_eq_false_iff
    (a b : Bool) :
    boolXor a b = false ↔ a = b := by
  cases a <;> cases b <;> simp [boolXor]

/-- Pure Boolean triangle parity under edge reversal. -/
theorem triangle_transition_xor
    (sij sik sjk : Bool) :
    boolXor sij sik !=
      (boolXor (!sij) sjk != boolXor (!sik) (!sjk)) = false := by
  cases sij <;> cases sik <;> cases sjk <;> decide

/-- More useful consequence: if i is same-sign, exactly one of the other two
vertices is opposite-sign. -/
theorem exactly_one_other_transition_of_same_at_first
    {sij sik sjk : Bool}
    (hi : sij = sik) :
    ( (!sij ≠ sjk) ∧ ¬ (!sik ≠ !sjk) ) ∨
    ( ¬ (!sij ≠ sjk) ∧ (!sik ≠ !sjk) ) := by
  subst sik
  cases sij <;> cases sjk <;> simp

/-- Geometric specialization to the three oriented edges of an injective
planar triangle. -/
theorem triangle_exactly_one_other_sign_transition
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi :
      raySignAt hp i ⟨j, hij.symm⟩ =
        raySignAt hp i ⟨k, hik.symm⟩) :
    ( (raySignAt hp j ⟨i, hij⟩ ≠
          raySignAt hp j ⟨k, hjk.symm⟩) ∧
        ¬ (raySignAt hp k ⟨i, hik⟩ ≠
          raySignAt hp k ⟨j, hjk⟩) ) ∨
    ( ¬ (raySignAt hp j ⟨i, hij⟩ ≠
          raySignAt hp j ⟨k, hjk.symm⟩) ∧
        (raySignAt hp k ⟨i, hik⟩ ≠
          raySignAt hp k ⟨j, hjk⟩) ) := by
  have hji :=
    raySignAt_reverse_eq_not hp hij
  have hki :=
    raySignAt_reverse_eq_not hp hik
  have hkj :=
    raySignAt_reverse_eq_not hp hjk
  let sij := raySignAt hp i ⟨j, hij.symm⟩
  let sik := raySignAt hp i ⟨k, hik.symm⟩
  let sjk := raySignAt hp j ⟨k, hjk.symm⟩
  have hpure :=
    exactly_one_other_transition_of_same_at_first
      (sij := sij) (sik := sik) (sjk := sjk)
      (by simpa [sij, sik] using hi)
  dsimp [sij, sik, sjk] at hpure
  rw [hji, hki] at hpure
  have hkj' :
      raySignAt hp k ⟨j, hjk⟩ =
        ! raySignAt hp j ⟨k, hjk.symm⟩ := hkj
  rw [hkj'] at hpure
  exact hpure

#print axioms triangle_transition_xor
#print axioms exactly_one_other_transition_of_same_at_first
#print axioms triangle_exactly_one_other_sign_transition

end JSP000404Research
