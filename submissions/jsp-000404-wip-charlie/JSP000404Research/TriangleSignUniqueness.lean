import JSP000404Research.TriangleSignParity
import JSP000404Research.CanonicalSignAcyclicity
import Mathlib.Tactic

/-!
# Exactly one canonical sign split on every triangle

For the canonical projective sign convention, edge reversal flips the sign.
The resulting three vertex-wise split predicates on a triangle have odd
parity.  The all-three case is impossible by canonical half-plane acyclicity.

Hence every nondegenerate triangle has exactly one vertex at which its two
incident canonical ray signs differ.

This packages the sign information in the form needed by later finite
Hamiltonian-residual arguments.
-/

namespace JSP000404Research

/-- Pure Boolean form: the three triangle split predicates have either one
true entry or all three true. -/
theorem triangle_split_bools_one_or_three
    (sab sac sbc : Bool) :
    (
      (sab ≠ sac ∧ ¬ ((Bool.not sab) ≠ sbc) ∧ ¬ ((Bool.not sac) ≠ (Bool.not sbc)))
      ∨
      (¬ (sab ≠ sac) ∧ ((Bool.not sab) ≠ sbc) ∧ ¬ ((Bool.not sac) ≠ (Bool.not sbc)))
      ∨
      (¬ (sab ≠ sac) ∧ ¬ ((Bool.not sab) ≠ sbc) ∧ ((Bool.not sac) ≠ (Bool.not sbc)))
      ∨
      ((sab ≠ sac) ∧ ((Bool.not sab) ≠ sbc) ∧ ((Bool.not sac) ≠ (Bool.not sbc)))
    ) := by
  cases sab <;> cases sac <;> cases sbc <;> simp

/-- Every injective planar triangle has exactly one canonical sign-split
vertex. -/
theorem triangle_exactly_one_canonical_sign_split
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    (
      (raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) ≠
          raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a))
      ∧
      ¬ (raySignAt hp b (⟨a, hab⟩ : OtherVertex b) ≠
          raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b))
      ∧
      ¬ (raySignAt hp c (⟨a, hac⟩ : OtherVertex c) ≠
          raySignAt hp c (⟨b, hbc⟩ : OtherVertex c))
    )
    ∨
    (
      ¬ (raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) ≠
          raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a))
      ∧
      (raySignAt hp b (⟨a, hab⟩ : OtherVertex b) ≠
          raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b))
      ∧
      ¬ (raySignAt hp c (⟨a, hac⟩ : OtherVertex c) ≠
          raySignAt hp c (⟨b, hbc⟩ : OtherVertex c))
    )
    ∨
    (
      ¬ (raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) ≠
          raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a))
      ∧
      ¬ (raySignAt hp b (⟨a, hab⟩ : OtherVertex b) ≠
          raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b))
      ∧
      (raySignAt hp c (⟨a, hac⟩ : OtherVertex c) ≠
          raySignAt hp c (⟨b, hbc⟩ : OtherVertex c))
    ) := by
  let sab :=
    raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a)
  let sac :=
    raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a)
  let sbc :=
    raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b)

  have hba :
      raySignAt hp b (⟨a, hab⟩ : OtherVertex b) = Bool.not sab := by
    simpa [sab] using raySignAt_reverse_eq_not hp hab
  have hca :
      raySignAt hp c (⟨a, hac⟩ : OtherVertex c) = Bool.not sac := by
    simpa [sac] using raySignAt_reverse_eq_not hp hac
  have hcb :
      raySignAt hp c (⟨b, hbc⟩ : OtherVertex c) = Bool.not sbc := by
    simpa [sbc] using raySignAt_reverse_eq_not hp hbc

  have hpure := triangle_split_bools_one_or_three sab sac sbc
  rcases hpure with hA | hB | hC | hAll
  · left
    simpa [sab, sac, sbc, hba, hca, hcb] using hA
  · right; left
    simpa [sab, sac, sbc, hba, hca, hcb] using hB
  · right; right
    simpa [sab, sac, sbc, hba, hca, hcb] using hC
  · exfalso
    have ha :
        raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) ≠
          raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a) := by
      simpa [sab, sac] using hAll.1
    have hb :
        raySignAt hp b (⟨a, hab⟩ : OtherVertex b) ≠
          raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b) := by
      rw [hba]
      simpa [sbc] using hAll.2.1
    have hc :
        raySignAt hp c (⟨a, hac⟩ : OtherVertex c) ≠
          raySignAt hp c (⟨b, hbc⟩ : OtherVertex c) := by
      rw [hca, hcb]
      exact hAll.2.2
    exact impossible_triangle_all_three_sign_splits
      hp hab hac hbc ha hb hc

#print axioms triangle_split_bools_one_or_three
#print axioms triangle_exactly_one_canonical_sign_split

end JSP000404Research
