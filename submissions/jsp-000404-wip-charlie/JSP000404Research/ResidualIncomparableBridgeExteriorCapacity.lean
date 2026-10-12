import JSP000404Research.ResidualActualCollisionTwoFlipDiagonal
import Mathlib.Tactic

/-!
# Cross-active two-colour face flips inject bridge overlaps into their exterior

If retained active palettes A_b and A_v are incomparable, pick
cf in A_b \ A_v and cr in A_v \ A_b. The double flip at cf/cr
carries EVERY overlap word w in Q_b intersection Q_v outside
BOTH endpoint completion cubes, injectively.

This is an actual numerical capacity statement in terms of an
explicitly defined EXTERIOR region of the ambient Boolean cube:

  |Q_b intersection Q_v| <= |univ \ (Q_b union Q_v)|.

Each oriented palette-incomparable SOFT bridge moreover satisfies

  2^card(commonInactive(b,v)) <= |univ \ (Q_b union Q_v)|.

The exterior is NOT the global hole set; other vertices may cover
its words. The local diagonal theorem exhibits the exact third-centre
obstruction to upgrading it to genuine true-hole payment.

The original JSP-000404 six-source payment stays open.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Any two retained completion cubes with mutually incomparable
active palettes admit an explicit TWO-coordinate injection from
their intersection into the complement of their UNION.
No geometric AngleCap or one-layer budget is required. -/
theorem incomparable_completion_overlap_le_two_cube_exterior
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V)
    (hinc : ¬ retainedActive C b ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C b) :
    (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        (retainedCompletionWords C b ∪
          retainedCompletionWords C v)).card := by
  classical
  obtain ⟨cf, cr, hcfActiveB, _, hcrActiveV, hcrInactiveB, _⟩ :=
    incomparable_palettes_have_two_distinct_active_witnesses
      C b v hinc
  let src := retainedCompletionWords C b ∩
    retainedCompletionWords C v
  let dst := (Finset.univ : Finset (Fin n → Bool)) \
    (retainedCompletionWords C b ∪
      retainedCompletionWords C v)
  let f : {word : Fin n → Bool // word ∈ src} →
      {word : Fin n → Bool // word ∈ dst} :=
    fun x => ⟨flipCompletionWord cf (flipCompletionWord cr x.1),
      by
        have hw := Finset.mem_inter.mp x.2
        have hout :=
          two_flip_diagonal_outside_bridge_endpoints
            C b v cf cr x.1
            hcfActiveB hcrInactiveB hcrActiveV hw.1 hw.2
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _,
            fun h => (Finset.mem_union.mp h).elim hout.1 hout.2⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact double_flip_completion_word_injective cf cr
      (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hcard

/-- For a surviving palette-incomparable SOFT bridge, its dyadic
overlap mass is bounded by the local two-cube exterior volume.
The target exterior words may still belong to another cube. -/
theorem incomparable_bridge_mass_le_two_cube_exterior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (r : V × V)
    (hr : r ∈ incomparableBridgeSoftCarriers C exponent) :
    2 ^ (commonRetainedInactive C r.1 r.2).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        (retainedCompletionWords C r.1 ∪
          retainedCompletionWords C r.2)).card := by
  classical
  have hinc := (Finset.mem_filter.mp hr).2
  have hbridge := (Finset.mem_filter.mp hr).1
  have hsoft := (Finset.mem_filter.mp hbridge).1
  have hoverlap := ((mem_softOverlapCarrierPairs C r).1 hsoft).1
  obtain ⟨word, hw⟩ :=
    ((mem_overlapCarrierPairs C r).1 hoverlap).2
  have hcube := retainedCompletionWords_inter_card C
    (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
  rw [← hcube]
  exact incomparable_completion_overlap_le_two_cube_exterior
    C r.1 r.2 hinc

/-- In particular, all TWO-BIT candidate carriers inherit the
local exterior injection, but NO claim about global holes follows. -/
theorem two_bit_bridge_mass_le_two_cube_exterior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (r : V × V)
    (hr : r ∈ twoBitDisagreementBridgeCarriers C exponent) :
    2 ^ (commonRetainedInactive C r.1 r.2).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        (retainedCompletionWords C r.1 ∪
          retainedCompletionWords C r.2)).card := by
  exact incomparable_bridge_mass_le_two_cube_exterior
    C exponent r (Finset.mem_filter.mp hr).1

#print axioms incomparable_completion_overlap_le_two_cube_exterior
#print axioms incomparable_bridge_mass_le_two_cube_exterior
#print axioms two_bit_bridge_mass_le_two_cube_exterior

end OrderedEdgeColoring
end JSP000404Research
