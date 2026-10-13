import JSP000404Research.ResidualNetCollisionSupportOverlapLaw
import Mathlib.Tactic

/-!
# Global certified NET diagonal multiplicity bound via unordered flip pairs

The actual canonical NET collision diagonal is generally NOT known
to be globally injective. However, its PAIR with the unordered set
of the two ORIGINAL transport flip colours IS globally injective.
The second component is a genuine two-element subset of Fin n.

Therefore any single diagonal can be hit by at most (n choose 2)
different actual NET source words, and in aggregate

  |NET actual collisions| <= (n choose 2) * |distinct canonical diagonals|.

This is an unconditional bound on genuine (not candidate) collision
multiplicity, with NO assumption of unavailable global hole credit.
It does not replace the six-source true-hole/surplus payment proof.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The PRODUCT of the actual canonical diagonal and the original
two-colour support is injective on ALL actual NET collision sources,
although neither projection alone need be globally injective. -/
theorem net_collision_diagonal_support_pair_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Function.Injective
      (fun s : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss} =>
          (netCollisionCertifiedDiagonal C exponent hexp honeLoss s,
           netCollisionCanonicalColourSupport C exponent hexp honeLoss s)) := by
  intro s t h
  exact net_collision_canonical_support_fibre_injective
    C exponent hexp honeLoss s t
    (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A globally valid multiplicity cap for the ACTUAL net hard-source
sink collisions. The upper bound counts distinct diagonal words
times the number of possible unordered two-colour supports.
In particular no diagonal gets more than choose(n,2) distinct
actual sources. This is not an all-hole payment: some diagonals
are globally covered and remain a separate geometric debt. -/
theorem net_collision_card_le_choose_two_times_distinct_diagonal_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords
      C exponent hexp honeLoss).card ≤
      (netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss).card * Nat.choose n 2 := by
  classical
  let I := netActualForwardReverseCollisionWords
    C exponent hexp honeLoss
  let Src := {w : Fin n → Bool // w ∈ I}
  let D := netCollisionCertifiedDiagonalWords
    C exponent hexp honeLoss
  let P := (Finset.univ : Finset (Fin n)).powersetCard 2
  let f : Src → (Fin n → Bool) × Finset (Fin n) :=
    fun s => (netCollisionCertifiedDiagonal C exponent hexp honeLoss s,
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s)
  have hinj : Function.Injective f :=
    net_collision_diagonal_support_pair_injective
      C exponent hexp honeLoss
  have hsubset :
      (Finset.univ : Finset Src).image f ⊆ D.product P := by
    intro p hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    constructor
    · unfold D netCollisionCertifiedDiagonalWords
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.subset_univ _
      · have hdistinct :=
          net_collision_certified_forward_reverse_colours_distinct
            C exponent hexp honeLoss s
        simpa [netCollisionCanonicalColourSupport] using
          (show
            ({transportablePairColor C (transportableWordCarrier C
                 (netCollisionCertifiedForwardSource
                   C exponent hexp honeLoss s)),
               strictDescentRigidPairColor C exponent hexp honeLoss
                 (strictDescentRigidWordCarrier C exponent
                   (netCollisionCertifiedReverseSource
                     C exponent hexp honeLoss s))}
                 : Finset (Fin n)).card = 2 by
             simp [hdistinct])
  change I.card ≤ D.card * Nat.choose n 2
  calc
    I.card = (Finset.univ : Finset Src).card := by
      simp [Src, Fintype.card_coe]
    _ = ((Finset.univ : Finset Src).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (D.product P).card := Finset.card_le_card hsubset
    _ = D.card * Nat.choose n 2 := by
      simp [P]

#print axioms net_collision_diagonal_support_pair_injective
#print axioms net_collision_card_le_choose_two_times_distinct_diagonal_card

end OrderedEdgeColoring
end JSP000404Research
