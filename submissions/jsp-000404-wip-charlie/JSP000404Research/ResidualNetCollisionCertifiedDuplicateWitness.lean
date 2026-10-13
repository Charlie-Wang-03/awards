import JSP000404Research.ResidualNetCollisionCertifiedBlockerClassification
import Mathlib.Tactic

/-!
# Exact witness extraction from POSITIVE genuine collision-target duplication

The actual NET-collision diagonal map has source-dependent but
CANONICALLY determined forward/reverse flip colours.

A positive global duplicate-image debt cannot remain an abstract
numerical difference: it forces two DISTINCT genuine NET sink
collision words with the SAME canonical two-flip target.
Their original sink words must agree outside the union of the
FOUR (possibly repeated) canonically selected flip coordinates.

This produces a concrete, witness-level target for the next
planar exclusion or separate duplicate payment. It does not
claim that duplicate debt is always zero.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every POSITIVE exact duplicate debt witnesses TWO DISTINCT
genuine NET collision source words that hit the SAME ACTUAL
canonical diagonal. No injectivity is assumed. -/
theorem net_collision_positive_duplicate_has_distinct_source_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    ∃ s t : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss},
      s ≠ t ∧
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t := by
  classical
  by_contra hnone
  have hinj : Function.Injective
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss) := by
    intro s t heq
    by_contra hne
    exact hnone ⟨s, t, hne, heq⟩
  have hcard :
      (netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss).card =
      (netActualForwardReverseCollisionWords
        C exponent hexp honeLoss).card := by
    unfold netCollisionCertifiedDiagonalWords
    rw [Finset.card_image_of_injective _ hinj]
    simp only [Finset.card_univ, Fintype.card_coe]
  unfold netCollisionCertifiedDuplicateDebt at hpositive
  omega

/-- If TWO actual canonical diagonals coincide, their original
NET collision sink words agree at every coordinate outside
their four ORIGINAL transport flip-colour coordinates. The
coordinate pairs may vary with the actual source. -/
theorem net_collision_certified_same_diagonal_agree_off_four
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (heq :
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (e : Fin n)
    (hsf : e ≠ transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)))
    (hsr : e ≠ strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)))
    (htf : e ≠ transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)))
    (htr : e ≠ strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss t))) :
    s.1 e = t.1 e := by
  exact double_flip_target_eq_source_agree_outside_four
    s.1 t.1
    (transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)))
    (strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)))
    (transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)))
    (strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)))
    (by simpa only [netCollisionCertifiedDiagonal] using heq)
    e hsf hsr htf htr

/-- An exact concrete DUPLICATE obstruction: if the duplicate mass
is positive, two distinct original NET collision sink words are
related by a four-coordinate Boolean difference. This is the
actual geometrically meaningful alternative to falsely treating
all canonical diagonals as globally non-reusing. -/
theorem net_collision_positive_duplicate_forces_four_coordinate_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    ∃ s t : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss},
      s ≠ t ∧
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t ∧
      ∀ e : Fin n,
        e ≠ transportablePairColor C
          (transportableWordCarrier C
            (netCollisionCertifiedForwardSource
              C exponent hexp honeLoss s)) →
        e ≠ strictDescentRigidPairColor C exponent hexp honeLoss
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource
              C exponent hexp honeLoss s)) →
        e ≠ transportablePairColor C
          (transportableWordCarrier C
            (netCollisionCertifiedForwardSource
              C exponent hexp honeLoss t)) →
        e ≠ strictDescentRigidPairColor C exponent hexp honeLoss
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource
              C exponent hexp honeLoss t)) →
        s.1 e = t.1 e := by
  obtain ⟨s, t, hne, heq⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
  refine ⟨s, t, hne, heq, ?_⟩
  intro e hsf hsr htf htr
  exact net_collision_certified_same_diagonal_agree_off_four
    C exponent hexp honeLoss s t heq e hsf hsr htf htr

#print axioms net_collision_positive_duplicate_has_distinct_source_pair
#print axioms net_collision_certified_same_diagonal_agree_off_four
#print axioms net_collision_positive_duplicate_forces_four_coordinate_pair

end OrderedEdgeColoring
end JSP000404Research
