import JSP000404Research.ResidualTwoFlipExactSymmetricDifference
import Mathlib.Tactic

/-!
# Genuine NET transport: exact source-difference support under diagonal reuse

The two canonical selected colours of every ACTUAL NET hard transport
collision are distinct, by the existing certified original-source
hardness theorem. Thus the preceding exact symmetric-difference
Boolean identity is now available WITHOUT extra assumptions for
every pair of actual collision sink words with the same canonical
diagonal target.

In particular, SAME UNORDERED pair of actual chosen transport
colours plus SAME target forces SAME original collision sink.
A positive duplicate debt must therefore involve genuinely
DIFFERENT unordered pairs of selected colours.

This is a stronger necessary obstruction than the earlier
outside-four agreement lemma, but no planar exclusion of such
two/four-coordinate witness pairs is claimed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Both genuine transport flip colours at each actual NET
collision are distinct; this is not a new assumed property. -/
theorem net_collision_certified_forward_reverse_colours_distinct
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    transportablePairColor C (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) ≠
    strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) := by
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  have hw := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss s
  exact forward_reverse_actual_collision_distinct_flip_colors
    C exponent hexp honeLoss x y (hw.1.trans hw.2.symm)

/-- If two DISTINCT actual NET collision words have the same
canonical double-flip diagonal, their original Boolean words
disagree EXACTLY on the symmetric difference of the two
genuinely selected unordered two-colour supports. -/
theorem net_collision_canonical_diagonal_exact_difference_support
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
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t) :
    let cfS := transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s))
    let crS := strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s))
    let cfT := transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss t))
    let crT := strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss t))
    (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)) =
      (({cfS, crS} : Finset (Fin n)) \ ({cfT, crT} : Finset (Fin n))) ∪
      (({cfT, crT} : Finset (Fin n)) \ ({cfS, crS} : Finset (Fin n))) := by
  have hS := net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss s
  have hT := net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss t
  exact two_flip_equal_target_exact_difference_set s.1 t.1
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
    hS hT (by simpa only [netCollisionCertifiedDiagonal] using heq)

/-- There is NO repetition of the canonical actual diagonal within
a fixed UNORDERED two-colour support class. The previous separate
fixed-ordered-pair injection has been upgraded to unordered pairs,
including a SWAP of the forward and reverse flip colours. -/
theorem net_collision_canonical_same_target_same_unordered_pair_eq
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
    (hsame :
      ({transportablePairColor C (transportableWordCarrier C
         (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)),
        strictDescentRigidPairColor C exponent hexp honeLoss
         (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s))}
       : Finset (Fin n)) =
      ({transportablePairColor C (transportableWordCarrier C
         (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)),
        strictDescentRigidPairColor C exponent hexp honeLoss
         (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss t))}
       : Finset (Fin n))) :
    s = t := by
  have hS := net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss s
  have hT := net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss t
  apply Subtype.ext
  exact two_flip_equal_target_same_support_source_eq s.1 t.1
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
    hS hT (by simpa only [netCollisionCertifiedDiagonal] using heq)
    hsame

#print axioms net_collision_certified_forward_reverse_colours_distinct
#print axioms net_collision_canonical_diagonal_exact_difference_support
#print axioms net_collision_canonical_same_target_same_unordered_pair_eq

end OrderedEdgeColoring
end JSP000404Research
