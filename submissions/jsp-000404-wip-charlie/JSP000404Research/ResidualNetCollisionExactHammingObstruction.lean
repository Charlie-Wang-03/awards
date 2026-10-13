import JSP000404Research.ResidualTwoFlipExactHammingCases
import Mathlib.Tactic

/-!
# Positive ACTUAL NET collision duplicate debt: an exact 2-or-4-bit witness

The preceding general Boolean lemma proves that equality of two
genuine two-bit-flip targets forces source distance 0, 2, or 4.
For DISTINCT sources the distance is 2 or 4.

Here every flip is the ACTUAL uniquely selected forward/reverse
transport colour of one genuine NET collision sink word. Positive
global canonical duplicate-image debt therefore forces a pair of
distinct actual sink words differing in EXACTLY two or four bits,
AND their unordered original transport colour supports MUST differ.

This is a bona fide sharpening of the open global payment's
collision-duplication obstruction, but not yet an AngleCap
exclusion or a debit against unreserved dyadic surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Genuine unordered transport flip-colour support of an ACTUAL
NET collision sink, identified via its unique original hard sources. -/
noncomputable def netCollisionCanonicalColourSupport
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) : Finset (Fin n) :=
  {transportablePairColor C (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)),
   strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s))}

/-- No two distinct NET sources with the same unordered canonical
transport-colour pair can hit the same diagonal, even if their
forward/reverse selected roles are swapped. -/
theorem net_collision_canonical_support_fibre_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (htarget : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hsupport : netCollisionCanonicalColourSupport
        C exponent hexp honeLoss s =
      netCollisionCanonicalColourSupport
        C exponent hexp honeLoss t) :
    s = t := by
  exact net_collision_canonical_same_target_same_unordered_pair_eq
    C exponent hexp honeLoss s t htarget hsupport

/-- If actual duplicate debt is POSITIVE, then two different
genuine NET sink words hit the SAME canonical opposite diagonal,
their unordered transport colour supports are DIFFERENT, and
their Hamming distance is exactly TWO or FOUR. -/
theorem net_collision_positive_duplicate_cross_support_hamming_two_or_four
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
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s ≠
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t ∧
      ((Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card = 2 ∨
       (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card = 4) := by
  classical
  obtain ⟨s, t, hne, heq⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
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
  have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s ≠
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
    intro hsame
    exact hne (net_collision_canonical_support_fibre_injective
      C exponent hexp honeLoss s t heq hsame)
  have hword : s.1 ≠ t.1 := by
    intro hval
    exact hne (Subtype.ext hval)
  have hcolS : cfS ≠ crS :=
    net_collision_certified_forward_reverse_colours_distinct
      C exponent hexp honeLoss s
  have hcolT : cfT ≠ crT :=
    net_collision_certified_forward_reverse_colours_distinct
      C exponent hexp honeLoss t
  have hdiag :
      flipCompletionWord cfS (flipCompletionWord crS s.1) =
      flipCompletionWord cfT (flipCompletionWord crT t.1) := by
    simpa only [netCollisionCertifiedDiagonal] using heq
  have hamming :=
    two_flip_equal_target_distinct_sources_hamming_two_or_four
      s.1 t.1 cfS crS cfT crT hcolS hcolT hdiag hword
  exact ⟨s, t, hne, heq, hsupport, hamming⟩

#print axioms net_collision_canonical_support_fibre_injective
#print axioms net_collision_positive_duplicate_cross_support_hamming_two_or_four

end OrderedEdgeColoring
end JSP000404Research
