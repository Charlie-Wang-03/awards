import JSP000404Research.PlanarNetLowColourNoDuplicate
import JSP000404Research.ResidualNetCollisionSupportOverlapLaw
import Mathlib.Tactic

/-!
# First potentially nontrivial low-colour NET duplication: n=3

The actual NET duplicate-image debt is ZERO for n<=2, now
verified both for abstract one-layer ordered edge colourings and
for the actual planar AngleCap residual colouring.

For 3 retained colours, positive genuine duplicate debt still
cannot have the general four-bit Hamming obstruction: at most
three coordinates exist. Hence every positive-debt witness must
consist of TWO distinct source words differing at EXACTLY TWO
Boolean coordinates, with original two-flip colour supports
having EXACTLY ONE colour in common.

This removes the disjoint-flip-support, four-bit branch completely
for n<=3, but it DOES NOT rule out the remaining two-bit branch.
Therefore it does not discharge the planar global six-source
payment sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- With no more than THREE retained colours, every pair of
Boolean source words differs at most three coordinates. Thus
the four-bit collision alternative is mathematically impossible. -/
theorem bool_words_hamming_ne_four_of_n_le_three
    {n : ℕ} (hn : n ≤ 3) (s t : Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin n => s i ≠ t i)).card ≠ 4 := by
  classical
  have hle :
      (Finset.univ.filter (fun i : Fin n => s i ≠ t i)).card ≤
      (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hlt :
      (Finset.univ.filter (fun i : Fin n => s i ≠ t i)).card ≤ n := by
    simpa using hle
  omega

/-- Genuine positive duplicate target debt is strongly constrained
when n<=3: the two distinct actual NET sink source words must have
EXACTLY two differing Boolean coordinates AND their two selected
canonical original-flip colour supports have ONE common colour.
This includes the first nontrivial n=3 case, while n<=2 was
already excluded unconditionally. -/
theorem net_collision_positive_duplicate_n_le_three_forces_two_bits_one_common
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 3)
    (hpositive : 0 <
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss) :
    ∃ s t : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss},
      s ≠ t ∧
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
        netCollisionCertifiedDiagonal C exponent hexp honeLoss t ∧
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s ≠
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t ∧
      (Finset.univ.filter (fun i : Fin n => s.1 i ≠ t.1 i)).card = 2 ∧
      (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card = 1 := by
  classical
  obtain ⟨s, t, hst, hdiag, hsupport, hham⟩ :=
    net_collision_positive_duplicate_cross_support_hamming_two_or_four
      C exponent hexp honeLoss hpositive
  have htwo :
      (Finset.univ.filter (fun i : Fin n => s.1 i ≠ t.1 i)).card = 2 := by
    rcases hham with h2 | h4
    · exact h2
    · exact False.elim
        ((bool_words_hamming_ne_four_of_n_le_three hn s.1 t.1) h4)
  have hcommon :=
    (net_collision_equal_diagonal_two_bits_iff_one_common_colour
      C exponent hexp honeLoss s t hdiag).mp htwo
  exact ⟨s, t, hst, hdiag, hsupport, htwo, hcommon⟩

#print axioms bool_words_hamming_ne_four_of_n_le_three
#print axioms net_collision_positive_duplicate_n_le_three_forces_two_bits_one_common

end OrderedEdgeColoring
end JSP000404Research
