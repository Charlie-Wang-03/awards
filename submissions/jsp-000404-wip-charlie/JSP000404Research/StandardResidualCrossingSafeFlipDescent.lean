import JSP000404Research.StandardResidualCrossingHardCredit
import JSP000404Research.ResidualSafeFlipBlocker
import Mathlib.Tactic

/-!
# Crossing hard carriers: a safe flip has finite descent on obstruction

Previous kernel-checked facts:
* two crossing unsafe hard overlap carriers with high middle exponent mass
  force a safe colour for the central residual edge a<v;
* for a same-retained hard middle edge without a common inactive colour,
  the safe colour is outgoing at a and inactive at v;
* an occupied one-bit flip is blocked either inside (resolving the hard
  pair into a retained-separated residual child) or strictly after v.

Here the exterior-blocker alternative is strengthened by genuine standard
residual triangle geometry: the new retained edge v--w has colour STRICTLY
LESS than the chosen safe colour c. Thus a potential endless external
blocker chain has a natural-number descent measure.

This is a local augmenting-path trichotomy; a hole in the retained CODE
image is not automatically a hole in the union of retained COMPLETION
CUBES. No global injection or complete JSP-000404 proof is claimed.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem crossing_unsafe_hard_high_mass_middle_flip_hole_resolve_or_descend
    {V : Type*} [LinearOrder V] [Fintype V]
    {t delta : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hn : 0 < n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hwidth : t < (n + 1 : ℕ))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x,
        (active (standardResidualColoring D n hwidth) x).card
          ≤ n - exponent x + 1)
    {u a v b : V}
    (hua : u < a) (hav : a < v) (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden
        (standardResidualColoring D n hwidth) u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden
        (standardResidualColoring D n hwidth) a b)
    (huWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) u)
    (hvWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) v)
    (haWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) a)
    (hbWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) b)
    (hmass : n ≤ exponent a + exponent v)
    (hsameAV :
      SameRetained (standardResidualColoring D n hwidth) a v)
    (hnoCommon :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive
          (standardResidualColoring D n hwidth) a ∧
        c ∉ retainedActive
          (standardResidualColoring D n hwidth) v) :
    let R := standardResidualColoring D n hwidth
    ∃ c : Fin n,
      c ∉ residualForbidden R a v ∧
      c ∈ outgoingRetained R a ∧
      c ∉ retainedActive R v ∧
      (
        (¬ ∃ w : V,
          (fun d => retainedBit R w d) =
            flippedRetainedCode R a c)
        ∨
        (∃ w : V,
          a < w ∧ w < v ∧
          IsResidual R w v ∧ RetainedSeparated R w v)
        ∨
        (∃ w : V,
          v < w ∧
          (fun d => retainedBit R w d) =
            flippedRetainedCode R a c ∧
          (R.color v w).val < c.val)
      ) := by
  classical
  let R := standardResidualColoring D n hwidth
  have hsafe :
      ∃ c : Fin n, c ∉ residualForbidden R a v :=
    crossing_unsafe_hard_carriers_high_mass_forces_safe_middle
      D hdeltaHalf ht hwidth exponent hexp honeLoss
      hua hav hvb hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord hmass
  obtain ⟨c, hcSafe⟩ := hsafe
  have hcout :=
    safe_hard_colour_outgoing_lower_inactive_upper
      D n hwidth hsameAV hnoCommon hcSafe
  have hresUV : IsResidual R u v :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hua.trans hav) huWord hvWord
  have hresAB : IsResidual R a b :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hav.trans hvb) haWord hbWord
  have hresAV : IsResidual R a v :=
    standardResidual_crossing_middle_edge
      D hwidth hua hav hvb hresUV hresAB
  have hblockCases :=
    safeFlip_hole_or_resolves_or_after_upper
      D n hn hwidth hav hresAV hsameAV
      hcout.1 hcout.2
  refine ⟨c, hcSafe, hcout.1, hcout.2, ?_⟩
  rcases hblockCases with hhole | hresolved | hafter
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hresolved)
  · right
    right
    obtain ⟨w, hvw, hcode⟩ := hafter
    have hblock : RetainedNeighbourBlocker R a c w :=
      (safeFlip_occupied_iff_blocker R a w c).1 hcode
    have hcol :
        R.color a w = c.castSucc :=
      safeFlip_blocker_edgeColor_eq
        R hav hsameAV hcout.1 hcout.2 hblock
    have hdesc : (R.color v w).val < c.val :=
      safe_hard_outer_witness_strict_band_descent
        D n hwidth hav hvw hresAV hcol hcout.2
    exact ⟨w, hvw, hcode, hdesc⟩

#print axioms crossing_unsafe_hard_high_mass_middle_flip_hole_resolve_or_descend

end DirectionData
end JSP000404Research
