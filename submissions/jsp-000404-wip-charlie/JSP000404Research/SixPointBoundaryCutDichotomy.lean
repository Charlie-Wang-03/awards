import JSP000404Research.PositiveArcSafeCutExistence
import JSP000404Research.SixPointFullDeltaArcDichotomy
import Mathlib.Tactic

/-! Original-geometry six-centre hard-branch structural alternative:
two distinct non-gaining support-two minima, or an actual projective cut
whose boundary 0/n edges have a coherent Boolean two-colouring.
No global true-hole/dyadic surplus payment is inferred. -/
namespace JSP000404Research

theorem six_point_hard_top_two_support_two_or_boundary_bipartite_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hthreshold : 13 * delta < (n : ℝ))
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      a ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      b ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2) ∨
    (∃ c : ℝ, ∃ hc0 : 0 ≤ c, ∃ hcpi : c < Real.pi,
      let htpos : 0 < t := by
        exact sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
      let htop : t < (n + 1 : ℕ) := by
        rw [ht]; push_cast; linarith
      let P := cutProjectiveBandPartition hp hcap htpos hlam hc0 hcpi n htop
      let bit := cutBoundaryWrapBit (delta := delta) hp n htpos htop hc0 hcpi
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨ (P.edgeColor u v).val = n) →
        bit u ≠ bit v) := by
  rcases six_point_hard_top_two_support_two_or_full_deltaArc_escape
    hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
    hthreshold top hTop hMin hNoTop with htwo | hsafe
  · exact Or.inl htwo
  · right
    obtain ⟨x, hx0, hxt, hArc⟩ := hsafe
    exact exists_boundary_cut_coloring_of_full_positive_deltaArc_safe
      hp hcap C (by omega : 1 ≤ n)
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
      hlam ht hdelta0 hdeltaHalf hx0 hxt hArc

#print axioms six_point_hard_top_two_support_two_or_boundary_bipartite_cut

end JSP000404Research
