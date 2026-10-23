import JSP000404Research.SixPointBoundaryCutDichotomy
import Mathlib.Tactic

/-!
# All-delta six-centre geometric boundary alternative at n>=7

Because 0<=delta<1/2 and n>=7, the precise full-delta-arc sampling
condition 13*delta<n is automatic; the authentic no-compensated-top
six-centre profile always admits either two distinct non-gaining support-two
minima, or a *real* projective cut with coherently separated boundary bands.
This does not resolve global Boolean-hole or dyadic-surplus payment.
-/

namespace JSP000404Research

theorem thirteen_delta_lt_n_of_seven_le
    {n : ℕ} {delta : ℝ}
    (hn : 7 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    13 * delta < (n : ℝ) := by
  have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem six_point_n_ge_seven_two_support_two_or_boundary_bipartite_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn7 : 7 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop : SixPointNoCompensatedTopDeletion
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
  exact six_point_hard_top_two_support_two_or_boundary_bipartite_cut
    hp hcap C hcard (by omega : 5 ≤ n)
    hdelta0 hdeltaHalf ht hlam
    (thirteen_delta_lt_n_of_seven_le hn7 hdeltaHalf)
    top hTop hMin hNoTop

#print axioms thirteen_delta_lt_n_of_seven_le
#print axioms six_point_n_ge_seven_two_support_two_or_boundary_bipartite_cut

end JSP000404Research
