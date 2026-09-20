import JSP000404Research.ResidualLists
import JSP000404Research.ResidualSafeTarget
import Mathlib.Tactic

/-!
# Residual forbidden-list capacity

For ordinary cardinality, eliminating the short residual colour is easier than
the weighted absorption problem.

For a residual increasing edge `u<v`, a retained target is safe exactly when
it avoids the local forbidden set

  incomingRetained(u) union outgoingRetained(v).

Residual edges never form an increasing two-edge path, so these safe target
choices are independent.  Consequently, if every residual edge has a proper
forbidden subset of the `k` retained colours, all residual edges can be
recoloured and the ordinary Hansel bound gives `|V| <= 2^k`.

This isolates a substantially weaker geometric target than common inactivity
or absorbed recolouring.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Choose a locally safe retained target for every residual edge.  Values on
non-residual/non-increasing pairs are irrelevant and are set to colour zero. -/
noncomputable def targetOfForbiddenCardLt
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (hk : 0 < k)
    (hcard : ∀ {u v : V}, u < v → IsResidual C u v →
      (residualForbidden C u v).card < k) :
    V → V → Fin k :=
  fun u v =>
    if h : u < v ∧ IsResidual C u v then
      Classical.choose
        (exists_compatible_target_of_forbidden_card_lt
          C (hcard h.1 h.2))
    else
      ⟨0, hk⟩

/-- The chosen targets satisfy the exact local compatibility condition. -/
theorem targetOfForbiddenCardLt_compatible
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (hk : 0 < k)
    (hcard : ∀ {u v : V}, u < v → IsResidual C u v →
      (residualForbidden C u v).card < k) :
    ResidualTargetCompatible C
      (targetOfForbiddenCardLt C hk hcard) := by
  intro u v huv hres
  unfold targetOfForbiddenCardLt
  simp only [dif_pos ⟨huv, hres⟩]
  exact Classical.choose_spec
    (exists_compatible_target_of_forbidden_card_lt
      C (hcard huv hres))

/-- Proper local forbidden lists eliminate the residual colour globally. -/
noncomputable def recoloringOfForbiddenCardLt
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (hk : 0 < k)
    (hcard : ∀ {u v : V}, u < v → IsResidual C u v →
      (residualForbidden C u v).card < k) :
    ResidualRecoloring C :=
  residualRecoloringOfCompatible
    (targetOfForbiddenCardLt C hk hcard)
    (targetOfForbiddenCardLt_compatible C hk hcard)

/-- Main cardinality outlet: every residual edge having one locally safe
retained colour already implies the sharp `2^k` bound. -/
theorem card_le_two_pow_of_residualForbidden_card_lt
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (hk : 0 < k)
    (hcard : ∀ {u v : V}, u < v → IsResidual C u v →
      (residualForbidden C u v).card < k) :
    Fintype.card V ≤ 2 ^ k := by
  let R := recoloringOfForbiddenCardLt C hk hcard
  exact card_le_two_pow R.toOrderedEdgeColoring

/-- Equivalent missing-colour formulation convenient for geometry. -/
theorem card_le_two_pow_of_residual_safe_colour
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    (hk : 0 < k)
    (hsafe : ∀ {u v : V}, u < v → IsResidual C u v →
      ∃ c : Fin k, c ∉ residualForbidden C u v) :
    Fintype.card V ≤ 2 ^ k := by
  apply card_le_two_pow_of_residualForbidden_card_lt C hk
  intro u v huv hres
  obtain ⟨c, hc⟩ := hsafe huv hres
  have hle : (residualForbidden C u v).card ≤ k := by
    simpa using Finset.card_le_univ (residualForbidden C u v)
  by_contra hnot
  have heq : (residualForbidden C u v).card = k := by
    omega
  have hall : residualForbidden C u v = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using heq)
  apply hc
  rw [hall]
  simp

#print axioms targetOfForbiddenCardLt_compatible
#print axioms recoloringOfForbiddenCardLt
#print axioms card_le_two_pow_of_residualForbidden_card_lt
#print axioms card_le_two_pow_of_residual_safe_colour

end OrderedEdgeColoring
end JSP000404Research
