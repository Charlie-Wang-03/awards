import JSP000404Research.ResidualRecolor
import Mathlib.Tactic

/-!
# Residual recolouring only needs absorption at saturated vertices

Suppose the retained old colours already satisfy

  card (retainedActive C v) <= ell v.

After residual edges are recoloured, every new active colour lies in

  retainedActive C v ∪ residualTargets R v.

Hence there is no need to absorb every residual target at every endpoint.
A vertex with a strict unit of slack may acquire one new target colour for
free.  Only vertices whose retained count is already equal to the budget must
force all incident residual targets back into the retained set.

The lemmas below isolate this weaker sufficient condition.  It is the natural
interface for the lower-half JSP-000404 problem: geometry only has to control
the saturated vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring
namespace ResidualRecoloring

/-- A retained-colour budget is saturated at a vertex. -/
def Saturated
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (ell : V → ℕ) (v : V) : Prop :=
  (retainedActive C v).card = ell v

/-- If a vertex has at least one unit of retained-colour slack, then adding
at most one new target colour still respects the budget. -/
theorem retained_union_singleton_card_le_of_slack
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (ell : V → ℕ) (v : V) (c : Fin k)
    (hret : (retainedActive C v).card < ell v) :
    (retainedActive C v ∪ {c}).card ≤ ell v := by
  classical
  have hcard :
      (retainedActive C v ∪ {c}).card ≤
        (retainedActive C v).card + 1 := by
    calc
      (retainedActive C v ∪ {c}).card
          ≤ (retainedActive C v).card + ({c} : Finset (Fin k)).card := by
            exact Finset.card_union_le _ _
      _ = (retainedActive C v).card + 1 := by simp
  omega

/-- Pointwise criterion: retained colours are within budget, and either the
vertex has slack or every residual target used there is already retained. -/
theorem union_budget_of_slack_or_absorbed
    {V : Type*} [LinearOrder V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (ell : V → ℕ)
    (hret : ∀ v, (retainedActive C v).card ≤ ell v)
    (hlocal : ∀ v,
      (retainedActive C v).card < ell v ∨
      R.residualTargets v ⊆ retainedActive C v)
    (hone : ∀ v, (R.residualTargets v).card ≤ 1) :
    ∀ v,
      (retainedActive C v ∪ R.residualTargets v).card ≤ ell v := by
  classical
  intro v
  rcases hlocal v with hslack | habs
  · by_cases hzero : R.residualTargets v = ∅
    · simp [hzero, hret v]
    · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
      have hsub : R.residualTargets v ⊆ {c} := by
        intro d hd
        have hcard := hone v
        have hcd : {c, d} ⊆ R.residualTargets v := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hpair := Finset.card_le_card hcd
        by_cases hdc : d = c
        · subst d
          simp
        · have : ({c, d} : Finset (Fin k)).card = 2 := by
            simp [hdc]
          rw [this] at hpair
          omega
      calc
        (retainedActive C v ∪ R.residualTargets v).card
            ≤ (retainedActive C v ∪ {c}).card := by
              exact Finset.card_le_card (Finset.union_subset_union
                (fun _ h => h) hsub)
        _ ≤ ell v :=
          retained_union_singleton_card_le_of_slack ell v c hslack
  · have hunion :
        retainedActive C v ∪ R.residualTargets v =
          retainedActive C v := by
      exact Finset.union_eq_left.mpr habs
    rw [hunion]
    exact hret v

/-- Capacity outlet under the saturated-vertex formulation. -/
theorem cluster_capacity_of_saturated_absorption
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    {C : OrderedEdgeColoring V (k + 1)}
    (R : ResidualRecoloring C)
    (exponent ell : V → ℕ)
    (hexponent : ∀ v, exponent v ≤ k)
    (hell : ∀ v, ell v = k - exponent v)
    (hret : ∀ v, (retainedActive C v).card ≤ ell v)
    (hlocal : ∀ v,
      (retainedActive C v).card < ell v ∨
      R.residualTargets v ⊆ retainedActive C v)
    (hone : ∀ v, (R.residualTargets v).card ≤ 1) :
    ∑ v, 2 ^ exponent v ≤ 2 ^ k := by
  apply cluster_capacity_of_recoloring_budget
    R exponent ell hexponent hell
  exact union_budget_of_slack_or_absorbed R ell hret hlocal hone

#print axioms retained_union_singleton_card_le_of_slack
#print axioms union_budget_of_slack_or_absorbed
#print axioms cluster_capacity_of_saturated_absorption

end ResidualRecoloring
end OrderedEdgeColoring
end JSP000404Research
