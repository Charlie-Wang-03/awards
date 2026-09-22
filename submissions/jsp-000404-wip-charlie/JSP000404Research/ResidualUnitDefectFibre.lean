
import JSP000404Research.ResidualCompletionIntersection
import JSP000404Research.ResidualDuplicateBudget
import Mathlib.Tactic

/-!
# Duplicate fibres reduce to an internal unit defect

Assume the global one-layer active-colour estimate

  card(active(v)) <= n - exponent(v) + 1

and exponent(v) <= n.

For a duplicated retained-code fibre u<v, the residual colour is active at
both endpoints.  Hence ResidualDuplicateBudget upgrades the projected retained
budgets to

  exponent(u) <= n-card(retainedActive(u)),
  exponent(v) <= n-card(retainedActive(v)).

If the pair has no common inactive retained coordinate, the two retained
completion cubes meet in exactly one Boolean word.

Consequently there are only two possibilities.

* At least one endpoint has strict retained free-coordinate slack.  Then the
  entire target dyadic mass 2^ku+2^kv fits inside the union of the two retained
  completion cubes.

* Both endpoints saturate their retained free dimensions.  Then the target
  dyadic mass exceeds that union by exactly one Boolean word.

Thus a no-common-inactive duplicate fibre never creates an exponential
packing deficit.  Its only unresolved internal obstruction is a single code.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def NoCommonInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Prop :=
  ¬ ∃ c : Fin n,
    c ∉ retainedActive C u ∧
    c ∉ retainedActive C v

def RetainedSaturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Prop :=
  exponent v = n - (retainedActive C v).card

def UnitDefectDuplicate
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (u v : V) : Prop :=
  SameRetained C u v ∧
  NoCommonInactive C u v ∧
  RetainedSaturated C exponent u ∧
  RetainedSaturated C exponent v

/-- Every duplicated fibre is exactly-budgeted after dropping the active
residual coordinate. -/
theorem duplicate_exponent_le_projected_free
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    exponent u ≤ n - (retainedActive C u).card ∧
    exponent v ≤ n - (retainedActive C v).card := by
  have hpair :=
    sameRetained_exact_pair_budget
      C exponent honeLoss huv hsame
  have huN := hexp u
  have hvN := hexp v
  omega

/-- Main fibre-level dichotomy under the actual one-layer global hypothesis. -/
theorem duplicate_completion_oneLayer_dichotomy
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hno : NoCommonInactive C u v) :
    (2 ^ exponent u + 2 ^ exponent v ≤
      (retainedCompletionWords C u ∪
        retainedCompletionWords C v).card)
    ∨
    (UnitDefectDuplicate C exponent u v ∧
      2 ^ exponent u + 2 ^ exponent v =
        (retainedCompletionWords C u ∪
          retainedCompletionWords C v).card + 1) := by
  have hbudget :=
    duplicate_exponent_le_projected_free
      C exponent hexp honeLoss huv hsame
  rcases duplicate_completion_internal_dichotomy
      C exponent hsame hno hbudget.1 hbudget.2 with hfit | hunit
  · exact Or.inl hfit
  · right
    refine ⟨?_, hunit.2.2⟩
    exact ⟨hsame, hno, hunit.1, hunit.2.1⟩

/-- In the unit-defect branch, the shortfall is literally one. -/
theorem unitDefectDuplicate_exact_shortfall
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hunit : UnitDefectDuplicate C exponent u v) :
    2 ^ exponent u + 2 ^ exponent v =
      (retainedCompletionWords C u ∪
        retainedCompletionWords C v).card + 1 := by
  exact duplicate_target_mass_eq_completion_union_add_one_of_both_saturated
    C exponent hunit.1 hunit.2.1 hunit.2.2.1 hunit.2.2.2

/-- Unit-defect status is symmetric in the two endpoints. -/
theorem unitDefectDuplicate_symm
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (h : UnitDefectDuplicate C exponent u v) :
    UnitDefectDuplicate C exponent v u := by
  refine ⟨sameRetained_symm h.1, ?_, h.2.2.2, h.2.2.1⟩
  unfold NoCommonInactive at h ⊢
  intro hex
  obtain ⟨c, hcv, hcu⟩ := hex
  exact h.2.1 ⟨c, hcu, hcv⟩

#print axioms duplicate_exponent_le_projected_free
#print axioms duplicate_completion_oneLayer_dichotomy
#print axioms unitDefectDuplicate_exact_shortfall
#print axioms unitDefectDuplicate_symm

end OrderedEdgeColoring
end JSP000404Research
