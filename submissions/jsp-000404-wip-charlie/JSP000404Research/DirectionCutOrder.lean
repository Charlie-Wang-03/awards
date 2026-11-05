import JSP000404Research.OrderedDirections
import Mathlib.Order.RelClasses

/-!
# Projection cut orders from triangle betweenness

Flip an initially ordered pair precisely when its event value lies below a moving cut.
Triangle betweenness makes these pair comparisons a strict total order. With strict
betweenness, the two endpoints of a crossing are adjacent immediately before that event.
These are the first finite-order components of the cyclic-wire embedding bridge.
-/

namespace JSP000404Research
namespace DirectionCut

variable {V : Type*} [LinearOrder V]

/-- Pair order before the events at a given cut have been crossed. -/
def less (value : V → V → ℝ) (cut : ℝ) (i j : V) : Prop :=
  (i < j ∧ cut ≤ value i j) ∨ (j < i ∧ value j i < cut)

theorem less_irrefl (value : V → V → ℝ) (cut : ℝ) (i : V) : ¬less value cut i i := by
  simp [less]

theorem less_asymm (value : V → V → ℝ) (cut : ℝ) {i j : V}
    (hij : less value cut i j) : ¬less value cut j i := by
  rintro hreverse
  rcases hij with ⟨hij, hv⟩ | ⟨hji, hv⟩ <;>
    rcases hreverse with ⟨hji, hw⟩ | ⟨hij, hw⟩
  · exact (lt_asymm hij hji).elim
  · linarith
  · linarith
  · exact (lt_asymm hji hij).elim

theorem less_trichotomy (value : V → V → ℝ) (cut : ℝ) (i j : V) :
    less value cut i j ∨ i = j ∨ less value cut j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases hvalue : cut ≤ value i j
    · exact Or.inl (Or.inl ⟨hij, hvalue⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hij, lt_of_not_ge hvalue⟩))
  · exact Or.inr (Or.inl rfl)
  · by_cases hvalue : cut ≤ value j i
    · exact Or.inr (Or.inr (Or.inl ⟨hji, hvalue⟩))
    · exact Or.inl (Or.inr ⟨hji, lt_of_not_ge hvalue⟩)

theorem no_three_cycle (value : V → V → ℝ)
    (hbetween : ∀ {i j k}, i < j → j < k →
      (value i j ≤ value i k ∧ value i k ≤ value j k) ∨
      (value j k ≤ value i k ∧ value i k ≤ value i j))
    (cut : ℝ) {i j k : V}
    (hij : less value cut i j) (hjk : less value cut j k) (hki : less value cut k i) :
    False := by
  rcases hij with ⟨hij, ha⟩ | ⟨hji, ha⟩ <;>
    rcases hjk with ⟨hjk, hb⟩ | ⟨hkj, hb⟩ <;>
    rcases hki with ⟨hki, hc⟩ | ⟨hik, hc⟩
  · exact (lt_asymm (hij.trans hjk) hki).elim
  · rcases hbetween hij hjk with h | h <;> linarith
  · rcases hbetween hki hij with h | h <;> linarith
  · rcases hbetween hik hkj with h | h <;> linarith
  · rcases hbetween hjk hki with h | h <;> linarith
  · rcases hbetween hji hik with h | h <;> linarith
  · rcases hbetween hkj hji with h | h <;> linarith
  · exact (lt_asymm (hik.trans hkj) hji).elim

theorem less_trans (value : V → V → ℝ)
    (hbetween : ∀ {i j k}, i < j → j < k →
      (value i j ≤ value i k ∧ value i k ≤ value j k) ∨
      (value j k ≤ value i k ∧ value i k ≤ value i j))
    (cut : ℝ) {i j k : V}
    (hij : less value cut i j) (hjk : less value cut j k) : less value cut i k := by
  rcases less_trichotomy value cut i k with hik | rfl | hki
  · exact hik
  · exact (less_asymm value cut hij hjk).elim
  · exact (no_three_cycle value hbetween cut hij hjk hki).elim

/-- The cut comparisons define an actual linear order. -/
@[instance_reducible]
noncomputable def linearOrder (value : V → V → ℝ)
    (hbetween : ∀ {i j k}, i < j → j < k →
      (value i j ≤ value i k ∧ value i k ≤ value j k) ∨
      (value j k ≤ value i k ∧ value i k ≤ value i j))
    (cut : ℝ) : LinearOrder V := by
  classical
  letI : IsStrictTotalOrder V (less value cut) := {
    toTrichotomous := Std.trichotomous_of_rel_or_eq_or_rel_swap
      (fun {i j} ↦ less_trichotomy value cut i j)
    irrefl := less_irrefl value cut
    trans := fun _ _ _ ↦ less_trans value hbetween cut }
  exact linearOrderOfSTO (less value cut)

theorem crossing_endpoints_adjacent (value : V → V → ℝ)
    (hbetween : ∀ {i j k}, i < j → j < k →
      (value i j < value i k ∧ value i k < value j k) ∨
      (value j k < value i k ∧ value i k < value i j))
    {i j : V} (hij : i < j) :
    ¬∃ k, less value (value i j) i k ∧ less value (value i j) k j := by
  rintro ⟨k, hik, hkj⟩
  rcases hik with ⟨hik, ha⟩ | ⟨hki, ha⟩ <;>
    rcases hkj with ⟨hkj, hb⟩ | ⟨hjk, hb⟩
  · rcases hbetween hik hkj with h | h <;> linarith
  · rcases hbetween hij hjk with h | h <;> linarith
  · rcases hbetween hki hij with h | h <;> linarith
  · exact (lt_asymm (hij.trans hjk) hki).elim

theorem less_at_zero {width : ℝ} (D : DirectionData V width) {i j : V} :
    less D.value 0 i j ↔ i < j := by
  constructor
  · rintro (⟨hij, _⟩ | ⟨hji, hneg⟩)
    · exact hij
    · exact (not_lt_of_ge (D.nonnegative hji) hneg).elim
  · intro hij
    exact Or.inl ⟨hij, D.nonnegative hij⟩

theorem less_at_width {width : ℝ} (D : DirectionData V width) {i j : V} :
    less D.value width i j ↔ j < i := by
  constructor
  · rintro (⟨hij, hlarge⟩ | ⟨hji, _⟩)
    · exact (not_le_of_gt (D.belowWidth hij) hlarge).elim
    · exact hji
  · intro hji
    exact Or.inr ⟨hji, D.belowWidth hji⟩

#print axioms less_trans
#print axioms crossing_endpoints_adjacent
#print axioms less_at_zero
#print axioms less_at_width

end DirectionCut
end JSP000404Research
