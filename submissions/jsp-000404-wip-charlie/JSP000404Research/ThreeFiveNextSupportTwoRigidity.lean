import JSP000404Research.NoTopNextLayerTwoSupportTwo
import Mathlib.Tactic

/-!
# Saturated quotient profile in the n=3 no-top four-next motif

For an actual exponent-one centre with positive support two, the
zero-carry identity gives total quotient sum exactly 3.  Since
floorExcess is exactly one, no quotient can exceed 2.

Four distinct next-layer centres in the no-top five-centre motif
already force at least two support-two centres by genuine AngleCap
transition packing.  These two consequently have this saturated
quotient mass profile.  The motif remains geometrically open.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exact arithmetic rigidity: exponent one and support two imply
total quotient mass 3 and every quotient at most 2. -/
theorem exponent_one_support_two_exact_mass
    {I : Type*} [Fintype I] (q : I → ℕ)
    (hEx : floorExcess q = 1)
    (hSup : positiveSupport q = 2) :
    (∑ r, q r) = 3 ∧ ∀ r, q r ≤ 2 := by
  have hsum := floorExcess_add_positiveSupport q
  have hmass : (∑ r, q r) = 3 := by omega
  refine ⟨hmass, ?_⟩
  intro r
  have hterm : q r - 1 ≤ floorExcess q := by
    unfold floorExcess
    exact Finset.single_le_sum
      (f := fun j => q j - 1)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  omega

/-- Concrete saturated support-two next-layer profile. -/
def nextSaturatedSupportTwo
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) (t : ℝ) : Prop :=
  positiveSupport (centreQuotient C t) = 2 ∧
  (∑ r, centreQuotient C t r) = 3 ∧
  (∀ r, centreQuotient C t r ≤ 2)

theorem next_saturated_of_exponent_one_support_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) {t : ℝ}
    (hEx : centreExponent C t = 1)
    (hSup : positiveSupport (centreQuotient C t) = 2) :
    nextSaturatedSupportTwo C t := by
  have hfloor : floorExcess (centreQuotient C t) = 1 := by
    simpa [centreExponent] using hEx
  obtain ⟨hMass,hBound⟩ :=
    exponent_one_support_two_exact_mass
      (centreQuotient C t) hfloor hSup
  exact ⟨hSup,hMass,hBound⟩

/-- Two of any four genuine exponent-one n=3 next-layer centres have
exactly three quotient mass units, supported on two gaps of size 1 or 2. -/
theorem two_saturated_next_among_four_n3
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = 1)
    (hA : centreExponent Ca t = 1)
    (hB : centreExponent Cb t = 1)
    (hC : centreExponent Cc t = 1) :
    (nextSaturatedSupportTwo Cs t ∧ nextSaturatedSupportTwo Ca t) ∨
    (nextSaturatedSupportTwo Cs t ∧ nextSaturatedSupportTwo Cb t) ∨
    (nextSaturatedSupportTwo Cs t ∧ nextSaturatedSupportTwo Cc t) ∨
    (nextSaturatedSupportTwo Ca t ∧ nextSaturatedSupportTwo Cb t) ∨
    (nextSaturatedSupportTwo Ca t ∧ nextSaturatedSupportTwo Cc t) ∨
    (nextSaturatedSupportTwo Cb t ∧ nextSaturatedSupportTwo Cc t) := by
  have hpair := two_support_two_among_four_second_layer_centres
    hp hcap (by omega : 3 ≤ (3 : ℕ)) hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc Cs Ca Cb Cc
    (by simpa using hS) (by simpa using hA)
    (by simpa using hB) (by simpa using hC)
  have hs : positiveSupport (centreQuotient Cs t) = 2 →
      nextSaturatedSupportTwo Cs t :=
    next_saturated_of_exponent_one_support_two Cs hS
  have ha : positiveSupport (centreQuotient Ca t) = 2 →
      nextSaturatedSupportTwo Ca t :=
    next_saturated_of_exponent_one_support_two Ca hA
  have hb : positiveSupport (centreQuotient Cb t) = 2 →
      nextSaturatedSupportTwo Cb t :=
    next_saturated_of_exponent_one_support_two Cb hB
  have hc : positiveSupport (centreQuotient Cc t) = 2 →
      nextSaturatedSupportTwo Cc t :=
    next_saturated_of_exponent_one_support_two Cc hC
  rcases hpair with h | h | h | h | h | h
  · exact Or.inl ⟨hs h.1, ha h.2⟩
  · exact Or.inr (Or.inl ⟨hs h.1, hb h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hs h.1, hc h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha h.1, hb h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha h.1, hc h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb h.1, hc h.2⟩))))

#print axioms exponent_one_support_two_exact_mass
#print axioms next_saturated_of_exponent_one_support_two
#print axioms two_saturated_next_among_four_n3

end JSP000404Research
