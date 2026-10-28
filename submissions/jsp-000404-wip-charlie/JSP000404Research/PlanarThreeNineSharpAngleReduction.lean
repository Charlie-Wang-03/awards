import JSP000404Research.PlanarNineCentreGeometryReduction
import Mathlib.Tactic

/-!
# A sharp fixed-nine geometric gate for original n=3 planar capacity

The classical maximal-angle extremal problem suggests the threshold 5*pi/7
for nine distinct planar points. This file DOES NOT formalize that deep
geometric result and deliberately does not declare it as an axiom.

Instead, it states that theorem as an explicit, unproved external
HYPOTHESIS of conditional reductions. If and only if its actual geometric
proof is eventually imported, the resulting real-arithmetic conversion
will eliminate the entire >=9 original-centre obstruction in the
strict n=3, 0<=delta<1/2 strip.

The remaining 7/8-centre exponent-one and exponent-two obstructions
are NOT removed by this finite-nine statement, and the global
eight-source nonreuse debt remains unproved.
-/

namespace JSP000404Research
open scoped BigOperators

/-- An explicitly named finite-NINE-point angle theorem to be proved in
Lean from plane geometry in a future step. Defining a Prop is NOT
an axiom or a proof of the proposition. -/
def NinePointFiveSeventhsAngleLowerBound : Prop :=
  ∀ q : Fin 9 → Plane, Function.Injective q →
    ∃ a b c : Fin 9,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        5 * Real.pi / 7 ≤
          EuclideanGeometry.angle (q a) (q b) (q c)

/-- The exact arithmetic obstruction: no angle can be simultaneously
at least 5*pi/7 and at most pi-pi/t when 0<t<7/2. -/
theorem five_sevenths_angle_incompatible_with_small_scale_cap
    {t theta : ℝ}
    (htpos : 0 < t)
    (htlt : t < (7 : ℝ) / 2)
    (hlarge : 5 * Real.pi / 7 ≤ theta)
    (hupper : theta ≤ Real.pi - Real.pi / t) :
    False := by
  have hdiv : (Real.pi / t) * t = Real.pi := by
    field_simp [ne_of_gt htpos]
  have hlargeMul :=
    mul_le_mul_of_nonneg_right hlarge htpos.le
  have hupperMul :=
    mul_le_mul_of_nonneg_right hupper htpos.le
  have hmargin : 0 < Real.pi * (7 - 2 * t) := by
    apply mul_pos Real.pi_pos
    linarith
  nlinarith [hdiv, hlargeMul, hupperMul, hmargin]

/-- An honest conditional implication: the named NINE-point geometric
threshold excludes every fixed-nine AngleCap arrangement throughout
the original strict n=3 half-strip. -/
theorem nine_point_sharp_angle_implies_three_strip_angle_obstruction
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hNine : NinePointFiveSeventhsAngleLowerBound) :
    ∀ (q : Fin 9 → Plane), Function.Injective q → ¬ AngleCap q lam := by
  intro q hq hcap
  obtain ⟨a, b, c, hab, hac, hbc, hlarge⟩ := hNine q hq
  have hupper :
      EuclideanGeometry.angle (q a) (q b) (q c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a b c hab hac hbc)
  have htpos : 0 < t := by rw [ht]; linarith
  have htlt : t < (7 : ℝ) / 2 := by rw [ht]; linarith
  exact five_sevenths_angle_incompatible_with_small_scale_cap
    htpos htlt hlarge hupper

/-- Formal reduction of ALL original >=9 planar configurations to one
explicit external nine-point geometric lemma, with no stronger
hypothesis on the original point set or manufactured dyadic credit. -/
theorem planar_three_original_card_le_eight_of_sharp_nine_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hNine : NinePointFiveSeventhsAngleLowerBound) :
    Fintype.card V ≤ 8 := by
  apply nine_point_angle_cap_obstruction_implies_global_card_le_eight hp hcap
  exact nine_point_sharp_angle_implies_three_strip_angle_obstruction
    hdelta0 hdeltaHalf ht hlam hNine

/-- Consequently, under that one STILL UNPROVED external nine-point
geometric fact, an original n=3 dyadic counterexample with >=7
centres must have exactly seven or eight original centres, with
exactly the forbidden real exponent profile stated below. -/
theorem planar_three_overweight_iff_seven_eight_profile_of_sharp_nine_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hseven : 7 ≤ Fintype.card V)
    (hNine : NinePointFiveSeventhsAngleLowerBound) :
    (8 < (∑ i : V, 2 ^ centreExponent (C i) t)) ↔
      ((Fintype.card V = 8 ∧
          (0 < ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card ∨
           0 < ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card)) ∨
       (Fintype.card V = 7 ∧
          (2 ≤ ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card ∨
           1 ≤ ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card))) := by
  have hcard8 : Fintype.card V ≤ 8 :=
    planar_three_original_card_le_eight_of_sharp_nine_angle
      hp hcap hdelta0 hdeltaHalf ht hlam hNine
  rw [planar_three_large_overweight_iff_obstruction_profile
    hp hdelta0 hdeltaHalf ht C hseven]
  omega

#print axioms five_sevenths_angle_incompatible_with_small_scale_cap
#print axioms nine_point_sharp_angle_implies_three_strip_angle_obstruction
#print axioms planar_three_original_card_le_eight_of_sharp_nine_angle
#print axioms planar_three_overweight_iff_seven_eight_profile_of_sharp_nine_angle

end JSP000404Research
