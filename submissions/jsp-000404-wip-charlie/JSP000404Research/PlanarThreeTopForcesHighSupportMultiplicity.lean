import JSP000404Research.PlanarWeightedLowSupportPacking
import JSP000404Research.PlanarThreeCrowdedTopTinyGap
import Mathlib.Tactic

/-!
# Actual n=3 TOP costs two global transition packing units

At an original exponent-two centre the true quotient support is one,
and its strict-support transition quotient is exactly three. The
weighted low-support packing bound conservatively counts just TWO
units for that centre. Therefore all original low-support centres
consume at least their cardinality plus one out of the total six
strict-support units. The complement contains all high-support
centres, each necessarily exponent zero.

This yields the quantitative genuine AngleCap constraint
  card(original high-support centres) + 5 >= card(original centres)
whenever at least one real exponent-two centre exists.

In particular seven original centres with an exponent-two centre
have at least TWO distinct support-three centres (and eight
original centres require at least THREE). These structural constraints
do NOT eliminate the remaining top-exponent configurations and
cannot be counted as exterior Boolean-hole credit.
-/

namespace JSP000404Research
open scoped BigOperators

theorem planar_three_top_forces_many_high_support_centres
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
    (htop : ∃ i : V, centreExponent (C i) t = 2) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card + 5 := by
  classical
  let I : Type _ :=
    {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
  let E : Finset I :=
    Finset.univ.filter (fun r =>
      positiveSupport (centreQuotient (C r) t) = 1 ∧
      1 ≤ centreExponent (C r) t)
  let L : Finset V :=
    Finset.univ.filter (fun i =>
      positiveSupport (centreQuotient (C i) t) ≤ 2)
  let H : Finset V :=
    Finset.univ.filter (fun i =>
      3 ≤ positiveSupport (centreQuotient (C i) t))
  obtain ⟨i, hi⟩ := htop
  have hisupp : positiveSupport (centreQuotient (C i) t) = 1 :=
    (planar_three_top_centre_has_exact_unit_support
      (C i) hdelta0 hdeltaHalf ht hi).1
  let z : I := ⟨i, by omega⟩
  have hz : z ∈ E := by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hisupp, by simpa [z] using
      (show 1 ≤ centreExponent (C i) t by omega)⟩
  have hE : 1 ≤ E.card :=
    Finset.one_le_card.mpr ⟨z, hz⟩
  have hbudget : Fintype.card I + E.card ≤ 6 := by
    have hh := planar_weighted_low_support_subfamily_card_le_two_n
      hp hcap (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdeltaHalf ht hlam C
    simpa [I, E] using hh
  have hLow : Fintype.card I = L.card := by
    simp [I, L, Fintype.card_subtype]
  have hcomp : H = (Finset.univ : Finset V) \ L := by
    ext i
    simp only [H, L, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff]
    omega
  have hpart : H.card + L.card = Fintype.card V := by
    have hc := Finset.card_sdiff_add_card_inter
      (Finset.univ : Finset V) L
    rw [← hcomp] at hc
    simpa using hc
  change Fintype.card V ≤ H.card + 5
  omega

/-- Seven-point actual n=3 geometry with a top exponent-two centre
necessarily exhibits TWO distinct high-support (therefore exponent-zero)
centres. This is an unconditional geometric consequence of AngleCap
in the displayed top-centre subcase, not a proof that this subcase
is impossible. -/
theorem planar_three_seven_top_forces_two_high_support_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hseven : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (htop : ∃ i : V, centreExponent (C i) t = 2) :
    2 ≤ ((Finset.univ : Finset V).filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card := by
  have h := planar_three_top_forces_many_high_support_centres
    hp hcap hdelta0 hdeltaHalf ht hlam C htop
  omega

#print axioms planar_three_top_forces_many_high_support_centres
#print axioms planar_three_seven_top_forces_two_high_support_centres

end JSP000404Research
