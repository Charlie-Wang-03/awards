import JSP000404Research.PlanarThreeSharpOverweightClassification
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Genuine original AngleCap overcrowding reduces to EXACTLY nine points

The n=3 missing large-cardinality geometric exclusion is already
substantive at nine points. This module reduces exclusion of ALL
finite original planar AngleCap point sets of cardinality >=9 to
one precise finite nine-point angle-cap obstruction.

The nine-point obstruction itself is NOT supplied and is NOT assumed
inside any purported proof of JSP-000404. Instead it is a clearly
named external premise to a separate conditional theorem, so future
proof attempts may focus on the exact first missing cardinality.
No artificial dyadic credit, fabricated Boolean hole or new axiom.
-/

namespace JSP000404Research

/-- A genuine injective nine-point subset of every finite LINEAR-ORDERED
original vertex set of at least nine elements. -/
noncomputable def original_nine_point_order_embedding
    {V : Type*} [LinearOrder V] [Fintype V]
    (hcard : 9 ≤ Fintype.card V) : Fin 9 ↪o V := by
  classical
  let hex :
      ∃ S : Finset V, S ⊆ (Finset.univ : Finset V) ∧ S.card = 9 :=
    (Finset.univ : Finset V).exists_subset_card_eq
      (by simpa using hcard : 9 ≤ (Finset.univ : Finset V).card)
  let S : Finset V := Classical.choose hex
  have hS : S.card = 9 := (Classical.choose_spec hex).2
  exact S.orderEmbOfFin hS

/-- Transport of ACTUAL AngleCap geometry to any injectively chosen
nine ORIGINAL vertices. Angles and vertex coordinates are unchanged. -/
theorem original_nine_subconfiguration_preserves_angle_cap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hcard : 9 ≤ Fintype.card V) :
    AngleCap
      (fun j : Fin 9 => p (original_nine_point_order_embedding hcard j))
      lam := by
  let e := original_nine_point_order_embedding hcard
  intro a b c hab hac hbc
  apply hcap (e a) (e b) (e c)
  · exact e.injective.ne hab
  · exact e.injective.ne hac
  · exact e.injective.ne hbc

/-- EXACT finite-cardinality reduction: any independent genuine
nine-point obstruction at fixed λ excludes ALL original larger
AngleCap configurations. No n-specific numeric assumption is needed. -/
theorem nine_point_angle_cap_obstruction_implies_global_card_le_eight
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hNine : ∀ (q : Fin 9 → Plane),
      Function.Injective q → ¬ AngleCap q lam) :
    Fintype.card V ≤ 8 := by
  by_contra h
  have hcard : 9 ≤ Fintype.card V := by omega
  let e := original_nine_point_order_embedding hcard
  have hqinj : Function.Injective (fun j : Fin 9 => p (e j)) :=
    hp.comp e.injective
  have hqcap : AngleCap (fun j : Fin 9 => p (e j)) lam :=
    original_nine_subconfiguration_preserves_angle_cap hp hcap hcard
  exact (hNine (fun j : Fin 9 => p (e j)) hqinj) hqcap

#print axioms original_nine_subconfiguration_preserves_angle_cap
#print axioms nine_point_angle_cap_obstruction_implies_global_card_le_eight

end JSP000404Research
