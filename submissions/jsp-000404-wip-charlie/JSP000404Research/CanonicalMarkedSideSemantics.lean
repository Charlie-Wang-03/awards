import JSP000404Research.CanonicalSignOrder
import Mathlib.Tactic

/-!
# Canonical sign side semantics

For a fixed centre i, the canonical ray sign records whether the other point
lies above i in the strict canonical planar order.  This file packages equal
and opposite sign relations for two marked endpoints as same-side / cross-side
order statements.
-/

namespace JSP000404Research

def CanonicalSameSide
    {V : Type*}
    (p : V → Plane) (i a b : V) : Prop :=
  (CanonicalPointLt p i a ∧ CanonicalPointLt p i b) ∨
  (CanonicalPointLt p a i ∧ CanonicalPointLt p b i)

def CanonicalOppositeSides
    {V : Type*}
    (p : V → Plane) (i a b : V) : Prop :=
  (CanonicalPointLt p a i ∧ CanonicalPointLt p i b) ∨
  (CanonicalPointLt p b i ∧ CanonicalPointLt p i a)

theorem raySign_eq_iff_canonicalSameSide
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i a b : V}
    (hia : i ≠ a)
    (hib : i ≠ b) :
    raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i) =
        raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i)
      ↔
    CanonicalSameSide p i a b := by
  let sa :=
    raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i)
  let sb :=
    raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i)
  constructor
  · intro heq
    cases hsa : sa <;> cases hsb : sb <;> simp_all [sa,sb]
    · right
      have hnotA :
          ¬ CanonicalPointLt p i a := by
        intro h
        have ht :=
          (raySign_true_iff_canonicalPointLt hp hia).2 h
        simpa [sa,hsa] using ht
      have hnotB :
          ¬ CanonicalPointLt p i b := by
        intro h
        have ht :=
          (raySign_true_iff_canonicalPointLt hp hib).2 h
        simpa [sb,hsb] using ht
      have htotA :=
        canonicalPointLt_total_of_ne hp hia
      have htotB :=
        canonicalPointLt_total_of_ne hp hib
      exact ⟨htotA.resolve_left hnotA,
        htotB.resolve_left hnotB⟩
    · left
      constructor
      · exact (raySign_true_iff_canonicalPointLt hp hia).1
          (by simpa [sa,hsa])
      · exact (raySign_true_iff_canonicalPointLt hp hib).1
          (by simpa [sb,hsb])
  · intro hside
    rcases hside with hupper | hlower
    · have ha :=
        (raySign_true_iff_canonicalPointLt hp hia).2 hupper.1
      have hb :=
        (raySign_true_iff_canonicalPointLt hp hib).2 hupper.2
      rw [ha,hb]
    · have haNot :
          raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i) ≠ true := by
        intro ha
        have hai :=
          (raySign_true_iff_canonicalPointLt hp hia).1 ha
        exact canonicalPointLt_asymm hlower.1 hai
      have hbNot :
          raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i) ≠ true := by
        intro hb
        have hbi :=
          (raySign_true_iff_canonicalPointLt hp hib).1 hb
        exact canonicalPointLt_asymm hlower.2 hbi
      cases ha :
          raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i) <;>
        cases hb :
          raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i) <;>
        simp_all

theorem raySign_ne_iff_canonicalOppositeSides
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i a b : V}
    (hia : i ≠ a)
    (hib : i ≠ b) :
    raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i) ≠
        raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i)
      ↔
    CanonicalOppositeSides p i a b := by
  constructor
  · intro hne
    let sa :=
      raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i)
    let sb :=
      raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i)
    cases hsa : sa <;> cases hsb : sb <;> simp_all [sa,sb]
    · right
      have hbi :
          CanonicalPointLt p b i := by
        have htot := canonicalPointLt_total_of_ne hp hib
        apply htot.resolve_left
        intro hib'
        have ht :=
          (raySign_true_iff_canonicalPointLt hp hib).2 hib'
        simpa [sb,hsb] using ht
      have hia' :
          CanonicalPointLt p i a :=
        (raySign_true_iff_canonicalPointLt hp hia).1
          (by simpa [sa,hsa])
      exact ⟨hbi,hia'⟩
    · left
      have hai :
          CanonicalPointLt p a i := by
        have htot := canonicalPointLt_total_of_ne hp hia
        apply htot.resolve_left
        intro hia'
        have ht :=
          (raySign_true_iff_canonicalPointLt hp hia).2 hia'
        simpa [sa,hsa] using ht
      have hib' :
          CanonicalPointLt p i b :=
        (raySign_true_iff_canonicalPointLt hp hib).1
          (by simpa [sb,hsb])
      exact ⟨hai,hib'⟩
  · intro hop
    intro heq
    have hsame :=
      (raySign_eq_iff_canonicalSameSide hp hia hib).1 heq
    rcases hop with ⟨hai,hib⟩ | ⟨hbi,hia⟩ <;>
      rcases hsame with ⟨hia',hib'⟩ | ⟨hai',hbi'⟩
    · exact canonicalPointLt_asymm hai hia'
    · exact canonicalPointLt_asymm hib hbi'
    · exact canonicalPointLt_asymm hbi hib'
    · exact canonicalPointLt_asymm hia hai'

theorem raySign_not_eq_iff_canonicalOppositeSides
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i a b : V}
    (hia : i ≠ a)
    (hib : i ≠ b) :
    raySignAt hp i (⟨a,hia.symm⟩ : OtherVertex i) =
        !raySignAt hp i (⟨b,hib.symm⟩ : OtherVertex i)
      ↔
    CanonicalOppositeSides p i a b := by
  have hbool :
      ∀ x y : Bool, x = !y ↔ x ≠ y := by
    intro x y
    cases x <;> cases y <;> simp
  rw [hbool]
  exact raySign_ne_iff_canonicalOppositeSides hp hia hib

#print axioms raySign_eq_iff_canonicalSameSide
#print axioms raySign_ne_iff_canonicalOppositeSides
#print axioms raySign_not_eq_iff_canonicalOppositeSides

end JSP000404Research
