import JSP000404Research.CanonicalSignAcyclicity
import Mathlib.Tactic

/-!
# The canonical Boolean ray sign is a strict planar order

The canonical projective sign is not merely triangle-acyclic.  With the
fixed half-open projective chart, sign=true means that the displacement lies
in the lexicographically positive half-plane

  y > 0  or  (y = 0 and x > 0).

Hence it induces the strict lexicographic order of the embedded planar
points.  This module records the order facts explicitly, so later finite
six-point arguments can use transitivity instead of repeatedly reopening the
polar representation.
-/

namespace JSP000404Research

def CanonicalPointLt
    {V : Type*} (p : V → Plane) (a b : V) : Prop :=
  PlaneHalfPositive (p b - p a)

theorem planeHalfPositive_or_neg_of_ne_zero
    {x : Plane}
    (hx : x ≠ 0) :
    PlaneHalfPositive x ∨ PlaneHalfPositive (-x) := by
  by_cases hy : x 1 = 0
  · have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      ext k
      fin_cases k
      · simpa using hx0
      · simpa using hy
    rcases lt_or_gt_of_ne hx0.symm with hxneg | hxpos
    · right
      right
      constructor
      · change -(x 1) = 0
        rw [hy]
        simp
      · change 0 < -(x 0)
        linarith
    · left
      exact Or.inr ⟨hy, hxpos⟩
  · by_cases hypos : 0 < x 1
    · exact Or.inl (Or.inl hypos)
    · right
      left
      change 0 < -(x 1)
      have hyle : x 1 ≤ 0 := le_of_not_gt hypos
      have hylt : x 1 < 0 := lt_of_le_of_ne hyle hy
      linarith

theorem canonicalPointLt_irrefl
    {V : Type*} {p : V → Plane} (a : V) :
    ¬ CanonicalPointLt p a a := by
  intro h
  have hz : p a - p a = 0 := sub_self _
  unfold CanonicalPointLt at h
  rw [hz] at h
  exact planeHalfPositive_ne_zero h rfl

theorem canonicalPointLt_trans
    {V : Type*} {p : V → Plane}
    {a b c : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c) :
    CanonicalPointLt p a c := by
  unfold CanonicalPointLt at *
  have hsum :=
    planeHalfPositive_add hab hbc
  have heq :
      (p b - p a) + (p c - p b) = p c - p a := by
    abel
  rwa [heq] at hsum

theorem canonicalPointLt_asymm
    {V : Type*} {p : V → Plane}
    {a b : V}
    (hab : CanonicalPointLt p a b) :
    ¬ CanonicalPointLt p b a := by
  intro hba
  unfold CanonicalPointLt at hab hba
  have hneg :
      p a - p b = -(p b - p a) := by
    abel
  rw [hneg] at hba
  exact planeHalfPositive_not_neg hab hba

theorem canonicalPointLt_total_of_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b : V}
    (hab : a ≠ b) :
    CanonicalPointLt p a b ∨ CanonicalPointLt p b a := by
  have hdisp : p b - p a ≠ 0 := by
    intro h
    have heq : p b = p a := sub_eq_zero.mp h
    exact hab (hp heq).symm
  rcases planeHalfPositive_or_neg_of_ne_zero hdisp with hpos | hneg
  · exact Or.inl hpos
  · right
    unfold CanonicalPointLt
    have heq :
        p a - p b = -(p b - p a) := by
      abel
    rwa [heq]

theorem raySign_true_iff_canonicalPointLt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V}
    (hij : i ≠ j) :
    raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) = true
      ↔
    CanonicalPointLt p i j := by
  constructor
  · intro h
    exact displacement_halfPositive_of_raySign_true hp hij h
  · intro hpos
    by_cases hs :
        raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) = true
    · exact hs
    · have hsfalse :
          raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) = false := by
        cases h :
            raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) <;>
          simp_all
      have hrev :
          raySignAt hp j (⟨i, hij⟩ : OtherVertex j) =
            !raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) :=
        raySignAt_reverse_eq_not hp hij
      have hrevTrue :
          raySignAt hp j (⟨i, hij⟩ : OtherVertex j) = true := by
        rw [hrev, hsfalse]
        rfl
      have hback :
          PlaneHalfPositive (p i - p j) :=
        displacement_halfPositive_of_raySign_true
          hp hij.symm hrevTrue
      have hneg :
          p i - p j = -(p j - p i) := by
        abel
      rw [hneg] at hback
      exact False.elim
        (planeHalfPositive_not_neg hpos hback)

theorem raySign_true_trans
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b c : V}
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hAB :
      raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) = true)
    (hBC :
      raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b) = true) :
    raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a) = true := by
  rw [raySign_true_iff_canonicalPointLt hp hab] at hAB
  rw [raySign_true_iff_canonicalPointLt hp hbc] at hBC
  rw [raySign_true_iff_canonicalPointLt hp hac]
  exact canonicalPointLt_trans hAB hBC

/-- Every pair of distinct embedded points has exactly one true canonical
orientation. -/
theorem exactly_one_raySign_true
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b : V}
    (hab : a ≠ b) :
    (raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) = true)
      ↔
    (raySignAt hp b (⟨a, hab⟩ : OtherVertex b) = false) := by
  rw [raySignAt_reverse_eq_not hp hab]
  cases h :
      raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) <;>
    simp

#print axioms planeHalfPositive_or_neg_of_ne_zero
#print axioms canonicalPointLt_trans
#print axioms canonicalPointLt_total_of_ne
#print axioms raySign_true_iff_canonicalPointLt
#print axioms raySign_true_trans

end JSP000404Research
