import JSP000404Research.SixPointSupportThreeShape
import JSP000404Research.SixPointExactWitnessTerminal
import JSP000404Research.FullQuotientZeroAngleMass
import Mathlib.Tactic

/-!
# Three unit-position cases for the six-point support-three exact witness

Let W.b be the exact-witness centre in the six-point terminal and suppose its
n-3 quotient profile has support three.

Pin the unique sharp top ray.  The five cyclic quotient positions have the
form

  qFirst :: qmid ++ [qLast],

where qFirst and qLast are positive and the length-three middle block contains
one positive entry qHidden.  Thus qmid is one of

  [qHidden,0,0], [0,qHidden,0], [0,0,qHidden].

The total quotient mass is n.  Independently, exact-witness geometry forces a
quotient equal to one.  Rotation preserves membership, so the unit quotient is
one of the three positive entries:

  qFirst = 1, qHidden = 1, or qLast = 1.

This is the finite positional terminal for the support-three witness branch.
-/

namespace JSP000404Research

theorem exists_six_point_exactWitness_support_three_unit_position
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    {s : V}
    (hsb : s ≠ W.b)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    ∃ first0 : OtherVertex W.b,
      ∃ rest0 : List (OtherVertex W.b),
      ∃ k : ℕ,
      ∃ r : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
      ∃ qFirst qLast qHidden : ℕ,
      ∃ qmid : List ℕ,
        C.rays = first0 :: rest0 ∧
        C.rays.rotate k =
          (⟨s, hsb⟩ : OtherVertex W.b) :: r :: rest ∧
        (quotientList t C.gaps).rotate k =
          qFirst :: qmid ++ [qLast] ∧
        1 ≤ qFirst ∧
        1 ≤ qLast ∧
        qHidden ≠ 0 ∧
        (qmid = [qHidden,0,0] ∨
         qmid = [0,qHidden,0] ∨
         qmid = [0,0,qHidden]) ∧
        qFirst + qHidden + qLast = n ∧
        (qFirst = 1 ∨ qHidden = 1 ∨ qLast = 1) := by
  obtain ⟨first0, rest0, k, r, rest,
      qFirst, qLast, qHidden, qmid,
      hrays0, hrotRays, hqRot,
      hqFirst, hqLast, _hmidLen,
      hqHidden, hmidShape⟩ :=
    exists_six_point_sharp_pinned_support_three_shape
      hp hcap hcard hn hdelta0 hdeltaHalf ht hlam
      hsb hs C hexp hsupport

  have hdelta1 : delta < 1 := by linarith
  have hsum :
      (quotientList t C.gaps).sum = n :=
    deficit_three_support_three_list_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hsumRot :
      ((quotientList t C.gaps).rotate k).sum = n := by
    rw [(List.rotate_perm (quotientList t C.gaps) k).sum_eq]
    exact hsum
  have hthreeSum :
      qFirst + qHidden + qLast = n := by
    rw [hqRot] at hsumRot
    rcases hmidShape with hshape | hshape | hshape
    · rw [hshape] at hsumRot
      simp at hsumRot
      omega
    · rw [hshape] at hsumRot
      simp at hsumRot
      omega
    · rw [hshape] at hsumRot
      simp at hsumRot
      omega

  have hone :
      1 ∈ quotientList t C.gaps :=
    one_mem_witnessCentre_quotientList
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
  have honeRot :
      1 ∈ (quotientList t C.gaps).rotate k := by
    exact (List.mem_rotate).2 hone
  have hunit :
      qFirst = 1 ∨ qHidden = 1 ∨ qLast = 1 := by
    rw [hqRot] at honeRot
    rcases hmidShape with hshape | hshape | hshape
    · rw [hshape] at honeRot
      simp only [List.mem_cons, List.mem_append,
        List.mem_singleton] at honeRot
      rcases honeRot with hfirst | hmid | hlast
      · exact Or.inl hfirst.symm
      · simp only [List.mem_cons, List.mem_singleton] at hmid
        rcases hmid with hhidden | hzero | hzero
        · exact Or.inr (Or.inl hhidden.symm)
        · omega
        · omega
      · exact Or.inr (Or.inr hlast.symm)
    · rw [hshape] at honeRot
      simp only [List.mem_cons, List.mem_append,
        List.mem_singleton] at honeRot
      rcases honeRot with hfirst | hmid | hlast
      · exact Or.inl hfirst.symm
      · simp only [List.mem_cons, List.mem_singleton] at hmid
        rcases hmid with hzero | hhidden | hzero
        · omega
        · exact Or.inr (Or.inl hhidden.symm)
        · omega
      · exact Or.inr (Or.inr hlast.symm)
    · rw [hshape] at honeRot
      simp only [List.mem_cons, List.mem_append,
        List.mem_singleton] at honeRot
      rcases honeRot with hfirst | hmid | hlast
      · exact Or.inl hfirst.symm
      · simp only [List.mem_cons, List.mem_singleton] at hmid
        rcases hmid with hzero | hzero | hhidden
        · omega
        · omega
        · exact Or.inr (Or.inl hhidden.symm)
      · exact Or.inr (Or.inr hlast.symm)

  exact ⟨first0, rest0, k, r, rest,
    qFirst, qLast, qHidden, qmid,
    hrays0, hrotRays, hqRot,
    hqFirst, hqLast, hqHidden, hmidShape,
    hthreeSum, hunit⟩

#print axioms exists_six_point_exactWitness_support_three_unit_position

end JSP000404Research
