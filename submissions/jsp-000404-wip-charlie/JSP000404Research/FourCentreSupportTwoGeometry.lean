import JSP000404Research.SharpAvoidsZeroGap
import JSP000404Research.TwoSmallAngleContradiction
import Mathlib.Tactic

/-!
# Outer support-two centres create a delta-small angle between the other
non-sharp vertices

Let s,i,j,k be the four distinct vertices of Fin 4.  Assume s is SharpAt and i
has deficit two with quotient support two.

The unique zero quotient gap at i avoids the ray to s.  Since there are only
three rays from i, its endpoints must therefore be exactly j and k.  The
zero-gap actual-angle estimate then gives

  angle(j,i,k) <= delta*lambda.

This removes all dependence on the sorted ray order and is the concrete
geometric statement needed to exclude two support-two outer n-2 centres in the
four-centre terminal.
-/

namespace JSP000404Research

open Real

private theorem local_ray01_ne
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    r0 ≠ r1 := by
  intro h
  have hn := C.nodup
  rw [hrays] at hn
  simp [h] at hn

private theorem local_ray12_ne
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    r1 ≠ r2 := by
  intro h
  have hn := C.nodup
  rw [hrays] at hn
  simp [h] at hn

private theorem local_ray02_ne
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    r0 ≠ r2 := by
  intro h
  have hn := C.nodup
  rw [hrays] at hn
  simp [h] at hn

/-- Four pairwise-distinct elements exhaust Fin 4.  Hence an element distinct
from the first two is one of the remaining two. -/
theorem fin4_eq_third_or_fourth_of_ne_first_two
    {s i j k x : Fin 4}
    (hsi : s ≠ i) (hsj : s ≠ j) (hsk : s ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hxi : x ≠ i) (hxs : x ≠ s) :
    x = j ∨ x = k := by
  have hsi' : s.val ≠ i.val := by
    intro h
    exact hsi (Fin.ext h)
  have hsj' : s.val ≠ j.val := by
    intro h
    exact hsj (Fin.ext h)
  have hsk' : s.val ≠ k.val := by
    intro h
    exact hsk (Fin.ext h)
  have hij' : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  have hik' : i.val ≠ k.val := by
    intro h
    exact hik (Fin.ext h)
  have hjk' : j.val ≠ k.val := by
    intro h
    exact hjk (Fin.ext h)
  have hxi' : x.val ≠ i.val := by
    intro h
    exact hxi (Fin.ext h)
  have hxs' : x.val ≠ s.val := by
    intro h
    exact hxs (Fin.ext h)
  have hv : x.val = j.val ∨ x.val = k.val := by
    have hslt := s.isLt
    have hilt := i.isLt
    have hjlt := j.isLt
    have hklt := k.isLt
    have hxlt := x.isLt
    omega
  rcases hv with hv | hv
  · exact Or.inl (Fin.ext hv)
  · exact Or.inr (Fin.ext hv)

/-- Order-free four-point support-two outer-angle theorem. -/
theorem support_two_outer_angle_le_delta_lam
    {p : Fin 4 → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s i j k : Fin 4}
    (hsi : s ≠ i) (hsj : s ≠ j) (hsk : s ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hs : SharpAt p delta lam s)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    EuclideanGeometry.angle (p j) (p i) (p k) ≤
      delta * lam := by
  obtain ⟨r0, r1, r2, hrays⟩ :=
    exists_three_rays_of_fin4_cycle i C
  let q0 := Nat.floor (t * gap01 r0 r1)
  let q1 := Nat.floor (t * gap12 r1 r2)
  let q2 := Nat.floor (t * gap20 r0 r2)
  have hzero :=
    deficit_two_support_two_exactly_one_zero_gap
      C r0 r1 r2 hrays hsupport
  dsimp [q0, q1, q2] at hzero
  rcases hzero with h0 | h1 | h2
  · have hsmall :=
      zero_q01_actual_angle_le_delta_lam
        C hcap ht htpos hlam r0 r1 r2 hrays
        hexp hsupport h0.1
    have hav :=
      zero_q01_endpoints_ne_sharp
        hp hcap hsi hs hdelta hlampos C
        ht htpos hlam r0 r1 r2 hrays
        hexp hsupport h0.1
    have h01 : r0.1 ≠ r1.1 := by
      intro h
      apply local_ray01_ne C r0 r1 r2 hrays
      exact Subtype.ext h
    have hr0 :=
      fin4_eq_third_or_fourth_of_ne_first_two
        hsi hsj hsk hij hik hjk r0.2 hav.1
    have hr1 :=
      fin4_eq_third_or_fourth_of_ne_first_two
        hsi hsj hsk hij hik hjk r1.2 hav.2
    rcases hr0 with hr0 | hr0 <;> rcases hr1 with hr1 | hr1
    · exact False.elim (h01 (by simpa [hr0, hr1]))
    · simpa [hr0, hr1] using hsmall
    · have hsmall' :
          EuclideanGeometry.angle (p j) (p i) (p k) ≤
            delta * lam := by
        rw [EuclideanGeometry.angle_comm]
        simpa [hr0, hr1] using hsmall
      exact hsmall'
    · exact False.elim (h01 (by simpa [hr0, hr1]))
  · have hsmall :=
      zero_q12_actual_angle_le_delta_lam
        C hcap ht htpos hlam r0 r1 r2 hrays
        hexp hsupport h1.2.1
    have hav :=
      zero_q12_endpoints_ne_sharp
        hp hcap hsi hs hdelta hlampos C
        ht htpos hlam r0 r1 r2 hrays
        hexp hsupport h1.2.1
    have h12 : r1.1 ≠ r2.1 := by
      intro h
      apply local_ray12_ne C r0 r1 r2 hrays
      exact Subtype.ext h
    have hr1 :=
      fin4_eq_third_or_fourth_of_ne_first_two
        hsi hsj hsk hij hik hjk r1.2 hav.1
    have hr2 :=
      fin4_eq_third_or_fourth_of_ne_first_two
        hsi hsj hsk hij hik hjk r2.2 hav.2
    rcases hr1 with hr1 | hr1 <;> rcases hr2 with hr2 | hr2
    · exact False.elim (h12 (by simpa [hr1, hr2]))
    · simpa [hr1, hr2] using hsmall
    · have hsmall' :
          EuclideanGeometry.angle (p j) (p i) (p k) ≤
            delta * lam := by
        rw [EuclideanGeometry.angle_comm]
        simpa [hr1, hr2] using hsmall
      exact hsmall'
    · exact False.elim (h12 (by simpa [hr1, hr2]))
  · have hsmall :=
      zero_q20_actual_angle_le_delta_lam
        C hcap ht htpos hlam r0 r1 r2 hrays
        hexp hsupport h2.2.2
    have hav :=
      zero_q20_endpoints_ne_sharp
        hp hcap hsi hs hdelta hlampos C
        ht htpos hlam r0 r1 r2 hrays
        hexp hsupport h2.2.2
    have h02 : r0.1 ≠ r2.1 := by
      intro h
      apply local_ray02_ne C r0 r1 r2 hrays
      exact Subtype.ext h
    have hr0 :=
      fin4_eq_third_or_fourth_of_ne_first_two
        hsi hsj hsk hij hik hjk r0.2 hav.1
    have hr2 :=
      fin4_eq_third_or_fourth_of_ne_first_two
        hsi hsj hsk hij hik hjk r2.2 hav.2
    rcases hr0 with hr0 | hr0 <;> rcases hr2 with hr2 | hr2
    · exact False.elim (h02 (by simpa [hr0, hr2]))
    · have hsmall' :
          EuclideanGeometry.angle (p j) (p i) (p k) ≤
            delta * lam := by
        -- wrap theorem is ordered as angle(r2,i,r0)
        simpa [hr0, hr2] using hsmall
      exact hsmall'
    · have hsmall' :
          EuclideanGeometry.angle (p j) (p i) (p k) ≤
            delta * lam := by
        rw [EuclideanGeometry.angle_comm]
        simpa [hr0, hr2] using hsmall
      exact hsmall'
    · exact False.elim (h02 (by simpa [hr0, hr2]))

/-- Two distinct outer deficit-two/support-two centres cannot coexist around
one sharp centre in a four-point lower-branch configuration. -/
theorem no_two_support_two_outer_centres_around_sharp
    {p : Fin 4 → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : SharpAt p delta lam s)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    {t : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hexpA : centreExponent Ca t = n - 2)
    (hexpB : centreExponent Cb t = n - 2)
    (hsuppA : positiveSupport (centreQuotient Ca t) = 2)
    (hsuppB : positiveSupport (centreQuotient Cb t) = 2) :
    False := by
  have ha :=
    support_two_outer_angle_le_delta_lam
      hp hcap hsa hsb hsc hab hac hbc
      hs hdelta hlampos Ca ht htpos hlam
      hexpA hsuppA
  have hb :=
    support_two_outer_angle_le_delta_lam
      hp hcap hsb hsa hsc hab.symm hbc hac
      hs hdelta hlampos Cb ht htpos hlam
      hexpB hsuppB
  exact impossible_two_delta_small_angles_under_cap
    hp hcap hdelta hlampos
    hab hac hbc ha hb

#print axioms fin4_eq_third_or_fourth_of_ne_first_two
#print axioms support_two_outer_angle_le_delta_lam
#print axioms no_two_support_two_outer_centres_around_sharp

end JSP000404Research
