import JSP000404Research.ZeroGapActualAngle
import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# A support-two zero gap avoids the ray to a sharp centre

At an outer centre i of a four-point configuration, suppose s is a distinct
SharpAt centre.  Every triangle angle at i involving the ray to s is strictly
larger than delta*lambda when delta<1/2.

On the other hand, in the deficit-two/support-two regime, the unique
zero-quotient projective gap is a genuine angle at most delta*lambda.

Therefore the zero gap cannot have the sharp ray as either endpoint.  Since
there are only three rays, once the sorted position of the sharp ray is known,
the zero quotient position is forced to be the opposite gap.
-/

namespace JSP000404Research

open Real

private theorem ray01_ne
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

private theorem ray12_ne
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

private theorem ray02_ne
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

theorem zero_q01_endpoints_ne_sharp
    {p : Fin 4 → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s i : Fin 4}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hq0 : Nat.floor (t * gap01 r0 r1) = 0) :
    r0.1 ≠ s ∧ r1.1 ≠ s := by
  have hsmall :=
    zero_q01_actual_angle_le_delta_lam
      C hcap ht htpos hlam r0 r1 r2 hrays hexp hsupport hq0
  have h01 := ray01_ne C r0 r1 r2 hrays
  constructor
  · intro h0s
    have hs1 : s ≠ r1.1 := by
      intro hs1
      apply h01
      apply Subtype.ext
      calc
        r0.1 = s := h0s
        _ = r1.1 := hs1
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdelta hlampos
        hsi hs1 r1.2.symm hs
    rw [h0s] at hsmall
    linarith
  · intro h1s
    have hs0 : s ≠ r0.1 := by
      intro hs0
      apply h01
      apply Subtype.ext
      calc
        r0.1 = s := hs0.symm
        _ = r1.1 := h1s.symm
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdelta hlampos
        hsi hs0 r0.2.symm hs
    rw [h1s] at hsmall
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p r0.1) ≤
          delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      exact hsmall
    linarith

theorem zero_q12_endpoints_ne_sharp
    {p : Fin 4 → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s i : Fin 4}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hq1 : Nat.floor (t * gap12 r1 r2) = 0) :
    r1.1 ≠ s ∧ r2.1 ≠ s := by
  have hsmall :=
    zero_q12_actual_angle_le_delta_lam
      C hcap ht htpos hlam r0 r1 r2 hrays hexp hsupport hq1
  have h12 := ray12_ne C r0 r1 r2 hrays
  constructor
  · intro h1s
    have hs2 : s ≠ r2.1 := by
      intro hs2
      apply h12
      apply Subtype.ext
      calc
        r1.1 = s := h1s
        _ = r2.1 := hs2
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdelta hlampos
        hsi hs2 r2.2.symm hs
    rw [h1s] at hsmall
    linarith
  · intro h2s
    have hs1 : s ≠ r1.1 := by
      intro hs1
      apply h12
      apply Subtype.ext
      calc
        r1.1 = s := hs1.symm
        _ = r2.1 := h2s.symm
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdelta hlampos
        hsi hs1 r1.2.symm hs
    rw [h2s] at hsmall
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p r1.1) ≤
          delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      exact hsmall
    linarith

theorem zero_q20_endpoints_ne_sharp
    {p : Fin 4 → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s i : Fin 4}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hq2 : Nat.floor (t * gap20 r0 r2) = 0) :
    r0.1 ≠ s ∧ r2.1 ≠ s := by
  have hsmall :=
    zero_q20_actual_angle_le_delta_lam
      C hcap ht htpos hlam r0 r1 r2 hrays hexp hsupport hq2
  have h02 := ray02_ne C r0 r1 r2 hrays
  constructor
  · intro h0s
    have hs2 : s ≠ r2.1 := by
      intro hs2
      apply h02
      apply Subtype.ext
      calc
        r0.1 = s := h0s
        _ = r2.1 := hs2
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdelta hlampos
        hsi hs2 r2.2.symm hs
    rw [h0s] at hsmall
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p r2.1) ≤
          delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      exact hsmall
    linarith
  · intro h2s
    have hs0 : s ≠ r0.1 := by
      intro hs0
      apply h02
      apply Subtype.ext
      calc
        r0.1 = s := hs0.symm
        _ = r2.1 := h2s.symm
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdelta hlampos
        hsi hs0 r0.2.symm hs
    rw [h2s] at hsmall
    linarith

/-- The zero-gap position is exactly opposite the ray to the sharp centre. -/
theorem zero_gap_position_opposite_sharp
    {p : Fin 4 → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s i : Fin 4}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    let q0 := Nat.floor (t * gap01 r0 r1)
    let q1 := Nat.floor (t * gap12 r1 r2)
    let q2 := Nat.floor (t * gap20 r0 r2)
    (q0 = 0 → r2.1 = s) ∧
    (q1 = 0 → r0.1 = s) ∧
    (q2 = 0 → r1.1 = s) := by
  dsimp
  let rs : OtherVertex i := ⟨s, hsi⟩
  have hrsMem : rs ∈ C.rays := C.mem_rays_iff rs
  rw [hrays] at hrsMem
  have hrsCases :
      rs = r0 ∨ rs = r1 ∨ rs = r2 := by
    simpa using hrsMem
  constructor
  · intro hq0
    have hne :=
      zero_q01_endpoints_ne_sharp
        hp hcap hsi hs hdelta hlampos C ht htpos hlam
        r0 r1 r2 hrays hexp hsupport hq0
    rcases hrsCases with h | h | h
    · exact False.elim (hne.1 (by
        have hv := congrArg Subtype.val h
        simpa [rs] using hv))
    · exact False.elim (hne.2 (by
        have hv := congrArg Subtype.val h
        simpa [rs] using hv))
    · have hv := congrArg Subtype.val h
      simpa [rs] using hv.symm
  constructor
  · intro hq1
    have hne :=
      zero_q12_endpoints_ne_sharp
        hp hcap hsi hs hdelta hlampos C ht htpos hlam
        r0 r1 r2 hrays hexp hsupport hq1
    rcases hrsCases with h | h | h
    · have hv := congrArg Subtype.val h
      simpa [rs] using hv.symm
    · exact False.elim (hne.1 (by
        have hv := congrArg Subtype.val h
        simpa [rs] using hv))
    · exact False.elim (hne.2 (by
        have hv := congrArg Subtype.val h
        simpa [rs] using hv))
  · intro hq2
    have hne :=
      zero_q20_endpoints_ne_sharp
        hp hcap hsi hs hdelta hlampos C ht htpos hlam
        r0 r1 r2 hrays hexp hsupport hq2
    rcases hrsCases with h | h | h
    · exact False.elim (hne.1 (by
        have hv := congrArg Subtype.val h
        simpa [rs] using hv))
    · have hv := congrArg Subtype.val h
      simpa [rs] using hv.symm
    · exact False.elim (hne.2 (by
        have hv := congrArg Subtype.val h
        simpa [rs] using hv))

#print axioms zero_q01_endpoints_ne_sharp
#print axioms zero_q12_endpoints_ne_sharp
#print axioms zero_q20_endpoints_ne_sharp
#print axioms zero_gap_position_opposite_sharp

end JSP000404Research
