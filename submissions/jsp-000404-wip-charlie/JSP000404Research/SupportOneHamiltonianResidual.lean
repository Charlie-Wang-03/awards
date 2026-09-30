import JSP000404Research.DeficitThreeSupportOneGeometry
import JSP000404Research.MixedSupportThreeSmallMatchings
import Mathlib.Tactic

/-!
# Support-one amplification inside the Hamiltonian residual

Let a be an exact deficit-three/support-one centre.  Every angle at a is at
most (2+delta)*lambda.

If a participates in a delta*lambda-small angle at another vertex v, then the
third angle of that triangle is at least

  (n-2-delta)*lambda.

The Hamiltonian residual has two small matching edges at each of b and c.
Since the support-one minimum a is one of the three residual vertices x,y,z,
two of those small edges therefore generate two explicit large outer angles.

This is stronger information than the bare small-matching residual and is
kept as a separate theorem for the next geometric reduction.
-/

namespace JSP000404Research

open Real

theorem support_one_and_small_angle_force_large_third
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a v u : V}
    (hav : a ≠ v)
    (hau : a ≠ u)
    (hvu : v ≠ u)
    (Ca : CentreProjectiveCycle hp a)
    (hA : centreExponent Ca t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsmall :
      EuclideanGeometry.angle (p a) (p v) (p u)
        ≤ delta * lam) :
    (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
      EuclideanGeometry.angle (p v) (p u) (p a) := by
  have hAang :
      EuclideanGeometry.angle (p v) (p a) (p u) ≤
        (2 + delta) * lam :=
    deficit_three_support_one_all_angles_le
      hp hcap hn hdelta0 ht hlam
      Ca hA hsupA
      v u hav.symm hau.symm hvu

  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p a) (p₂ := p v) (p u)
      (hp.ne hav)
  have hcommA :
      EuclideanGeometry.angle (p u) (p a) (p v) =
        EuclideanGeometry.angle (p v) (p a) (p u) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommA] at hsum

  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [hpi, ht, hncast] at hsum ⊢
  nlinarith

/-- A support-one residual vertex produces two large third angles. -/
theorem hamiltonian_residual_support_one_amplification
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a b c x y z : V}
    (haTop : a ≠ top)
    (haB : a ≠ b)
    (haC : a ≠ c)
    (hbTop : b ≠ top)
    (hcTop : c ≠ top)
    (hbc : b ≠ c)
    (hxTop : x ≠ top) (hyTop : y ≠ top) (hzTop : z ≠ top)
    (hxB : x ≠ b) (hyB : y ≠ b) (hzB : z ≠ b)
    (hxC : x ≠ c) (hyC : y ≠ c) (hzC : z ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (Ca : CentreProjectiveCycle hp a)
    (hA : centreExponent Ca t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsmallB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hsmallC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam) :
    (
      a = x ∧
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p x) ∧
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p c) (p z) (p x)
    )
    ∨
    (
      a = y ∧
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p y) ∧
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p b) (p z) (p y)
    )
    ∨
    (
      a = z ∧
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p b) (p y) (p z) ∧
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p c) (p x) (p z)
    ) := by
  have haCase :
      a = x ∨ a = y ∨ a = z :=
    SmallPerfectMatchingAwayFromTop.three_remaining_vertices_exhaust
      hcard hbTop.symm hcTop.symm hbc
      hxTop hyTop hzTop
      hxB hyB hzB
      hxC hyC hzC
      hxy hxz hyz
      haTop haB haC

  have hB1nonneg :
      0 ≤ EuclideanGeometry.angle (p y) (p b) (p z) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hB2nonneg :
      0 ≤ EuclideanGeometry.angle (p c) (p b) (p x) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hC1nonneg :
      0 ≤ EuclideanGeometry.angle (p x) (p c) (p z) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hC2nonneg :
      0 ≤ EuclideanGeometry.angle (p b) (p c) (p y) :=
    EuclideanGeometry.angle_nonneg _ _ _

  rcases haCase with hax | hay | haz
  · left
    subst a
    have hsmallBX :
        EuclideanGeometry.angle (p x) (p b) (p c)
          ≤ delta * lam := by
      have h :
          EuclideanGeometry.angle (p c) (p b) (p x)
            ≤ delta * lam := by
        linarith
      simpa [EuclideanGeometry.angle_comm] using h
    have hsmallCXZ :
        EuclideanGeometry.angle (p x) (p c) (p z)
          ≤ delta * lam := by
      linarith
    have hlargeC :=
      support_one_and_small_angle_force_large_third
        hp hcap hn hdelta0 ht hlam
        hxB hxC hbc
        Ca hA hsupA hsmallBX
    have hlargeZ :=
      support_one_and_small_angle_force_large_third
        hp hcap hn hdelta0 ht hlam
        hxC hxz hzC.symm
        Ca hA hsupA hsmallCXZ
    exact ⟨rfl, hlargeC, hlargeZ⟩

  · right; left
    subst a
    have hsmallCY :
        EuclideanGeometry.angle (p y) (p c) (p b)
          ≤ delta * lam := by
      have h :
          EuclideanGeometry.angle (p b) (p c) (p y)
            ≤ delta * lam := by
        linarith
      simpa [EuclideanGeometry.angle_comm] using h
    have hsmallBYZ :
        EuclideanGeometry.angle (p y) (p b) (p z)
          ≤ delta * lam := by
      linarith
    have hlargeB :=
      support_one_and_small_angle_force_large_third
        hp hcap hn hdelta0 ht hlam
        hyC hyB hbc.symm
        Ca hA hsupA hsmallCY
    have hlargeZ :=
      support_one_and_small_angle_force_large_third
        hp hcap hn hdelta0 ht hlam
        hyB hyz hzB.symm
        Ca hA hsupA hsmallBYZ
    exact ⟨rfl, hlargeB, hlargeZ⟩

  · right; right
    subst a
    have hsmallBZY :
        EuclideanGeometry.angle (p z) (p b) (p y)
          ≤ delta * lam := by
      have h :
          EuclideanGeometry.angle (p y) (p b) (p z)
            ≤ delta * lam := by
        linarith
      simpa [EuclideanGeometry.angle_comm] using h
    have hsmallCZX :
        EuclideanGeometry.angle (p z) (p c) (p x)
          ≤ delta * lam := by
      have h :
          EuclideanGeometry.angle (p x) (p c) (p z)
            ≤ delta * lam := by
        linarith
      simpa [EuclideanGeometry.angle_comm] using h
    have hlargeY :=
      support_one_and_small_angle_force_large_third
        hp hcap hn hdelta0 ht hlam
        hzB hyz.symm hyB.symm
        Ca hA hsupA hsmallBZY
    have hlargeX :=
      support_one_and_small_angle_force_large_third
        hp hcap hn hdelta0 ht hlam
        hzC hxz.symm hxC.symm
        Ca hA hsupA hsmallCZX
    exact ⟨rfl, hlargeY, hlargeX⟩

#print axioms support_one_and_small_angle_force_large_third
#print axioms hamiltonian_residual_support_one_amplification

end JSP000404Research
