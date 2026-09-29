import JSP000404Research.FiniteProjectiveRays
import JSP000404Research.CanonicalRayReversal
import Mathlib.Tactic

/-!
# Canonical sign acyclicity on a triangle

The canonical signed projective representation uses parameters in [0,pi).
Consequently sign=true means that the represented nonzero vector belongs to
the lexicographically positive closed upper half-plane:

  y > 0, or y = 0 and x > 0.

This half-plane is closed under addition and disjoint from its negative.

Therefore three distinct planar points cannot have opposite canonical signs
at all three vertices of their triangle.  If they did, after orienting the
triangle according to one edge sign, all three cyclic edge vectors would lie
in the positive half-plane while summing to zero.

This is the geometric obstruction needed by the Hamiltonian residual route.
-/

namespace JSP000404Research

/-- Strict positive half-plane with the horizontal boundary oriented to the
right.  This is the lexicographic positivity relation for coordinates (y,x). -/
def PlaneHalfPositive (x : Plane) : Prop :=
  0 < x 1 ∨ (x 1 = 0 ∧ 0 < x 0)

theorem planeHalfPositive_add
    {x y : Plane}
    (hx : PlaneHalfPositive x)
    (hy : PlaneHalfPositive y) :
    PlaneHalfPositive (x + y) := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · left
      change 0 < x 1 + y 1
      linarith
    · left
      change 0 < x 1 + y 1
      linarith [hy.1]
  · rcases hy with hy | hy
    · left
      change 0 < x 1 + y 1
      linarith [hx.1]
    · right
      constructor
      · change x 1 + y 1 = 0
        linarith [hx.1, hy.1]
      · change 0 < x 0 + y 0
        linarith [hx.2, hy.2]

theorem planeHalfPositive_ne_zero
    {x : Plane}
    (hx : PlaneHalfPositive x) :
    x ≠ 0 := by
  intro h
  subst x
  rcases hx with hx | hx <;> simp at hx

theorem planeHalfPositive_not_neg
    {x : Plane}
    (hx : PlaneHalfPositive x) :
    ¬ PlaneHalfPositive (-x) := by
  intro hneg
  have hsum :=
    planeHalfPositive_add hx hneg
  have hzero : x + (-x) = 0 := by abel
  rw [hzero] at hsum
  exact planeHalfPositive_ne_zero hsum rfl

theorem planeHalfPositive_smul_of_pos
    {rho : ℝ} {x : Plane}
    (hrho : 0 < rho)
    (hx : PlaneHalfPositive x) :
    PlaneHalfPositive (rho • x) := by
  rcases hx with hx | hx
  · left
    change 0 < rho * x 1
    positivity
  · right
    constructor
    · change rho * x 1 = 0
      rw [hx.1]
      simp
    · change 0 < rho * x 0
      positivity

theorem rayDirection_halfPositive
    {theta : ℝ}
    (htheta0 : 0 ≤ theta)
    (hthetapi : theta < Real.pi) :
    PlaneHalfPositive (rayDirection theta) := by
  by_cases htheta : theta = 0
  · subst theta
    right
    constructor <;> simp [PlaneHalfPositive, rayDirection]
  · left
    have hthetaPos : 0 < theta := lt_of_le_of_ne htheta0 (Ne.symm htheta)
    have hsin : 0 < Real.sin theta :=
      Real.sin_pos_of_pos_of_lt_pi hthetaPos hthetapi
    simpa [PlaneHalfPositive, rayDirection] using hsin

theorem positive_signedRay_of_true
    {rho theta : ℝ}
    (hrho : 0 < rho)
    (htheta0 : 0 ≤ theta)
    (hthetapi : theta < Real.pi) :
    PlaneHalfPositive
      (rho • signedRayDirection true theta) := by
  apply planeHalfPositive_smul_of_pos hrho
  simpa [signedRayDirection] using
    rayDirection_halfPositive htheta0 hthetapi

/-- A canonical ray whose Boolean sign is true points into the positive
half-plane. -/
theorem displacement_halfPositive_of_raySign_true
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V}
    (hij : i ≠ j)
    (hsign :
      raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) = true) :
    PlaneHalfPositive (p j - p i) := by
  let v : OtherVertex i := ⟨j, hij.symm⟩
  rw [rayRepAt_eq hp i v]
  have hrho := rayRhoAt_pos hp i v
  have htheta0 := rayThetaAt_nonneg hp i v
  have hthetapi := rayThetaAt_lt_pi hp i v
  rw [hsign]
  exact positive_signedRay_of_true hrho htheta0 hthetapi

theorem bool_eq_not_of_ne'
    {a b : Bool}
    (h : a ≠ b) :
    b = !a := by
  cases a <;> cases b <;> simp_all

/-- Three distinct vertices cannot each see the other two with opposite
canonical signs. -/
theorem impossible_triangle_all_three_sign_splits
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    (ha :
      raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a) ≠
        raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a))
    (hb :
      raySignAt hp b (⟨a, hab⟩ : OtherVertex b) ≠
        raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b))
    (hc :
      raySignAt hp c (⟨a, hac⟩ : OtherVertex c) ≠
        raySignAt hp c (⟨b, hbc⟩ : OtherVertex c)) :
    False := by
  let sab :=
    raySignAt hp a (⟨b, hab.symm⟩ : OtherVertex a)
  have hba :
      raySignAt hp b (⟨a, hab⟩ : OtherVertex b) = !sab := by
    simpa [sab] using raySignAt_reverse_eq_not hp hab
  have hacSign :
      raySignAt hp a (⟨c, hac.symm⟩ : OtherVertex a) = !sab :=
    bool_eq_not_of_ne' ha
  have hbcSign :
      raySignAt hp b (⟨c, hbc.symm⟩ : OtherVertex b) = sab := by
    have h :=
      bool_eq_not_of_ne' hb
    rw [hba] at h
    cases hs : sab <;> simp [hs] at h ⊢
    · exact h
    · exact h
  have hca :
      raySignAt hp c (⟨a, hac⟩ : OtherVertex c) = sab := by
    have hrev := raySignAt_reverse_eq_not hp hac
    rw [hacSign] at hrev
    cases hs : sab <;> simpa [hs] using hrev
  have hcb :
      raySignAt hp c (⟨b, hbc⟩ : OtherVertex c) = !sab := by
    simpa [hbcSign] using raySignAt_reverse_eq_not hp hbc

  cases hs : sab with
  | false =>
      have hAC :
          PlaneHalfPositive (p c - p a) := by
        apply displacement_halfPositive_of_raySign_true hp hac
        rw [hacSign, hs]
        decide
      have hCB :
          PlaneHalfPositive (p b - p c) := by
        apply displacement_halfPositive_of_raySign_true hp hbc.symm
        rw [hcb, hs]
        decide
      have hBA :
          PlaneHalfPositive (p a - p b) := by
        apply displacement_halfPositive_of_raySign_true hp hab.symm
        rw [hba, hs]
        decide
      have hsum1 := planeHalfPositive_add hAC hCB
      have hsum2 := planeHalfPositive_add hsum1 hBA
      have hzero :
          (p c - p a) + (p b - p c) + (p a - p b) = 0 := by
        abel
      rw [hzero] at hsum2
      exact planeHalfPositive_ne_zero hsum2 rfl
  | true =>
      have hAB :
          PlaneHalfPositive (p b - p a) := by
        apply displacement_halfPositive_of_raySign_true hp hab
        simpa [sab, hs]
      have hBC :
          PlaneHalfPositive (p c - p b) := by
        apply displacement_halfPositive_of_raySign_true hp hbc
        simpa [hbcSign, hs]
      have hCA :
          PlaneHalfPositive (p a - p c) := by
        apply displacement_halfPositive_of_raySign_true hp hac.symm
        simpa [hca, hs]
      have hsum1 := planeHalfPositive_add hAB hBC
      have hsum2 := planeHalfPositive_add hsum1 hCA
      have hzero :
          (p b - p a) + (p c - p b) + (p a - p c) = 0 := by
        abel
      rw [hzero] at hsum2
      exact planeHalfPositive_ne_zero hsum2 rfl

#print axioms planeHalfPositive_add
#print axioms rayDirection_halfPositive
#print axioms displacement_halfPositive_of_raySign_true
#print axioms impossible_triangle_all_three_sign_splits

end JSP000404Research
