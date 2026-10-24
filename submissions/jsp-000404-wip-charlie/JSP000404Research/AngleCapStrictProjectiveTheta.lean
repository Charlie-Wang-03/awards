import JSP000404Research.AngleCapNoncollinear
import JSP000404Research.SignedRayAngle
import JSP000404Research.CentreProjectiveCycle
import Mathlib.Tactic

/-!
# Genuine AngleCap makes canonical projective ray parameters injective

Two distinct original rays with exactly the same projective theta
have physical angle either 0 or pi, violating the positive
original-plane AngleCap. Thus neither coincident nor antipodal
projective ray directions can occur at an actual centre. This
cannot be inferred from injectivity of the planar point map alone.
-/

namespace JSP000404Research

/-- Canonical projective angle data around an original centre are injective
under a strictly positive global AngleCap. -/
theorem rayThetaAt_injective_of_AngleCap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    (i : V) :
    Function.Injective (rayThetaAt hp i) := by
  intro j k htheta
  by_contra hne
  have hjkVal : j.1 ≠ k.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hdist :
      projectiveRayDistance
        (rayThetaAt hp i j) (rayThetaAt hp i k) = 0 := by
    simp [projectiveRayDistance, htheta, Real.pi_pos.le]
  have hsmall :
      projectiveRayDistance
        (rayThetaAt hp i j) (rayThetaAt hp i k) < lam := by
    rw [hdist]
    exact hlam
  have hangle :=
    actual_angle_eq_projective_of_projective_lt_lam
      hp hcap j k hne hsmall
  have hzero :
      EuclideanGeometry.angle (p j.1) (p i) (p k.1) = 0 := by
    simpa [hdist] using hangle
  have hpos :=
    angleCap_actual_angle_pos_of_distinct
      hp hcap hlam j.2 hjkVal k.2.symm
  linarith

/-- The canonical projective angle list of a centre cycle has no repeated
values, a stronger property than its existing nondecreasing-order witness. -/
theorem centreProjectiveCycle_angles_nodup_of_AngleCap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    (i : V) (C : CentreProjectiveCycle hp i) :
    C.angles.Nodup := by
  simpa [CentreProjectiveCycle.angles] using
    C.nodup.map (rayThetaAt_injective_of_AngleCap hp hcap hlam i)

/-- A finite strictly ordered list has strictly positive successive
projective differences, not merely nonnegative ones. -/
theorem successiveDiffsFrom_pos_of_sorted_nodup
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hnodup : (a :: xs).Nodup) :
    ∀ g ∈ successiveDiffsFrom a xs, 0 < g := by
  induction xs generalizing a with
  | nil =>
      intro g hg
      simp [successiveDiffsFrom] at hg
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hsorted
      have hn := List.nodup_cons.mp hnodup
      have hle : a ≤ b := hp.1 b (by simp)
      have hneq : a ≠ b := by
        intro heq
        apply hn.1
        simpa [heq]
      have hlt : a < b := lt_of_le_of_ne hle hneq
      intro g hg
      simp only [successiveDiffsFrom, List.mem_cons] at hg
      rcases hg with rfl | hg
      · linarith
      · exact ih b hp.2 hn.2 g hg

/-- Every normalized cyclic projective gap is strictly positive under
genuine original-plane AngleCap. This strengthens the previously known
nonnegative gap theorem and includes the wrap gap. -/
theorem centreProjectiveCycle_gaps_pos_of_AngleCap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    (i : V) (C : CentreProjectiveCycle hp i) :
    ∀ g ∈ C.gaps, 0 < g := by
  obtain ⟨a, xs, hangles⟩ :
      ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil => exact False.elim (C.angles_nonempty h)
    | cons a xs => exact ⟨a, xs, rfl⟩
  have hsorted : (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hangles] using C.angles_pairwise
  have hnodup : (a :: xs).Nodup := by
    simpa [hangles] using
      centreProjectiveCycle_angles_nodup_of_AngleCap
        hp hcap hlam i C
  have hall : ∀ theta ∈ a :: xs, theta < Real.pi := by
    intro theta htheta
    exact (C.angle_mem_bounds (by simpa [hangles] using htheta)).2
  have ha0 : 0 ≤ a :=
    (C.angle_mem_bounds (by rw [hangles]; simp)).1
  intro g hg
  rw [CentreProjectiveCycle.gaps, hangles] at hg
  simp only [normalizedProjectiveGaps, List.mem_map] at hg
  obtain ⟨d, hd, rfl⟩ := hg
  have hdpos : 0 < d := by
    simp only [projectiveGaps, List.mem_append, List.mem_singleton] at hd
    rcases hd with hdiff | rfl
    · exact successiveDiffsFrom_pos_of_sorted_nodup
        a xs hsorted hnodup d hdiff
    · have hlast := getLastD_lt_pi_of_all_lt a xs hall
      linarith
  exact div_pos hdpos Real.pi_pos

#print axioms successiveDiffsFrom_pos_of_sorted_nodup
#print axioms centreProjectiveCycle_gaps_pos_of_AngleCap

#print axioms rayThetaAt_injective_of_AngleCap
#print axioms centreProjectiveCycle_angles_nodup_of_AngleCap

end JSP000404Research
