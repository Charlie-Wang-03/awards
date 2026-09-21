import JSP000404Research.DeficitTwo
import JSP000404Research.CentreSignPath
import JSP000404Research.SmallSameSignGapAngle
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# The unique small angle at a four-point support-two centre

At a centre of a four-point configuration there are exactly three canonical
projective rays and hence exactly three cyclic gaps.

In the lower branch, a deficit-two centre with quotient support two has
quotient sum n.  Thus the total scaled width of all quotient-zero gaps is at
most delta.  Since there are three gaps and exactly two positive quotients,
there is exactly one zero quotient gap.

The concrete lifted sign-path rule says a quotient-zero gap cannot be a sign
transition.  Therefore its genuine Euclidean angle is exactly its projective
gap (ordinary or wrap), and is at most delta*lambda.

This file packages the conclusion as the existence of one pair of distinct
non-centre rays making a genuinely small angle.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

theorem otherVertex_card_fin_four
    (i : Fin 4) :
    Fintype.card (OtherVertex i) = 3 := by
  change Fintype.card {j : Fin 4 // j ≠ i} = 3
  rw [Fintype.card_subtype_compl (fun j : Fin 4 => j = i)]
  simp

theorem centre_rays_length_fin_four
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i) :
    C.rays.length = 3 := by
  have hcard :=
    List.toFinset_card_of_nodup C.nodup
  rw [C.complete] at hcard
  have hother := otherVertex_card_fin_four i
  simpa [hother] using hcard.symm

theorem centre_rays_eq_three_fin_four
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i) :
    ∃ r0 r1 r2 : OtherVertex i,
      C.rays = [r0,r1,r2] := by
  exact List.length_eq_three.mp
    (centre_rays_length_fin_four i C)

/-- Pure three-gap remainder estimate.  If the three gaps sum to one, their
integer lower bounds sum to n, and t=n+delta, any quotient-zero gap has scaled
width at most delta. -/
theorem triple_zero_gap_scaled_le_delta
    {g0 g1 g2 t delta : ℝ}
    {q0 q1 q2 n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (hgap : g0 + g1 + g2 = 1)
    (hqsum : q0 + q1 + q2 = n)
    (hfloor0 : (q0 : ℝ) ≤ t * g0)
    (hfloor1 : (q1 : ℝ) ≤ t * g1)
    (hfloor2 : (q2 : ℝ) ≤ t * g2) :
    (q0 = 0 → t * g0 ≤ delta) ∧
    (q1 = 0 → t * g1 ≤ delta) ∧
    (q2 = 0 → t * g2 ≤ delta) := by
  have hqsumR :
      (q0 : ℝ) + (q1 : ℝ) + (q2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hqsum
  have htotal :
      t * g0 + t * g1 + t * g2 =
        (n : ℝ) + delta := by
    rw [← mul_add, ← mul_add, hgap, mul_one, ht]
  constructor
  · intro hq0
    have hq0R : (q0 : ℝ) = 0 := by simp [hq0]
    nlinarith
  · constructor
    · intro hq1
      have hq1R : (q1 : ℝ) = 0 := by simp [hq1]
      nlinarith
    · intro hq2
      have hq2R : (q2 : ℝ) = 0 := by simp [hq2]
      nlinarith

/-- Explicit three-gap formula for a four-point centre after naming its sorted
rays. -/
theorem centre_gaps_eq_three_rays
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2]) :
    C.gaps =
      [
        (rayThetaAt hp i r1 - rayThetaAt hp i r0) / Real.pi,
        (rayThetaAt hp i r2 - rayThetaAt hp i r1) / Real.pi,
        (rayThetaAt hp i r0 + Real.pi -
          rayThetaAt hp i r2) / Real.pi
      ] := by
  rw [CentreProjectiveCycle.gaps,
      CentreProjectiveCycle.angles, hrays]
  simp [normalizedProjectiveGaps, projectiveGaps,
    successiveDiffsFrom]

/-- Main four-point support-two conclusion: some pair of actual rays makes an
angle at most delta*lambda. -/
theorem exists_small_angle_pair_of_four_centre_deficit_two_support_two
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      EuclideanGeometry.angle (p x.1) (p i) (p y.1) ≤
        delta * lam := by
  obtain ⟨r0, r1, r2, hrays⟩ :=
    centre_rays_eq_three_fin_four i C
  let g0 :=
    (rayThetaAt hp i r1 - rayThetaAt hp i r0) / Real.pi
  let g1 :=
    (rayThetaAt hp i r2 - rayThetaAt hp i r1) / Real.pi
  let g2 :=
    (rayThetaAt hp i r0 + Real.pi -
      rayThetaAt hp i r2) / Real.pi
  let q0 := Nat.floor (t * g0)
  let q1 := Nat.floor (t * g1)
  let q2 := Nat.floor (t * g2)
  have hgaps : C.gaps = [g0,g1,g2] := by
    simpa [g0, g1, g2] using
      centre_gaps_eq_three_rays i C r0 r1 r2 hrays
  have hqlist :
      quotientList t C.gaps = [q0,q1,q2] := by
    rw [hgaps]
    simp [quotientList, q0, q1, q2]
  have hgapSum : g0 + g1 + g2 = 1 := by
    have hs := C.gaps_sum
    rw [hgaps] at hs
    simpa using hs
  have hdelta1 : delta < 1 := by linarith
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  have hstruct :=
    deficit_two_structure
      (centreQuotient C t) n hn hQ hdef
  have hqsumFn :
      (∑ r, centreQuotient C t r) = n := by
    rcases hstruct with h1 | h2
    · rw [hsupport] at h1
      omega
    · exact h2.2
  have hqsumList :
      (quotientList t C.gaps).sum = n := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hqsumFn
  have hqsum :
      q0 + q1 + q2 = n := by
    rw [hqlist] at hqsumList
    simpa using hqsumList
  have hsupportList :
      listPositiveCount [q0,q1,q2] = 2 := by
    have h :
        listPositiveCount (quotientList t C.gaps) = 2 := by
      rw [← centreQuotient_ofFn]
      rw [listPositiveCount_ofFn_eq_positiveSupport]
      exact hsupport
    rw [hqlist] at h
    exact h
  have ht1 : 1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hg0 : 0 ≤ g0 := by
    have h := C.gaps_nonneg g0
    apply h
    rw [hgaps]
    simp
  have hg1 : 0 ≤ g1 := by
    have h := C.gaps_nonneg g1
    apply h
    rw [hgaps]
    simp
  have hg2 : 0 ≤ g2 := by
    have h := C.gaps_nonneg g2
    apply h
    rw [hgaps]
    simp
  have hfloor0 : (q0 : ℝ) ≤ t * g0 := by
    dsimp [q0]
    exact Nat.floor_le (mul_nonneg htpos.le hg0)
  have hfloor1 : (q1 : ℝ) ≤ t * g1 := by
    dsimp [q1]
    exact Nat.floor_le (mul_nonneg htpos.le hg1)
  have hfloor2 : (q2 : ℝ) ≤ t * g2 := by
    dsimp [q2]
    exact Nat.floor_le (mul_nonneg htpos.le hg2)
  have hsmall :=
    triple_zero_gap_scaled_le_delta
      ht hgapSum hqsum hfloor0 hfloor1 hfloor2
  have hpair :
      [r0,r1,r2].Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    rw [← hrays]
    exact C.theta_sorted
  have horder01 :
      rayThetaAt hp i r0 ≤ rayThetaAt hp i r1 :=
    (List.pairwise_cons.mp hpair).1 r1 (by simp)
  have horder12 :
      rayThetaAt hp i r1 ≤ rayThetaAt hp i r2 :=
    (List.pairwise_cons.mp
      (List.pairwise_cons.mp hpair).2).1 r2 (by simp)
  have horder02 :
      rayThetaAt hp i r0 ≤ rayThetaAt hp i r2 :=
    (List.pairwise_cons.mp hpair).1 r2 (by simp)
  have hnod :
      r0 ≠ r1 ∧ r0 ≠ r2 ∧ r1 ≠ r2 := by
    have h := C.nodup
    rw [hrays] at h
    simpa using h
  have hchanges0 :=
    centre_changesOnlyOnPositive
      hp hcap htpos ht1 hlam i C r0 [r1,r2] hrays
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i r0)
        [raySignAt hp i r1,
          raySignAt hp i r2,
          !raySignAt hp i r0]
        [q0,q1,q2] := by
    rw [hqlist] at hchanges0
    simpa [liftedCentreSignPath] using hchanges0
  have hstep01 :
      raySignAt hp i r0 ≠ raySignAt hp i r1 →
        q0 ≠ 0 := hchanges.1
  have hstep12 :
      raySignAt hp i r1 ≠ raySignAt hp i r2 →
        q1 ≠ 0 := hchanges.2.1
  have hstep20 :
      raySignAt hp i r2 ≠ !raySignAt hp i r0 →
        q2 ≠ 0 := hchanges.2.2.1
  by_cases hq0 : q0 = 0
  · have hs01 :
        raySignAt hp i r0 = raySignAt hp i r1 := by
      by_contra hs
      exact hq0 (hstep01 hs)
    have hang :=
      actual_angle_le_delta_lam_of_ordinary_same_sign_gap
        hp htpos hlam i horder01 hs01 (hsmall.1 hq0)
    exact ⟨r0, r1, hnod.1, by simpa [g0] using hang⟩
  · by_cases hq1 : q1 = 0
    · have hs12 :
          raySignAt hp i r1 = raySignAt hp i r2 := by
        by_contra hs
        exact hq1 (hstep12 hs)
      have hang :=
        actual_angle_le_delta_lam_of_ordinary_same_sign_gap
          hp htpos hlam i horder12 hs12 (hsmall.2.1 hq1)
      exact ⟨r1, r2, hnod.2.2, by simpa [g1] using hang⟩
    · have hq2 : q2 = 0 := by
        by_contra hq2
        simp [listPositiveCount, hq0, hq1, hq2] at hsupportList
      have hs20 :
          raySignAt hp i r2 = !raySignAt hp i r0 := by
        by_contra hs
        exact hq2 (hstep20 hs)
      have hang :=
        actual_angle_le_delta_lam_of_wrap_same_sign_gap
          hp htpos hlam i horder02 hs20 (hsmall.2.2 hq2)
      exact ⟨r2, r0, hnod.2.1.symm,
        by simpa [g2] using hang⟩

#print axioms otherVertex_card_fin_four
#print axioms centre_rays_length_fin_four
#print axioms triple_zero_gap_scaled_le_delta
#print axioms exists_small_angle_pair_of_four_centre_deficit_two_support_two

end JSP000404Research
