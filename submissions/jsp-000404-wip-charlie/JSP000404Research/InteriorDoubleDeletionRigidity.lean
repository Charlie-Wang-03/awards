import JSP000404Research.MiddleProjectiveGapDeletion
import Mathlib.Tactic

/-!
# Rigidity of two consecutive interior deletions

Consider a sorted projective angle list

  a :: (pre ++ x :: y :: z :: tail).

Delete x first and then y.  The three old adjacent normalized gaps are

  g0 = (x-prev)/pi,
  g1 = (y-x)/pi,
  g2 = (z-y)/pi,

where prev = pre.getLastD a.

If the Sendov quotient-list exponent is unchanged by both deletions, then at
most one of floor(t*g0), floor(t*g1), floor(t*g2) is positive.

The reason is exact and local.  Positivity of q0,q1 would already force a unit
gain at the first deletion.  After the first deletion the new left quotient at
y is q0+q1+carry, so positivity of either q0 or q1 together with q2 would force
a unit gain at the second deletion.

This is the angle-list bridge needed before instantiating two-step rigidity
with two adjacent minimum-centre rays in a concrete CentreProjectiveCycle.
-/

namespace JSP000404Research

open Real

theorem interior_double_deletion_triple_pairwise_sparse
    {t a x y z : ℝ}
    {pre tail : List ℝ}
    (ht : 0 ≤ t)
    (hg0 :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hg1 :
      0 ≤ (y - x) / Real.pi)
    (hg2 :
      0 ≤ (z - y) / Real.pi)
    (hEq1 :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tail))))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ x :: y :: z :: tail)))))
    (hEq2 :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ z :: tail))))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tail))))) :
    let q0 :=
      Nat.floor
        (t * ((x - pre.getLastD a) / Real.pi))
    let q1 :=
      Nat.floor
        (t * ((y - x) / Real.pi))
    let q2 :=
      Nat.floor
        (t * ((z - y) / Real.pi))
    ¬ (1 ≤ q0 ∧ 1 ≤ q1) ∧
    ¬ (1 ≤ q0 ∧ 1 ≤ q2) ∧
    ¬ (1 ≤ q1 ∧ 1 ≤ q2) := by
  dsimp
  let g0 := (x - pre.getLastD a) / Real.pi
  let g1 := (y - x) / Real.pi
  let g2 := (z - y) / Real.pi
  let q0 := Nat.floor (t * g0)
  let q1 := Nat.floor (t * g1)
  let q2 := Nat.floor (t * g2)
  have hlocal :
      (y - pre.getLastD a) / Real.pi = g0 + g1 := by
    dsimp [g0, g1]
    field_simp [Real.pi_ne_zero]
    ring
  have hgMerged :
      0 ≤ (y - pre.getLastD a) / Real.pi := by
    rw [hlocal]
    exact add_nonneg hg0 hg1
  obtain ⟨carry, _hcarry, hmerge0⟩ :=
    natFloor_scaled_gap_merge ht hg0 hg1
  have hmerge :
      Nat.floor
          (t * ((y - pre.getLastD a) / Real.pi))
        =
      q0 + q1 + carry := by
    rw [hlocal]
    simpa [q0, q1, g0, g1] using hmerge0
  have h01 : ¬ (1 ≤ q0 ∧ 1 ≤ q1) := by
    rintro ⟨hq0, hq1⟩
    have hgain :=
      listExponent_gain_delete_interior
        (t := t) (a := a) (x := x) (y := y)
        (pre := pre) (tail := z :: tail)
        ht hg0 hg1
        (by simpa [q0, g0] using hq0)
        (by simpa [q1, g1] using hq1)
    rw [hEq1] at hgain
    omega
  have h02 : ¬ (1 ≤ q0 ∧ 1 ≤ q2) := by
    rintro ⟨hq0, hq2⟩
    have hqMerged :
        1 ≤ Nat.floor
          (t * ((y - pre.getLastD a) / Real.pi)) := by
      rw [hmerge]
      omega
    have hgain :=
      listExponent_gain_delete_interior
        (t := t) (a := a) (x := y) (y := z)
        (pre := pre) (tail := tail)
        ht hgMerged hg2
        hqMerged
        (by simpa [q2, g2] using hq2)
    rw [hEq2] at hgain
    omega
  have h12 : ¬ (1 ≤ q1 ∧ 1 ≤ q2) := by
    rintro ⟨hq1, hq2⟩
    have hqMerged :
        1 ≤ Nat.floor
          (t * ((y - pre.getLastD a) / Real.pi)) := by
      rw [hmerge]
      omega
    have hgain :=
      listExponent_gain_delete_interior
        (t := t) (a := a) (x := y) (y := z)
        (pre := pre) (tail := tail)
        ht hgMerged hg2
        hqMerged
        (by simpa [q2, g2] using hq2)
    rw [hEq2] at hgain
    omega
  simpa [q0, q1, q2, g0, g1, g2] using
    And.intro h01 (And.intro h02 h12)

/-- Equivalent zero-shape formulation: among the three old local quotients,
at least two vanish. -/
theorem interior_double_deletion_triple_shape
    {t a x y z : ℝ}
    {pre tail : List ℝ}
    (ht : 0 ≤ t)
    (hg0 :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hg1 :
      0 ≤ (y - x) / Real.pi)
    (hg2 :
      0 ≤ (z - y) / Real.pi)
    (hEq1 :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tail))))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ x :: y :: z :: tail)))))
    (hEq2 :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ z :: tail))))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tail))))) :
    let q0 :=
      Nat.floor
        (t * ((x - pre.getLastD a) / Real.pi))
    let q1 :=
      Nat.floor
        (t * ((y - x) / Real.pi))
    let q2 :=
      Nat.floor
        (t * ((z - y) / Real.pi))
    (q0 = 0 ∧ q1 = 0) ∨
    (q0 = 0 ∧ q2 = 0) ∨
    (q1 = 0 ∧ q2 = 0) := by
  dsimp
  have hs :=
    interior_double_deletion_triple_pairwise_sparse
      ht hg0 hg1 hg2 hEq1 hEq2
  let q0 :=
    Nat.floor
      (t * ((x - pre.getLastD a) / Real.pi))
  let q1 :=
    Nat.floor
      (t * ((y - x) / Real.pi))
  let q2 :=
    Nat.floor
      (t * ((z - y) / Real.pi))
  change
    ¬ (1 ≤ q0 ∧ 1 ≤ q1) ∧
    ¬ (1 ≤ q0 ∧ 1 ≤ q2) ∧
    ¬ (1 ≤ q1 ∧ 1 ≤ q2) at hs
  by_cases h0 : q0 = 0
  · by_cases h1 : q1 = 0
    · exact Or.inl ⟨h0, h1⟩
    · have h1p : 1 ≤ q1 := by omega
      have h2 : q2 = 0 := by
        by_contra h2
        exact hs.2.2 ⟨h1p, by omega⟩
      exact Or.inr (Or.inl ⟨h0, h2⟩)
  · have h0p : 1 ≤ q0 := by omega
    have h1 : q1 = 0 := by
      by_contra h1
      exact hs.1 ⟨h0p, by omega⟩
    have h2 : q2 = 0 := by
      by_contra h2
      exact hs.2.1 ⟨h0p, by omega⟩
    exact Or.inr (Or.inr ⟨h1, h2⟩)

#print axioms interior_double_deletion_triple_pairwise_sparse
#print axioms interior_double_deletion_triple_shape

end JSP000404Research
