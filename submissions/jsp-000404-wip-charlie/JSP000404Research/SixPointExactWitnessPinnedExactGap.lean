import JSP000404Research.ExactWitnessCanonicalUnitGap
import JSP000404Research.SixPointExactWitnessSupportThree
import JSP000404Research.CyclicQuotientRotation
import Mathlib.Tactic

/-!
# Exact scaled unit gap inside the pinned five-gap support-three shape

At a six-point support-three exact-witness centre, pinning the sharp top ray
gives a five-position quotient pattern with exactly three positive positions:

  qFirst, qHidden, qLast,

and two zero positions.

ExactWitnessCanonicalUnitGap supplies one canonical gap whose scaled width is
exactly one.  Cyclic rotation preserves membership of that same gap value.
Because floor(1)=1, the exact gap cannot occupy either zero-quotient position.

Hence, in the pinned rotation, the exact gap lies at one of the three positive
positions.  This strengthens the earlier statement "some positive quotient is
one": the selected position has both quotient one and exact scaled width one.
-/

namespace JSP000404Research

/-- Pure five-position list arithmetic: an exact scaled-unit gap in a
three-positive/two-zero quotient pattern must occur at one of the three
positive positions. -/
theorem five_gap_exact_unit_lies_at_positive_position
    (t : ℝ)
    (gs : List ℝ)
    (qFirst qLast qHidden : ℕ)
    (qmid : List ℕ)
    (hlen : gs.length = 5)
    (hq :
      quotientList t gs =
        qFirst :: qmid ++ [qLast])
    (hshape :
      qmid = [qHidden,0,0] ∨
      qmid = [0,qHidden,0] ∨
      qmid = [0,0,qHidden])
    (hexact :
      ∃ g ∈ gs, t * g = 1) :
    ∃ gFirst g₁ g₂ g₃ gLast : ℝ,
      gs = [gFirst,g₁,g₂,g₃,gLast] ∧
      (
        (qFirst = 1 ∧ t * gFirst = 1)
        ∨
        (qmid = [qHidden,0,0] ∧
          qHidden = 1 ∧ t * g₁ = 1)
        ∨
        (qmid = [0,qHidden,0] ∧
          qHidden = 1 ∧ t * g₂ = 1)
        ∨
        (qmid = [0,0,qHidden] ∧
          qHidden = 1 ∧ t * g₃ = 1)
        ∨
        (qLast = 1 ∧ t * gLast = 1)
      ) := by
  rcases gs with _ | gFirst gs
  · simp at hlen
  rcases gs with _ | g₁ gs
  · simp at hlen
  rcases gs with _ | g₂ gs
  · simp at hlen
  rcases gs with _ | g₃ gs
  · simp at hlen
  rcases gs with _ | gLast gs
  · simp at hlen
  have hnil : gs = [] := by
    simpa using hlen
  subst gs
  refine ⟨gFirst, g₁, g₂, g₃, gLast, rfl, ?_⟩
  obtain ⟨g, hg, hscale⟩ := hexact
  simp only [List.mem_cons, List.mem_singleton] at hg
  rcases hshape with hshape | hshape | hshape
  · rw [hshape] at hq
    simp [quotientList] at hq
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · left
      have hfloor : Nat.floor (t * gFirst) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨by omega, hscale⟩
    · right; left
      have hfloor : Nat.floor (t * g₁) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨hshape, by omega, hscale⟩
    · have hfloor : Nat.floor (t * g₂) = 1 := by
        rw [hscale]
        norm_num
      omega
    · have hfloor : Nat.floor (t * g₃) = 1 := by
        rw [hscale]
        norm_num
      omega
    · right; right; right; right
      have hfloor : Nat.floor (t * gLast) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨by omega, hscale⟩
  · rw [hshape] at hq
    simp [quotientList] at hq
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · left
      have hfloor : Nat.floor (t * gFirst) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨by omega, hscale⟩
    · have hfloor : Nat.floor (t * g₁) = 1 := by
        rw [hscale]
        norm_num
      omega
    · right; right; left
      have hfloor : Nat.floor (t * g₂) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨hshape, by omega, hscale⟩
    · have hfloor : Nat.floor (t * g₃) = 1 := by
        rw [hscale]
        norm_num
      omega
    · right; right; right; right
      have hfloor : Nat.floor (t * gLast) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨by omega, hscale⟩
  · rw [hshape] at hq
    simp [quotientList] at hq
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · left
      have hfloor : Nat.floor (t * gFirst) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨by omega, hscale⟩
    · have hfloor : Nat.floor (t * g₁) = 1 := by
        rw [hscale]
        norm_num
      omega
    · have hfloor : Nat.floor (t * g₂) = 1 := by
        rw [hscale]
        norm_num
      omega
    · right; right; right; left
      have hfloor : Nat.floor (t * g₃) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨hshape, by omega, hscale⟩
    · right; right; right; right
      have hfloor : Nat.floor (t * gLast) = 1 := by
        rw [hscale]
        norm_num
      exact ⟨by omega, hscale⟩

/-- Exact-witness specialization: after any rotation whose quotient list has
the pinned support-three shape, the rotated gap list has an exact scaled-unit
gap at one of the three positive positions. -/
theorem exactWitness_pinned_support_three_exact_unit_position
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n k : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (qFirst qLast qHidden : ℕ)
    (qmid : List ℕ)
    (hqRot :
      (quotientList t C.gaps).rotate k =
        qFirst :: qmid ++ [qLast])
    (hshape :
      qmid = [qHidden,0,0] ∨
      qmid = [0,qHidden,0] ∨
      qmid = [0,0,qHidden]) :
    ∃ gFirst g₁ g₂ g₃ gLast : ℝ,
      C.gaps.rotate k =
        [gFirst,g₁,g₂,g₃,gLast] ∧
      (
        (qFirst = 1 ∧ t * gFirst = 1)
        ∨
        (qmid = [qHidden,0,0] ∧
          qHidden = 1 ∧ t * g₁ = 1)
        ∨
        (qmid = [0,qHidden,0] ∧
          qHidden = 1 ∧ t * g₂ = 1)
        ∨
        (qmid = [0,0,qHidden] ∧
          qHidden = 1 ∧ t * g₃ = 1)
        ∨
        (qLast = 1 ∧ t * gLast = 1)
      ) := by
  obtain ⟨e, _heq, hscaled⟩ :=
    exists_exactWitness_canonical_unit_gap
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
  have hmem :
      C.gaps.get e ∈ C.gaps.rotate k := by
    exact (List.mem_rotate).2 (List.get_mem C.gaps e)
  have hexact :
      ∃ g ∈ C.gaps.rotate k, t * g = 1 :=
    ⟨C.gaps.get e, hmem, hscaled⟩
  have hlen :
      (C.gaps.rotate k).length = 5 := by
    rw [List.length_rotate, C.gaps_length,
      centreRayList_length_eq_five_of_card_six C hcard]
  have hq :
      quotientList t (C.gaps.rotate k) =
        qFirst :: qmid ++ [qLast] := by
    rw [quotientList_rotate]
    exact hqRot
  exact five_gap_exact_unit_lies_at_positive_position
    t (C.gaps.rotate k)
    qFirst qLast qHidden qmid
    hlen hq hshape hexact

#print axioms five_gap_exact_unit_lies_at_positive_position
#print axioms exactWitness_pinned_support_three_exact_unit_position

end JSP000404Research
