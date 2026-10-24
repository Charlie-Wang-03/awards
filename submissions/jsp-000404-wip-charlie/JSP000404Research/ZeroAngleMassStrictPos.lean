import JSP000404Research.CyclicActualAngles
import JSP000404Research.AngleCapNoncollinear
import Mathlib.Tactic

/-!
# Genuine zero-quotient angle mass cannot vanish when a zero slot exists

This module combines actual original-plane AngleCap positivity with an
aligned finite-list fact. It does not assume or prove any global NET payment.
-/

namespace JSP000404Research

/-- A zero quotient coordinate contributes positive mass if every paired
actual angle is positive and the quotient/angle lengths agree. -/
theorem listZeroAngleMass_pos_of_zero_mem_and_angles_pos
    (qs : List ℕ) (As : List ℝ)
    (hlen : qs.length = As.length)
    (hpos : ∀ A ∈ As, 0 < A)
    (hzero : 0 ∈ qs) :
    0 < listZeroAngleMass qs As := by
  induction qs generalizing As with
  | nil =>
      simp at hzero
  | cons q qs ih =>
      cases As with
      | nil =>
          simp at hlen
      | cons A As =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hA : 0 < A := hpos A (by simp)
          have hrest : ∀ x ∈ As, 0 < x := by
            intro x hx
            exact hpos x (by simp [hx])
          by_cases hq : q = 0
          · subst q
            have hmass0 :
                0 ≤ listZeroAngleMass qs As :=
              listZeroAngleMass_nonneg qs As
                (fun x hx => (hrest x hx).le)
            simp [listZeroAngleMass]
            linarith
          · have hzeroTail : 0 ∈ qs := by
              simpa [List.mem_cons, eq_comm, hq] using hzero
            have ht := ih hlen hrest hzeroTail
            simpa [listZeroAngleMass, hq] using ht

/-- The original-plane global cap makes every consecutive angle of a nodup
ray list strictly positive. Unlike projective gaps, these are actual angles. -/
theorem all_consecutiveRayAngles_pos_of_AngleCap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    (i : V) (r : OtherVertex i) (rs : List (OtherVertex i))
    (hnodup : (r :: rs).Nodup) :
    ∀ A ∈ consecutiveRayAngles (p := p) i r rs, 0 < A := by
  induction rs generalizing r with
  | nil =>
      intro A hA
      simp [consecutiveRayAngles] at hA
  | cons s rs ih =>
      have hne : r ≠ s := by
        intro heq
        exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
      have hneV : r.1 ≠ s.1 := by
        intro heq
        exact hne (Subtype.ext heq)
      have hfirst :
          0 < EuclideanGeometry.angle (p r.1) (p i) (p s.1) :=
        angleCap_actual_angle_pos_of_distinct
          hp hcap hlam r.2 hneV s.2.symm
      have htail : (s :: rs).Nodup :=
        (List.nodup_cons.mp hnodup).2
      intro A hA
      simp only [consecutiveRayAngles, List.mem_cons] at hA
      rcases hA with rfl | hA
      · exact hfirst
      · exact ih s htail A hA

#print axioms listZeroAngleMass_pos_of_zero_mem_and_angles_pos
#print axioms all_consecutiveRayAngles_pos_of_AngleCap

end JSP000404Research
