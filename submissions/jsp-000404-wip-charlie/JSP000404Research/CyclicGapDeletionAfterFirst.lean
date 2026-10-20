import JSP000404Research.LastProjectiveGapDeletion
import Mathlib.Tactic

/-!
# One-step cyclic deletion after the first projective angle

This unifies the last and the interior deletion lemmas into one lemma
parameterized by the prefix and suffix around a deleted nonfirst angle.

The next angle is the head of the suffix; for an empty suffix, it is
the wrap-around angle a + pi. This avoids a duplicated two-case
hypothesis while retaining the *actual* circular successor gap.

This is a kernel-checked local deletion result, not an unconditional
global compensated-deletion existence claim.
-/

namespace JSP000404Research

open Real

/-- Deleting any selected nonfirst angle from an ordered circular angle list
gains a full excess-exponent unit if its preceding and cyclic-following
normalized gap quotients are both positive. -/
theorem listExponent_gain_delete_after_first
    (t a x : ℝ) (pre rest : List ℝ)
    (ht : 0 ≤ t)
    (hleft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hright :
      0 ≤ (rest.headD (a + Real.pi) - x) / Real.pi)
    (hleftPos :
      1 ≤ Nat.floor (t * ((x - pre.getLastD a) / Real.pi)))
    (hrightPos :
      1 ≤ Nat.floor (t *
        ((rest.headD (a + Real.pi) - x) / Real.pi))) :
    listExponent
      (quotientList t
        (normalizedProjectiveGaps (a :: (pre ++ x :: rest)))) + 1
      ≤
    listExponent
      (quotientList t
        (normalizedProjectiveGaps (a :: (pre ++ rest)))) := by
  cases rest with
  | nil =>
      simpa only [List.append_nil, List.headD_nil] using
        (listExponent_gain_delete_last
          (t := t) (a := a) (x := x) (pre := pre)
          ht hleft
          (by simpa only [List.headD_nil] using hright)
          hleftPos
          (by simpa only [List.headD_nil] using hrightPos))
  | cons y tail =>
      simpa only [List.headD_cons] using
        (listExponent_gain_delete_interior
          (t := t) (a := a) (x := x) (y := y)
          (pre := pre) (tail := tail)
          ht hleft
          (by simpa only [List.headD_cons] using hright)
          hleftPos
          (by simpa only [List.headD_cons] using hrightPos))

#print axioms listExponent_gain_delete_after_first

end JSP000404Research
