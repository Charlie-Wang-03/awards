import JSP000404Research.CutSupportThreeBadSmallAngle
import JSP000404Research.SixPointSupportThreeShape
import Mathlib.Tactic

/-!
# Nonnegative sorted cut-cycle real gaps
Shared, sorry-free elementary lemma for both support-two and support-three
original-plane cut arguments. Extracted from CutSupportThreeBadSameBand.
-/

namespace JSP000404Research

/-- Cyclic real gaps of a sorted list in [0,width) are nonnegative. -/
theorem cyclicRealGapsAt_nonneg_of_sorted
    {width a : ℝ} {xs : List ℝ}
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < width) :
    ∀ g ∈ cyclicRealGapsAt width (a :: xs), 0 ≤ g := by
  intro g hg
  simp only [cyclicRealGapsAt, List.mem_append,
    List.mem_singleton] at hg
  rcases hg with hg | rfl
  · induction xs generalizing a with
    | nil =>
        simp [successiveDiffsFrom] at hg
    | cons b bs ih =>
        have hp := List.pairwise_cons.mp hsorted
        simp only [successiveDiffsFrom, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact sub_nonneg.mpr (hp.1 b (by simp))
        · have hb0 : 0 ≤ b :=
            ha0.trans (hp.1 b (by simp))
          exact ih (a := b) hb0 hp.2
            (by
              intro x hx
              exact hall x (by simp [hx])) hg
  · have hlast :
        xs.getLastD a < width :=
      hall _ (List.getLastD_mem_cons)
    have hafirst :
        a ≤ xs.getLastD a :=
      head_le_getLastD_of_pairwise a xs hsorted
    linarith

end JSP000404Research
