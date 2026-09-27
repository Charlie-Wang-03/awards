import JSP000404Research.CutSupportTwoBadSmallAngle
import JSP000404Research.CutBadOrdinaryMismatchShape
import Mathlib.Tactic

/-!
# Band-local form of the support-two bad small-angle witness

The support-two sub-half-angle theorem selects an ordinary quotient-zero
cut gap.  At a saturation-bad exact n-3 centre, every ordinary q=0 step has
old-band jump either 0 or 1: if the band jump is positive, the exact
saturation mismatch theorem forces it to be exactly one.

Thus a support-two bad centre carries a non-top small-angle pair whose old
cut-band labels are equal or adjacent.
-/

namespace JSP000404Research

open BinaryEdgePartition

/-- In a length-aligned ordinary step profile, a q=0 position has band jump
0 or 1 under the exact saturation unit-mismatch rule. -/
theorem zero_ordinary_step_band_jump_le_one
    {qs bs : List ℕ}
    (hdom : List.Forall₂ (· ≤ ·) qs bs)
    (hunit :
      List.Forall₂
        (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
        qs bs)
    {r : Fin qs.length}
    (hr0 : qs.get r = 0) :
    ∃ rb : Fin bs.length,
      rb.val = r.val ∧
      bs.get rb ≤ 1 := by
  have hlen := List.Forall₂.length_eq hdom
  let rb : Fin bs.length := ⟨r.val, by simpa [hlen] using r.isLt⟩
  have hdomGet :
      qs.get r ≤ bs.get rb := by
    exact List.Forall₂.get hdom r rb (by rfl)
  have hunitGet :
      qs.get r = 0 ∧ bs.get rb ≠ 0 → bs.get rb = 1 := by
    exact List.Forall₂.get hunit r rb (by rfl)
  refine ⟨rb, rfl, ?_⟩
  by_cases hb0 : bs.get rb = 0
  · simp [hb0]
  · have hb1 := hunitGet ⟨hr0, hb0⟩
    omega

#print axioms zero_ordinary_step_band_jump_le_one

end JSP000404Research
