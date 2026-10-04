import JSP000404Research.CyclicRealGapsCore
import JSP000404Research.ListZeroGapMass
import Mathlib.Tactic

/-!
# Zero-floor mass budget for a sorted local direction cycle

For a nonempty sorted list of local direction values in [0,t), the cyclic raw
gaps sum to t.  If their natural-floor quotients sum to n and t=n+delta,
then every floor-zero raw gap is paid entirely by the fractional remainder.
Hence the total width of all floor-zero local gaps is at most delta.

This is the local-coordinate analogue of the normalized projective
zero-gap-mass budget, with scale one.
-/

namespace JSP000404Research

theorem successiveDiffsFrom_sum_eq_getLastD_sub
    (a : ℝ) (xs : List ℝ) :
    (successiveDiffsFrom a xs).sum = xs.getLastD a - a := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp only [successiveDiffsFrom, List.sum_cons]
      rw [ih x, List.getLastD_cons]
      ring

theorem cyclicRealGaps_sum_eq_width
    (t a : ℝ) (xs : List ℝ) :
    (cyclicRealGaps t (a :: xs)).sum = t := by
  simp only [cyclicRealGaps, List.sum_append, List.sum_singleton]
  rw [successiveDiffsFrom_sum_eq_getLastD_sub]
  ring

theorem successiveDiffsFrom_nonneg_of_pairwise
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    ∀ g ∈ successiveDiffsFrom a xs, 0 ≤ g := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hax : a ≤ x := hpair.1 x (by simp)
      have htail : (x :: xs).Pairwise (· ≤ ·) := hpair.2
      intro g hg
      simp only [successiveDiffsFrom, List.mem_cons] at hg
      rcases hg with rfl | hg
      · linarith
      · exact ih x htail g hg

theorem cyclicRealGaps_nonneg_of_sorted
    {t a : ℝ} {xs : List ℝ}
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hallt : ∀ x ∈ a :: xs, x < t) :
    ∀ g ∈ cyclicRealGaps t (a :: xs), 0 ≤ g := by
  intro g hg
  simp only [cyclicRealGaps, List.mem_append, List.mem_singleton] at hg
  rcases hg with hinner | hwrap
  · exact successiveDiffsFrom_nonneg_of_pairwise
      a xs hsorted g hinner
  · subst g
    have hlastMem : xs.getLastD a ∈ a :: xs := by
      exact List.getLastD_mem_cons
    have hlastt : xs.getLastD a < t :=
      hallt _ hlastMem
    linarith

theorem floorMap_aligned_one
    (gs : List ℝ)
    (hg0 : ∀ g ∈ gs, 0 ≤ g) :
    QuotientGapAligned 1 (gs.map Nat.floor) gs := by
  unfold QuotientGapAligned
  induction gs with
  | nil =>
      exact List.Forall₂.nil
  | cons g gs ih =>
      have hg : 0 ≤ g := hg0 g (by simp)
      have htail : ∀ x ∈ gs, 0 ≤ x := by
        intro x hx
        exact hg0 x (by simp [hx])
      exact List.Forall₂.cons
        (by
          have hfloor : ((Nat.floor g : ℕ) : ℝ) ≤ g :=
            Nat.floor_le hg
          simpa using hfloor)
        (ih htail)

/-- Local raw zero-floor gaps consume at most delta of the normalized
direction-coordinate circumference. -/
theorem cyclic_floor_zero_mass_le_delta
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hallt : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hqsum :
      ((cyclicRealGaps t (a :: xs)).map Nat.floor).sum = n) :
    listZeroGapMass
        ((cyclicRealGaps t (a :: xs)).map Nat.floor)
        (cyclicRealGaps t (a :: xs))
      ≤ delta := by
  let gs := cyclicRealGaps t (a :: xs)
  let qs := gs.map Nat.floor
  have hg0 : ∀ g ∈ gs, 0 ≤ g := by
    intro g hg
    exact cyclicRealGaps_nonneg_of_sorted
      ha0 hsorted hallt g (by simpa [gs] using hg)
  have halign : QuotientGapAligned 1 qs gs :=
    floorMap_aligned_one gs hg0
  have hlen : qs.length = gs.length :=
    quotientGapAligned_length halign
  have hmass :=
    listZeroGapMass_scaled_le_remainder halign
  have hgsum : gs.sum = t := by
    simpa [gs] using cyclicRealGaps_sum_eq_width t a xs
  have hqsum' : qs.sum = n := by
    simpa [qs,gs] using hqsum
  rw [listRemainderMass_eq 1 qs gs hlen,
      hgsum, hqsum'] at hmass
  norm_num at hmass
  linarith [ht]

#print axioms successiveDiffsFrom_sum_eq_getLastD_sub
#print axioms cyclicRealGaps_sum_eq_width
#print axioms cyclic_floor_zero_mass_le_delta

end JSP000404Research
