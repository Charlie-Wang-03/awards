import JSP000404Research.TransitionGapAlignment
import Mathlib.Tactic

/-!
# Zero-gap mass for aligned quotient/gap lists

This is the list-valued counterpart of GapRemainder.zeroGapMass.

For aligned quotient/gap lists define the total fractional remainder

  sum_j (t*g_j - q_j)

and the total mass of quotient-zero gaps.  Alignment q_j <= t*g_j gives the
pointwise inequality

  t * zeroGapMass <= total remainder.

If gaps sum to one, quotients sum to n, and t=n+delta, the total remainder is
exactly delta.  Hence all zero-quotient gaps together have scaled width at
most delta.

The proof stays entirely in List.Forall₂, so repeated quotient/gap values are
preserved rather than deduplicated.
-/

namespace JSP000404Research

def listZeroGapMass : List ℕ → List ℝ → ℝ
  | [], [] => 0
  | q :: qs, g :: gs =>
      (if q = 0 then g else 0) + listZeroGapMass qs gs
  | _, _ => 0

def listRemainderMass (t : ℝ) : List ℕ → List ℝ → ℝ
  | [], [] => 0
  | q :: qs, g :: gs =>
      (t * g - (q : ℝ)) + listRemainderMass t qs gs
  | _, _ => 0

theorem listRemainderMass_eq
    (t : ℝ) (qs : List ℕ) (gs : List ℝ)
    (hlen : qs.length = gs.length) :
    listRemainderMass t qs gs =
      t * gs.sum - (qs.sum : ℝ) := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [listRemainderMass]
  | cons q qs ih =>
      cases gs with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp at hlen
          simp [listRemainderMass, ih gs hlen]
          ring

theorem listZeroGapMass_scaled_le_remainder
    {t : ℝ} {qs : List ℕ} {gs : List ℝ}
    (halign : QuotientGapAligned t qs gs) :
    t * listZeroGapMass qs gs ≤
      listRemainderMass t qs gs := by
  induction halign with
  | nil =>
      simp [listZeroGapMass, listRemainderMass]
  | @cons q g qs gs hqg halign ih =>
      by_cases hq0 : q = 0
      · subst q
        simp [listZeroGapMass, listRemainderMass]
        linarith
      · have hrem : 0 ≤ t * g - (q : ℝ) := by
          linarith
        simp [listZeroGapMass, listRemainderMass, hq0]
        linarith

theorem listZeroGapMass_scaled_le_delta
    (qs : List ℕ) (gs : List ℝ)
    {n : ℕ} {delta t : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hgapsum : gs.sum = 1)
    (hqsum : qs.sum = n)
    (halign : QuotientGapAligned t qs gs) :
    t * listZeroGapMass qs gs ≤ delta := by
  have hlen : qs.length = gs.length :=
    List.Forall₂.length_eq halign
  have hrem :=
    listZeroGapMass_scaled_le_remainder halign
  rw [listRemainderMass_eq t qs gs hlen,
      hgapsum, hqsum, ht] at hrem
  norm_num at hrem
  exact hrem

theorem listZeroGapMass_le_delta_div
    (qs : List ℕ) (gs : List ℝ)
    {n : ℕ} {delta t : ℝ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hgapsum : gs.sum = 1)
    (hqsum : qs.sum = n)
    (halign : QuotientGapAligned t qs gs) :
    listZeroGapMass qs gs ≤ delta / t := by
  rw [le_div_iff₀ htpos]
  exact listZeroGapMass_scaled_le_delta
    qs gs ht hgapsum hqsum halign

/-- If all quotients in a list are zero, listZeroGapMass is just the gap sum. -/
theorem listZeroGapMass_eq_gap_sum_of_all_zero
    (qs : List ℕ) (gs : List ℝ)
    (hlen : qs.length = gs.length)
    (hzero : ∀ q ∈ qs, q = 0) :
    listZeroGapMass qs gs = gs.sum := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [listZeroGapMass] at hlen ⊢
  | cons q qs ih =>
      cases gs with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp at hlen
          have hq0 : q = 0 := hzero q (by simp)
          have htail : ∀ x ∈ qs, x = 0 := by
            intro x hx
            exact hzero x (by simp [hx])
          subst q
          simp [listZeroGapMass, ih gs hlen htail]


/-- Nonnegativity of zero-gap mass when the aligned gap list is nonnegative. -/
theorem listZeroGapMass_nonneg
    {qs : List ℕ} {gs : List ℝ}
    (hlen : qs.length = gs.length)
    (hgs : ∀ g ∈ gs, 0 ≤ g) :
    0 ≤ listZeroGapMass qs gs := by
  induction qs generalizing gs with
  | nil =>
      cases gs <;> simp [listZeroGapMass] at hlen ⊢
  | cons q qs ih =>
      cases gs with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp at hlen
          have hg0 : 0 ≤ g := hgs g (by simp)
          have htail : ∀ x ∈ gs, 0 ≤ x := by
            intro x hx
            exact hgs x (by simp [hx])
          have ih' := ih gs hlen htail
          by_cases hq : q = 0 <;>
            simp [listZeroGapMass, hq, hg0, ih']

/-- A displayed quotient-zero gap is bounded by the total zero-gap mass. -/
theorem displayed_zero_gap_le_listZeroGapMass
    (pre post : List ℕ)
    (gpre gpost : List ℝ)
    (ge : ℝ)
    (hpre : pre.length = gpre.length)
    (hpost : post.length = gpost.length)
    (hgap0 : ∀ g ∈ gpre ++ ge :: gpost, 0 ≤ g) :
    ge ≤
      listZeroGapMass
        (pre ++ 0 :: post)
        (gpre ++ ge :: gpost) := by
  induction pre generalizing gpre with
  | nil =>
      have hgpre : gpre = [] := List.length_eq_zero.mp (by simpa using hpre.symm)
      subst gpre
      have hge0 : 0 ≤ ge := hgap0 ge (by simp)
      have htail0 : ∀ g ∈ gpost, 0 ≤ g := by
        intro g hg
        exact hgap0 g (by simp [hg])
      have htailMass :
          0 ≤ listZeroGapMass post gpost :=
        listZeroGapMass_nonneg hpost htail0
      simp [listZeroGapMass]
      linarith
  | cons q pre ih =>
      cases gpre with
      | nil =>
          simp at hpre
      | cons g gpre =>
          simp at hpre
          have hg0 : 0 ≤ g := hgap0 g (by simp)
          have hrest0 :
              ∀ x ∈ gpre ++ ge :: gpost, 0 ≤ x := by
            intro x hx
            exact hgap0 x (by simp [hx])
          have ih' :=
            ih gpre hpre hpost hrest0
          by_cases hq : q = 0 <;>
            simp [listZeroGapMass, hq, hg0] <;>
            linarith

/-- Localized form of the global delta remainder budget. -/
theorem displayed_zero_gap_scaled_le_delta
    (pre post : List ℕ)
    (gpre gpost : List ℝ)
    (ge : ℝ)
    {n : ℕ} {delta t : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hpre : pre.length = gpre.length)
    (hpost : post.length = gpost.length)
    (hgap0 : ∀ g ∈ gpre ++ ge :: gpost, 0 ≤ g)
    (hgapsum : (gpre ++ ge :: gpost).sum = 1)
    (hqsum : (pre ++ 0 :: post).sum = n)
    (halign :
      QuotientGapAligned t
        (pre ++ 0 :: post)
        (gpre ++ ge :: gpost))
    (ht0 : 0 ≤ t) :
    t * ge ≤ delta := by
  have hsingle :=
    displayed_zero_gap_le_listZeroGapMass
      pre post gpre gpost ge hpre hpost hgap0
  have hmass :=
    listZeroGapMass_scaled_le_delta
      (pre ++ 0 :: post)
      (gpre ++ ge :: gpost)
      ht hgapsum hqsum halign
  have hscaled :=
    mul_le_mul_of_nonneg_left hsingle ht0
  exact hscaled.trans hmass

#print axioms listRemainderMass_eq
#print axioms displayed_zero_gap_scaled_le_delta
#print axioms listZeroGapMass_scaled_le_remainder
#print axioms listZeroGapMass_scaled_le_delta
#print axioms listZeroGapMass_le_delta_div

end JSP000404Research
