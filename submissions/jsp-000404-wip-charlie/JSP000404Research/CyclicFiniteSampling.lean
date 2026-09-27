import JSP000404Research.TurnUnitPhaseInterval
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# Generic finite sampling on a periodic phase circle

For M>=2 sample the normalized phase circle at

  r*t/M,  r : Fin M.

If delta < t/M, every periodic arc of length delta contains at most one
sample.

Unlike the earlier eleven-phase lemma, the arc base is allowed to be any real
number.  This is essential for turn-unit slots, whose canonical starts include
an integer offset and need not lie in the fundamental interval [0,t).
-/

namespace JSP000404Research

def cyclicSamplePhase (t : ℝ) (M : ℕ) (r : Fin M) : ℝ :=
  (r.val : ℝ) * t / (M : ℝ)

theorem cyclicSamplePhase_nonneg
    {t : ℝ} {M : ℕ}
    (ht : 0 ≤ t)
    (hM : 1 ≤ M)
    (r : Fin M) :
    0 ≤ cyclicSamplePhase t M r := by
  unfold cyclicSamplePhase
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  positivity

theorem cyclicSamplePhase_lt_t
    {t : ℝ} {M : ℕ}
    (ht : 0 < t)
    (hM : 1 ≤ M)
    (r : Fin M) :
    cyclicSamplePhase t M r < t := by
  unfold cyclicSamplePhase
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hr : (r.val : ℝ) < M := by
    exact_mod_cast r.isLt
  apply (div_lt_iff₀ hMR).2
  nlinarith

theorem fin_val_abs_sub_bounds
    {M : ℕ}
    (hM : 1 ≤ M)
    {r s : Fin M}
    (hrs : r ≠ s) :
    1 ≤ |(r.val : ℝ) - (s.val : ℝ)| ∧
    |(r.val : ℝ) - (s.val : ℝ)| ≤ (M - 1 : ℕ) := by
  have hv : r.val ≠ s.val := by
    intro h
    exact hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have h1Nat : r.val + 1 ≤ s.val := by omega
    have h1Cast :
        (r.val : ℝ) + 1 ≤ (s.val : ℝ) := by
      exact_mod_cast h1Nat
    have hsBound : s.val ≤ M - 1 := by omega
    have hsBoundR : (s.val : ℝ) ≤ (M - 1 : ℕ) := by
      exact_mod_cast hsBound
    have hr0 : (0 : ℝ) ≤ r.val := by positivity
    rw [abs_of_nonpos]
    · constructor <;> linarith
    · exact_mod_cast hlt.le
  · have h1Nat : s.val + 1 ≤ r.val := by omega
    have h1Cast :
        (s.val : ℝ) + 1 ≤ (r.val : ℝ) := by
      exact_mod_cast h1Nat
    have hrBound : r.val ≤ M - 1 := by omega
    have hrBoundR : (r.val : ℝ) ≤ (M - 1 : ℕ) := by
      exact_mod_cast hrBound
    have hs0 : (0 : ℝ) ≤ s.val := by positivity
    rw [abs_of_nonneg]
    · constructor <;> linarith
    · exact_mod_cast hgt.le

theorem cyclicSamplePhase_abs_sub
    {t : ℝ} {M : ℕ}
    (ht : 0 < t)
    (hM : 1 ≤ M)
    (r s : Fin M) :
    |cyclicSamplePhase t M r -
        cyclicSamplePhase t M s|
      =
    |(r.val : ℝ) - (s.val : ℝ)| * t / (M : ℝ) := by
  unfold cyclicSamplePhase
  have htAbs : |t| = t := abs_of_pos ht
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [show
      (r.val : ℝ) * t / (M : ℝ) -
          (s.val : ℝ) * t / (M : ℝ) =
        (((r.val : ℝ) - (s.val : ℝ)) * t) /
          (M : ℝ) by ring,
      abs_div, abs_mul, htAbs,
      abs_of_pos hMR]
  ring

theorem cyclicSamplePhase_cyclic_separation
    {t delta : ℝ} {M : ℕ}
    (ht : 0 < t)
    (hM : 2 ≤ M)
    (hdelta : delta < t / (M : ℝ))
    {r s : Fin M}
    (hrs : r ≠ s) :
    delta <
        |cyclicSamplePhase t M r -
          cyclicSamplePhase t M s|
      ∧
    delta <
        t -
          |cyclicSamplePhase t M r -
            cyclicSamplePhase t M s| := by
  have hM1 : 1 ≤ M := by omega
  obtain ⟨hd1, hdTop⟩ :=
    fin_val_abs_sub_bounds hM1 hrs
  rw [cyclicSamplePhase_abs_sub ht hM1 r s]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have ht0 : 0 < t := ht
  have hlower :
      t / (M : ℝ) ≤
        |(r.val : ℝ) - (s.val : ℝ)| * t / (M : ℝ) := by
    apply (div_le_div_iff_of_pos_right hMR).2
    nlinarith
  have hMsubCast :
      ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hupper :
      |(r.val : ℝ) - (s.val : ℝ)| * t / (M : ℝ)
        ≤
      ((M : ℝ) - 1) * t / (M : ℝ) := by
    apply (div_le_div_iff_of_pos_right hMR).2
    rw [← hMsubCast]
    exact mul_le_mul_of_nonneg_right hdTop ht.le
  have hcomp :
      t / (M : ℝ) ≤
        t -
          |(r.val : ℝ) - (s.val : ℝ)| * t / (M : ℝ) := by
    have hid :
        t - ((M : ℝ) - 1) * t / (M : ℝ) =
          t / (M : ℝ) := by
      field_simp [ne_of_gt hMR]
      ring
    rw [← hid]
    linarith
  exact ⟨hdelta.trans_le hlower, hdelta.trans_le hcomp⟩

/-- The direct/wrap closeness conclusion does not require the periodic arc
base to be normalized into [0,t). -/
theorem two_points_same_cyclicDeltaArcAnyBase_close
    {t delta alpha x y : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdeltaT : delta < t)
    (hx0 : 0 ≤ x) (hxT : x < t)
    (hy0 : 0 ≤ y) (hyT : y < t)
    (hx : CyclicDeltaArcAtAnyBase t delta alpha x)
    (hy : CyclicDeltaArcAtAnyBase t delta alpha y) :
    |x - y| ≤ delta ∨
      t - |x - y| ≤ delta := by
  obtain ⟨kx, hxL, hxR⟩ := hx
  obtain ⟨ky, hyL, hyR⟩ := hy
  have hdiffUpper :
      ((kx - ky : ℤ) : ℝ) * t ≤ x - y + delta := by
    push_cast
    nlinarith
  have hdiffLower :
      x - y ≤ ((kx - ky : ℤ) : ℝ) * t + delta := by
    push_cast
    nlinarith
  have hkUpper : kx - ky ≤ 1 := by
    by_contra hnot
    have h2 : (2 : ℤ) ≤ kx - ky := by omega
    have h2R : (2 : ℝ) ≤ ((kx - ky : ℤ) : ℝ) := by
      exact_mod_cast h2
    have hxy : x - y < t := by linarith
    nlinarith
  have hkLower : (-1 : ℤ) ≤ kx - ky := by
    by_contra hnot
    have hm2 : kx - ky ≤ (-2 : ℤ) := by omega
    have hm2R : ((kx - ky : ℤ) : ℝ) ≤ (-2 : ℝ) := by
      exact_mod_cast hm2
    have hyx : y - x < t := by linarith
    nlinarith
  have hcases :
      kx - ky = -1 ∨ kx - ky = 0 ∨ kx - ky = 1 := by
    omega
  rcases hcases with hm1 | h0 | h1
  · right
    have hcast :
        ((kx - ky : ℤ) : ℝ) = (-1 : ℝ) := by
      exact_mod_cast hm1
    rw [hcast] at hdiffUpper hdiffLower
    have hyxPos : 0 ≤ y - x := by
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hyxPos)]
    nlinarith
  · left
    have hcast :
        ((kx - ky : ℤ) : ℝ) = 0 := by
      exact_mod_cast h0
    rw [hcast] at hdiffUpper hdiffLower
    rw [abs_le]
    constructor <;> linarith
  · right
    have hcast :
        ((kx - ky : ℤ) : ℝ) = 1 := by
      exact_mod_cast h1
    rw [hcast] at hdiffUpper hdiffLower
    have hxyPos : 0 ≤ x - y := by
      nlinarith
    rw [abs_of_nonneg hxyPos]
    nlinarith

theorem cyclicSamplePhase_injective_on_same_anyBaseArc
    {t delta alpha : ℝ} {M : ℕ}
    (ht : 0 < t)
    (hM : 2 ≤ M)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / (M : ℝ))
    {r s : Fin M}
    (hr :
      CyclicDeltaArcAtAnyBase t delta alpha
        (cyclicSamplePhase t M r))
    (hs :
      CyclicDeltaArcAtAnyBase t delta alpha
        (cyclicSamplePhase t M s)) :
    r = s := by
  by_contra hrs
  have hsep :=
    cyclicSamplePhase_cyclic_separation
      ht hM hdelta hrs
  have hdeltaT : delta < t := by
    have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
    have htM : t / (M : ℝ) < t := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < M)).2
      nlinarith
    exact hdelta.trans htM
  have hclose :=
    two_points_same_cyclicDeltaArcAnyBase_close
      ht hdelta0 hdeltaT
      (cyclicSamplePhase_nonneg ht.le (by omega : 1 ≤ M) r)
      (cyclicSamplePhase_lt_t ht (by omega : 1 ≤ M) r)
      (cyclicSamplePhase_nonneg ht.le (by omega : 1 ≤ M) s)
      (cyclicSamplePhase_lt_t ht (by omega : 1 ≤ M) s)
      hr hs
  rcases hclose with hdirect | hwrap
  · linarith
  · linarith

#print axioms cyclicSamplePhase_cyclic_separation
#print axioms two_points_same_cyclicDeltaArcAnyBase_close
#print axioms cyclicSamplePhase_injective_on_same_anyBaseArc

end JSP000404Research
