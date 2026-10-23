import JSP000404Research.SixPointNoCompensationPositiveGapBudget
import JSP000404Research.PositiveGapSeventeenPhase
import Mathlib.Tactic

/-!
# Fifteen-phase obstruction avoidance for uncompensated hard top deletions

Unlike the general sixteen-slot six-centre budget (requiring seventeen
samples and n>=8), the no-compensated-top-deletion original-geometry
profile has at most FOURTEEN actual positive quotient slots. Fifteen
equally spaced phase samples are pairwise circularly separated by more
than delta when n>=7 and delta<1/2. One period phase thus avoids every
q>=1 positive-gap bad interval. The genuinely global TRUE Boolean-hole
dyadic nonreuse payment remains open.
-/

namespace JSP000404Research

noncomputable def fifteenPhase (t : ℝ) (r : Fin 15) : ℝ :=
  (r.val : ℝ) * t / 15

theorem fifteenPhase_nonneg
    {t : ℝ} (ht : 0 ≤ t)
    (r : Fin 15) :
    0 ≤ fifteenPhase t r := by
  unfold fifteenPhase
  positivity

theorem fifteenPhase_lt_t
    {t : ℝ} (ht : 0 < t)
    (r : Fin 15) :
    fifteenPhase t r < t := by
  unfold fifteenPhase
  have hr : (r.val : ℝ) < 15 := by
    exact_mod_cast r.isLt
  nlinarith

/-- Distinct Fin 15 indices differ by between one and ten in absolute real
value. -/
theorem fin15_val_abs_sub_bounds
    {r s : Fin 15}
    (hrs : r ≠ s) :
    1 ≤ |(r.val : ℝ) - (s.val : ℝ)| ∧
    |(r.val : ℝ) - (s.val : ℝ)| ≤ 14 := by
  have hv : r.val ≠ s.val := by
    intro h
    exact hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have h1Nat : r.val + 1 ≤ s.val := by omega
    have h1Cast :
        (r.val : ℝ) + 1 ≤ (s.val : ℝ) := by
      exact_mod_cast h1Nat
    have hs10Nat : s.val ≤ 14 := by omega
    have hs10 : (s.val : ℝ) ≤ 14 := by
      exact_mod_cast hs10Nat
    have hr0 : (0 : ℝ) ≤ r.val := by positivity
    have h1 : (1 : ℝ) ≤ (s.val : ℝ) - (r.val : ℝ) := by
      linarith
    have h10 : (s.val : ℝ) - (r.val : ℝ) ≤ 14 := by
      linarith
    rw [abs_of_nonpos]
    · constructor <;> linarith
    · have hle : (r.val : ℝ) ≤ (s.val : ℝ) := by
        exact_mod_cast hlt.le
      linarith
  · have h1Nat : s.val + 1 ≤ r.val := by omega
    have h1Cast :
        (s.val : ℝ) + 1 ≤ (r.val : ℝ) := by
      exact_mod_cast h1Nat
    have hr10Nat : r.val ≤ 14 := by omega
    have hr10 : (r.val : ℝ) ≤ 14 := by
      exact_mod_cast hr10Nat
    have hs0 : (0 : ℝ) ≤ s.val := by positivity
    have h1 : (1 : ℝ) ≤ (r.val : ℝ) - (s.val : ℝ) := by
      linarith
    have h10 : (r.val : ℝ) - (s.val : ℝ) ≤ 14 := by
      linarith
    rw [abs_of_nonneg]
    · exact ⟨h1, h10⟩
    · have hle : (s.val : ℝ) ≤ (r.val : ℝ) := by
        exact_mod_cast hgt.le
      linarith

theorem fifteenPhase_abs_sub
    {t : ℝ} (ht : 0 < t)
    (r s : Fin 15) :
    |fifteenPhase t r - fifteenPhase t s| =
      |(r.val : ℝ) - (s.val : ℝ)| * t / 15 := by
  unfold fifteenPhase
  have htAbs : |t| = t := abs_of_pos ht
  rw [show
      (r.val : ℝ) * t / 15 -
          (s.val : ℝ) * t / 15 =
        (((r.val : ℝ) - (s.val : ℝ)) * t) / 15 by ring,
      abs_div, abs_mul, htAbs]
  norm_num <;> ring

/-- Any two distinct fifteen-sample phases are separated by more than delta in
both the direct and complementary circular directions whenever delta<t/15. -/
theorem fifteenPhase_cyclic_separation
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta : delta < t / 15)
    {r s : Fin 15}
    (hrs : r ≠ s) :
    delta < |fifteenPhase t r - fifteenPhase t s| ∧
    delta <
      t - |fifteenPhase t r - fifteenPhase t s| := by
  obtain ⟨hd1, hd10⟩ :=
    fin15_val_abs_sub_bounds hrs
  rw [fifteenPhase_abs_sub ht r s]
  have h11 : (0 : ℝ) < 15 := by norm_num
  have hlower :
      t / 15 ≤
        |(r.val : ℝ) - (s.val : ℝ)| * t / 15 := by
    apply (div_le_div_iff_of_pos_right h11).2
    nlinarith
  have hupper :
      |(r.val : ℝ) - (s.val : ℝ)| * t / 15
        ≤ 14 * t / 15 := by
    apply (div_le_div_iff_of_pos_right h11).2
    nlinarith
  constructor
  · exact hdelta.trans_le hlower
  · have hcomp :
        t / 15 ≤
          t - |(r.val : ℝ) - (s.val : ℝ)| * t / 15 := by
      nlinarith
    exact hdelta.trans_le hcomp

/-- Consequently one periodic delta-arc can contain at most one of the fifteen
equally spaced samples. -/
theorem fifteenPhase_injective_on_same_cyclicDeltaArc
    {t delta alpha : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / 15)
    (halpha0 : 0 ≤ alpha)
    (halphaT : alpha < t)
    {r s : Fin 15}
    (hr : CyclicDeltaArcAt t delta alpha (fifteenPhase t r))
    (hs : CyclicDeltaArcAt t delta alpha (fifteenPhase t s)) :
    r = s := by
  by_contra hrs
  have hsep :=
    fifteenPhase_cyclic_separation ht hdelta hrs
  have hdeltaT : delta < t := by
    have ht11 : t / 15 < t := by
      nlinarith
    exact hdelta.trans ht11
  have hclose :=
    two_points_same_cyclicDeltaArc_close
      ht hdelta0 hdeltaT halpha0 halphaT
      (fifteenPhase_nonneg ht.le r)
      (fifteenPhase_lt_t ht r)
      (fifteenPhase_nonneg ht.le s)
      (fifteenPhase_lt_t ht s)
      hr hs
  rcases hclose with hdirect | hwrap
  · linarith
  · linarith

/-- Assigning a positive quotient gap slot to every fifteen-sample phase forces an
injective map into the global positive gap-slot type. -/
theorem positive_gap_slot_assignment_on_fifteenPhase_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / 15)
    (slot : Fin 15 → GlobalPositiveGapSlot C t)
    (hbad :
      ∀ r : Fin 15,
        GlobalCyclicPositiveGapBadAt
          C t delta (slot r) (fifteenPhase t r)) :
    Function.Injective slot := by
  intro r s hrsSlot
  have hrArc :=
    cyclicPositiveGapBadAt_implies_deltaArc
      C ht.le (hbad r)
  have hsArc :
      CyclicDeltaArcAt t delta
        (globalPositiveGapStart C t (slot r))
        (fifteenPhase t s) := by
    have h :=
      cyclicPositiveGapBadAt_implies_deltaArc
        C ht.le (hbad s)
    simpa [hrsSlot] using h
  exact fifteenPhase_injective_on_same_cyclicDeltaArc
    ht hdelta0 hdelta
    (globalPositiveGapStart_nonneg C ht.le (slot r))
    (globalPositiveGapStart_lt_t C ht (slot r))
    hrArc hsArc


/-- A true uncompensated top-deletion hard profile has at most fourteen
positive canonical quotient slots. Fifteen distinct circular phases are too
many to all be obstructed when 0<=delta<1/2 and n>=7. -/
theorem six_point_hard_top_exists_unblocked_positiveGap_fifteenPhase
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn7 : 7 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ r : Fin 15,
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt
          C t delta u (fifteenPhase t r) := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn7
  have h15delta : 15 * delta < t := by
    rw [ht]
    linarith
  have hdelta : delta < t / 15 := by
    nlinarith
  by_contra hnone
  push_neg at hnone
  let slot : Fin 15 → GlobalPositiveGapSlot C t :=
    fun r => Classical.choose (hnone r)
  have hbad :
      ∀ r : Fin 15,
        GlobalCyclicPositiveGapBadAt
          C t delta (slot r) (fifteenPhase t r) := by
    intro r
    exact Classical.choose_spec (hnone r)
  have hinj : Function.Injective slot :=
    positive_gap_slot_assignment_on_fifteenPhase_injective
      C htpos hdelta0 hdelta slot hbad
  have hcardInj :
      15 ≤ Fintype.card (GlobalPositiveGapSlot C t) := by
    have h := Fintype.card_le_of_injective slot hinj
    simpa using h
  have hslot14 :
      Fintype.card (GlobalPositiveGapSlot C t) ≤ 14 :=
    six_point_no_compensation_positive_gap_card_le_fourteen
      hp hcap C hcard (by omega : 5 ≤ n)
      hdelta0 hdeltaHalf ht hlam top hTop hMin hNoTop
  omega

/-- Nonvacuous in-period safe phase for all q>=1 under the actual no-top-
compensation hard branch and n>=7. -/
theorem six_point_hard_top_exists_period_phase_without_positiveGap_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn7 : 7 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u x := by
  obtain ⟨r, hr⟩ :=
    six_point_hard_top_exists_unblocked_positiveGap_fifteenPhase
      hp hcap C hcard hn7 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hNoTop
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  exact ⟨fifteenPhase t r, fifteenPhase_nonneg htpos.le r,
    fifteenPhase_lt_t htpos r, hr⟩

#print axioms six_point_hard_top_exists_unblocked_positiveGap_fifteenPhase
#print axioms six_point_hard_top_exists_period_phase_without_positiveGap_bad

end JSP000404Research
