import JSP000404Research.PositiveGapPhaseInterval
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# Seventeen-sample avoidance for ALL positive quotient gaps (n >= 8)

Six original centres in the top-(n-1)/five-(n-3) profile admit at most
16 canonical positive quotient coordinates, including q>=2 saturation
gaps. If n>=8, 17*delta < n+delta = t for delta<1/2, so seventeen
equally spaced period samples are pairwise separated by more than delta
around the projective circle. Any genuine positive-gap bad interval lies
inside the corresponding periodic delta-arc, and thus can hit at most
one sample. Pigeonhole gives an original-geometry safe phase for all q>=1.

This does NOT show that global Boolean-hole/dyadic payment failure is
captured by these gap intervals or settle the prize conjecture.
-/

namespace JSP000404Research

noncomputable def seventeenPhase (t : ℝ) (r : Fin 17) : ℝ :=
  (r.val : ℝ) * t / 17

theorem seventeenPhase_nonneg
    {t : ℝ} (ht : 0 ≤ t)
    (r : Fin 17) :
    0 ≤ seventeenPhase t r := by
  unfold seventeenPhase
  positivity

theorem seventeenPhase_lt_t
    {t : ℝ} (ht : 0 < t)
    (r : Fin 17) :
    seventeenPhase t r < t := by
  unfold seventeenPhase
  have hr : (r.val : ℝ) < 17 := by
    exact_mod_cast r.isLt
  nlinarith

/-- Distinct Fin 17 indices differ by between one and ten in absolute real
value. -/
theorem fin17_val_abs_sub_bounds
    {r s : Fin 17}
    (hrs : r ≠ s) :
    1 ≤ |(r.val : ℝ) - (s.val : ℝ)| ∧
    |(r.val : ℝ) - (s.val : ℝ)| ≤ 16 := by
  have hv : r.val ≠ s.val := by
    intro h
    exact hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have h1Nat : r.val + 1 ≤ s.val := by omega
    have h1Cast :
        (r.val : ℝ) + 1 ≤ (s.val : ℝ) := by
      exact_mod_cast h1Nat
    have hs10Nat : s.val ≤ 16 := by omega
    have hs10 : (s.val : ℝ) ≤ 16 := by
      exact_mod_cast hs10Nat
    have hr0 : (0 : ℝ) ≤ r.val := by positivity
    have h1 : (1 : ℝ) ≤ (s.val : ℝ) - (r.val : ℝ) := by
      linarith
    have h10 : (s.val : ℝ) - (r.val : ℝ) ≤ 16 := by
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
    have hr10Nat : r.val ≤ 16 := by omega
    have hr10 : (r.val : ℝ) ≤ 16 := by
      exact_mod_cast hr10Nat
    have hs0 : (0 : ℝ) ≤ s.val := by positivity
    have h1 : (1 : ℝ) ≤ (r.val : ℝ) - (s.val : ℝ) := by
      linarith
    have h10 : (r.val : ℝ) - (s.val : ℝ) ≤ 16 := by
      linarith
    rw [abs_of_nonneg]
    · exact ⟨h1, h10⟩
    · have hle : (s.val : ℝ) ≤ (r.val : ℝ) := by
        exact_mod_cast hgt.le
      linarith

theorem seventeenPhase_abs_sub
    {t : ℝ} (ht : 0 < t)
    (r s : Fin 17) :
    |seventeenPhase t r - seventeenPhase t s| =
      |(r.val : ℝ) - (s.val : ℝ)| * t / 17 := by
  unfold seventeenPhase
  have htAbs : |t| = t := abs_of_pos ht
  rw [show
      (r.val : ℝ) * t / 17 -
          (s.val : ℝ) * t / 17 =
        (((r.val : ℝ) - (s.val : ℝ)) * t) / 17 by ring,
      abs_div, abs_mul, htAbs]
  norm_num <;> ring

/-- Any two distinct seventeen-sample phases are separated by more than delta in
both the direct and complementary circular directions whenever delta<t/17. -/
theorem seventeenPhase_cyclic_separation
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta : delta < t / 17)
    {r s : Fin 17}
    (hrs : r ≠ s) :
    delta < |seventeenPhase t r - seventeenPhase t s| ∧
    delta <
      t - |seventeenPhase t r - seventeenPhase t s| := by
  obtain ⟨hd1, hd10⟩ :=
    fin17_val_abs_sub_bounds hrs
  rw [seventeenPhase_abs_sub ht r s]
  have h11 : (0 : ℝ) < 17 := by norm_num
  have hlower :
      t / 17 ≤
        |(r.val : ℝ) - (s.val : ℝ)| * t / 17 := by
    apply (div_le_div_iff_of_pos_right h11).2
    nlinarith
  have hupper :
      |(r.val : ℝ) - (s.val : ℝ)| * t / 17
        ≤ 16 * t / 17 := by
    apply (div_le_div_iff_of_pos_right h11).2
    nlinarith
  constructor
  · exact hdelta.trans_le hlower
  · have hcomp :
        t / 17 ≤
          t - |(r.val : ℝ) - (s.val : ℝ)| * t / 17 := by
      nlinarith
    exact hdelta.trans_le hcomp

/-- Consequently one periodic delta-arc can contain at most one of the seventeen
equally spaced samples. -/
theorem seventeenPhase_injective_on_same_cyclicDeltaArc
    {t delta alpha : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / 17)
    (halpha0 : 0 ≤ alpha)
    (halphaT : alpha < t)
    {r s : Fin 17}
    (hr : CyclicDeltaArcAt t delta alpha (seventeenPhase t r))
    (hs : CyclicDeltaArcAt t delta alpha (seventeenPhase t s)) :
    r = s := by
  by_contra hrs
  have hsep :=
    seventeenPhase_cyclic_separation ht hdelta hrs
  have hdeltaT : delta < t := by
    have ht11 : t / 17 < t := by
      nlinarith
    exact hdelta.trans ht11
  have hclose :=
    two_points_same_cyclicDeltaArc_close
      ht hdelta0 hdeltaT halpha0 halphaT
      (seventeenPhase_nonneg ht.le r)
      (seventeenPhase_lt_t ht r)
      (seventeenPhase_nonneg ht.le s)
      (seventeenPhase_lt_t ht s)
      hr hs
  rcases hclose with hdirect | hwrap
  · linarith
  · linarith

/-- Assigning a positive quotient gap slot to every seventeen-sample phase forces an
injective map into the global positive gap-slot type. -/
theorem positive_gap_slot_assignment_on_seventeenPhase_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / 17)
    (slot : Fin 17 → GlobalPositiveGapSlot C t)
    (hbad :
      ∀ r : Fin 17,
        GlobalCyclicPositiveGapBadAt
          C t delta (slot r) (seventeenPhase t r)) :
    Function.Injective slot := by
  intro r s hrsSlot
  have hrArc :=
    cyclicPositiveGapBadAt_implies_deltaArc
      C ht.le (hbad r)
  have hsArc :
      CyclicDeltaArcAt t delta
        (globalPositiveGapStart C t (slot r))
        (seventeenPhase t s) := by
    have h :=
      cyclicPositiveGapBadAt_implies_deltaArc
        C ht.le (hbad s)
    simpa [hrsSlot] using h
  exact seventeenPhase_injective_on_same_cyclicDeltaArc
    ht hdelta0 hdelta
    (globalPositiveGapStart_nonneg C ht.le (slot r))
    (globalPositiveGapStart_lt_t C ht (slot r))
    hrArc hsArc

/-- A sixteen-slot family cannot obstruct all seventeen equally spaced
physical phases. This holds for arbitrary positive quotient (q>=1), not merely
q=1 unit gaps, whenever n>=8 and delta<1/2. -/
theorem six_point_exists_unblocked_positiveGap_seventeenPhase
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn8 : 8 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3) :
    ∃ r : Fin 17,
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt
          C t delta u (seventeenPhase t r) := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
  have h17delta : 17 * delta < t := by
    rw [ht]
    linarith
  have hdelta : delta < t / 17 := by
    nlinarith
  by_contra hnone
  push_neg at hnone
  let slot : Fin 17 → GlobalPositiveGapSlot C t :=
    fun r => Classical.choose (hnone r)
  have hbad :
      ∀ r : Fin 17,
        GlobalCyclicPositiveGapBadAt
          C t delta (slot r) (seventeenPhase t r) := by
    intro r
    exact Classical.choose_spec (hnone r)
  have hinj : Function.Injective slot :=
    positive_gap_slot_assignment_on_seventeenPhase_injective
      C htpos hdelta0 hdelta slot hbad
  have hcardInj :
      17 ≤ Fintype.card (GlobalPositiveGapSlot C t) := by
    have h := Fintype.card_le_of_injective slot hinj
    simpa using h
  have hslot16 :
      Fintype.card (GlobalPositiveGapSlot C t) ≤ 16 :=
    six_point_globalPositiveGapSlot_card_le_sixteen
      C (by omega : 4 ≤ n) hdelta0
      (by linarith : delta < 1) ht
      hcard top hTop hMin
  omega

/-- Nonvacuous period statement: some x in [0,t) avoids every positive-gap
bad phase for this six-centre profile. -/
theorem six_point_exists_period_phase_without_positiveGap_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn8 : 8 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3) :
    ∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u x := by
  obtain ⟨r, hr⟩ :=
    six_point_exists_unblocked_positiveGap_seventeenPhase
      C hn8 hdelta0 hdeltaHalf ht hcard top hTop hMin
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  exact ⟨seventeenPhase t r,
    seventeenPhase_nonneg htpos.le r,
    seventeenPhase_lt_t htpos r, hr⟩

#print axioms six_point_exists_unblocked_positiveGap_seventeenPhase
#print axioms six_point_exists_period_phase_without_positiveGap_bad

end JSP000404Research
