import JSP000404Research.SixPointThirteenSlotAlternative
import JSP000404Research.CyclicFiniteSampling
import Mathlib.Tactic

/-!
# Sharp 14-sample escape for thirteen positive gap slots

This is a genuinely conditional improvement in the original six-point
no-compensated-top branch. Under the support-one/support-two alternative,
there are at most 13 positive quotient-gap coordinates; 14 equally spaced
period phases suffice when 14*delta<t, equivalently 13*delta<n.
In the other hard-branch alternative there remain two actual non-gaining
support-two centres. No global Boolean-hole/dyadic payment is inferred.
-/

namespace JSP000404Research

/-- A finite set of fewer than M genuine positive gap arcs cannot cover
M equally spaced phases provided each periodic arc has width < t/M. -/
theorem positive_gap_safe_sample_of_card_lt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} (M : ℕ)
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hM : 2 ≤ M)
    (hsep : delta < t / (M : ℝ))
    (hcard : Fintype.card (GlobalPositiveGapSlot C t) < M) :
    ∃ r : Fin M,
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u
          (cyclicSamplePhase t M r) := by
  classical
  by_contra hnone
  push_neg at hnone
  let slot : Fin M → GlobalPositiveGapSlot C t :=
    fun r => Classical.choose (hnone r)
  have hbad :
      ∀ r : Fin M,
        GlobalCyclicPositiveGapBadAt C t delta
          (slot r) (cyclicSamplePhase t M r) := by
    intro r
    exact Classical.choose_spec (hnone r)
  have hinj : Function.Injective slot := by
    intro r s hrs
    have hrArc : CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t (slot r))
        (cyclicSamplePhase t M r) := by
      simpa only [CyclicDeltaArcAtAnyBase, CyclicDeltaArcAt] using
        (cyclicPositiveGapBadAt_implies_deltaArc C ht.le (hbad r))
    have hsArc : CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t (slot r))
        (cyclicSamplePhase t M s) := by
      have h := cyclicPositiveGapBadAt_implies_deltaArc C ht.le (hbad s)
      simpa only [hrs, CyclicDeltaArcAt, CyclicDeltaArcAtAnyBase] using h
    exact cyclicSamplePhase_injective_on_same_anyBaseArc
      ht hM hdelta0 hsep hrArc hsArc
  have hcount : M ≤ Fintype.card (GlobalPositiveGapSlot C t) := by
    simpa using (Fintype.card_le_of_injective slot hinj)
  omega

/-- With a support-one and support-two minimum, a six-centre uncompensated
hard profile has an in-period phase safe against every q>=1 positive-gap
obstruction under the sharper necessary sampling threshold 13*delta<n. -/
theorem six_point_support_one_two_safe_fourteenPhase_of_threshold
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hthreshold : 13 * delta < (n : ℝ))
    (top a b : V)
    (hat : a ≠ top) (hbt : b ≠ top) (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (ha : positiveSupport (centreQuotient (C a) t) = 1)
    (hb : positiveSupport (centreQuotient (C b) t) = 2) :
    ∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u x := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hsep : delta < t / 14 := by
    rw [ht]
    linarith
  have hslots :
      Fintype.card (GlobalPositiveGapSlot C t) < 14 := by
    have hcard13 :=
      six_point_positive_gap_card_le_thirteen_of_support_one_two
        C hcard hn5 hdelta0 hdeltaHalf ht top a b
        hat hbt hab hTop hMin ha hb
    omega
  obtain ⟨r, hr⟩ :=
    positive_gap_safe_sample_of_card_lt C 14 htpos hdelta0
      (by omega : 2 ≤ 14) hsep hslots
  exact ⟨cyclicSamplePhase t 14 r,
    cyclicSamplePhase_nonneg htpos.le (by omega : 1 ≤ 14) r,
    cyclicSamplePhase_lt_t htpos (by omega : 1 ≤ 14) r, hr⟩

/-- Exact six-point no-compensation split after the improved slot accounting:
either two distinct non-gaining support-two minima remain, or the 14-phase
sampling obstruction is avoided. -/
theorem six_point_hard_top_two_support_two_or_safe_fourteenPhase
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hthreshold : 13 * delta < (n : ℝ))
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      a ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      b ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2) ∨
    (∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u x) := by
  rcases six_point_hard_top_thirteen_slots_or_two_support_two
    hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
    top hTop hMin hNoTop with h13 | htwo
  · right
    have htpos : 0 < t :=
      sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
    have hsep : delta < t / 14 := by
      rw [ht]
      linarith
    obtain ⟨r, hr⟩ :=
      positive_gap_safe_sample_of_card_lt C 14 htpos hdelta0
        (by omega : 2 ≤ 14) hsep (by omega)
    exact ⟨cyclicSamplePhase t 14 r,
      cyclicSamplePhase_nonneg htpos.le (by omega : 1 ≤ 14) r,
      cyclicSamplePhase_lt_t htpos (by omega : 1 ≤ 14) r, hr⟩
  · exact Or.inl htwo

#print axioms positive_gap_safe_sample_of_card_lt
#print axioms six_point_support_one_two_safe_fourteenPhase_of_threshold
#print axioms six_point_hard_top_two_support_two_or_safe_fourteenPhase

end JSP000404Research
