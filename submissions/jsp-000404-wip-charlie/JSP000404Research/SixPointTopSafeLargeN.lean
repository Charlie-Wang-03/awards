import JSP000404Research.CyclicFiniteSampling
import JSP000404Research.SixPointTopTurnSlots
import JSP000404Research.SixPointUnitGapSlots
import JSP000404Research.ElevenPhaseCut
import JSP000404Research.CutSaturationGlobalTurnSlot
import Mathlib.Tactic

/-!
# Simultaneously avoiding critical unit slots and top saturation slots

For M equally spaced samples of the normalized phase circle, with

  delta < t/M,

every periodic delta arc contains at most one sample.

At the six-point top centre there are exactly n whole-unit turn slots, while
the full configuration has at most ten q=1 critical unit slots.  Therefore,
if M > n+10, the M samples cannot all be covered by the union of

* top-centred saturation turn slots, and
* global critical q=1 slots.

Choosing M=2n+1 gives M>n+10 for n>=10.  Since delta<1/2 implies

  delta < (n+delta)/(2n+1),

this produces a sampled projective cut that is simultaneously critical-
uncovered and top-saturation-safe for every n>=10.
-/

namespace JSP000404Research

theorem cyclicCriticalUnitBadAt_implies_anyBaseArc
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    {u : GlobalUnitGapSlot C t}
    {x : ℝ}
    (hbad :
      GlobalCyclicCriticalUnitBadAt C t delta u x) :
    CyclicDeltaArcAtAnyBase t delta
      (globalUnitGapStart C t u) x := by
  rcases cyclicCriticalUnitBadAt_implies_deltaArc C hbad with
    ⟨k, hkL, hkR⟩
  exact ⟨k, hkL, hkR⟩

/-- If every sample is covered either by a top turn-unit bad arc or by a
critical q=1 bad arc, the sample set injects into the disjoint union of those
two finite slot types. -/
theorem topCritical_slot_assignment_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (top : V)
    {t delta : ℝ} {M : ℕ}
    (ht : 0 < t)
    (hM : 2 ≤ M)
    (hdelta0 : 0 ≤ delta)
    (hdelta :
      delta < t / (M : ℝ))
    (slot :
      Fin M →
        Sum (CentreTurnUnitSlot (C top) t)
          (GlobalUnitGapSlot C t))
    (hbad :
      ∀ r : Fin M,
        match slot r with
        | Sum.inl u =>
            CentreCyclicTurnUnitBadAt
              (C top) t delta u
              (cyclicSamplePhase t M r)
        | Sum.inr u =>
            GlobalCyclicCriticalUnitBadAt
              C t delta u
              (cyclicSamplePhase t M r)) :
    Function.Injective slot := by
  intro r s hrs
  cases hrSlot : slot r with
  | inl ur =>
      cases hsSlot : slot s with
      | inl us =>
          have hus : ur = us := by
            simpa [hrSlot, hsSlot] using hrs
          subst us
          have hrBad :
              CentreCyclicTurnUnitBadAt
                (C top) t delta ur
                (cyclicSamplePhase t M r) := by
            simpa [hrSlot] using hbad r
          have hsBad :
              CentreCyclicTurnUnitBadAt
                (C top) t delta ur
                (cyclicSamplePhase t M s) := by
            simpa [hsSlot] using hbad s
          have hrArc :=
            cyclicTurnUnitBadAt_implies_deltaArc
              (C top) ht.le hrBad
          have hsArc :=
            cyclicTurnUnitBadAt_implies_deltaArc
              (C top) ht.le hsBad
          exact cyclicSamplePhase_injective_on_same_anyBaseArc
            ht hM hdelta0 hdelta hrArc hsArc
      | inr us =>
          simp [hrSlot, hsSlot] at hrs
  | inr ur =>
      cases hsSlot : slot s with
      | inl us =>
          simp [hrSlot, hsSlot] at hrs
      | inr us =>
          have hus : ur = us := by
            simpa [hrSlot, hsSlot] using hrs
          subst us
          have hrBad :
              GlobalCyclicCriticalUnitBadAt
                C t delta ur
                (cyclicSamplePhase t M r) := by
            simpa [hrSlot] using hbad r
          have hsBad :
              GlobalCyclicCriticalUnitBadAt
                C t delta ur
                (cyclicSamplePhase t M s) := by
            simpa [hsSlot] using hbad s
          have hrArc :=
            cyclicCriticalUnitBadAt_implies_anyBaseArc
              C hrBad
          have hsArc :=
            cyclicCriticalUnitBadAt_implies_anyBaseArc
              C hsBad
          exact cyclicSamplePhase_injective_on_same_anyBaseArc
            ht hM hdelta0 hdelta hrArc hsArc

/-- Abstract finite-sampling outlet for the union of top saturation slots and
critical unit slots. -/
theorem exists_sample_outside_topTurn_and_critical
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (top : V)
    {t delta : ℝ} {M : ℕ}
    (ht : 0 < t)
    (hM : 2 ≤ M)
    (hdelta0 : 0 ≤ delta)
    (hdelta :
      delta < t / (M : ℝ))
    (hcard :
      Fintype.card (CentreTurnUnitSlot (C top) t) +
        Fintype.card (GlobalUnitGapSlot C t) < M) :
    ∃ r : Fin M,
      (∀ u : CentreTurnUnitSlot (C top) t,
        ¬ CentreCyclicTurnUnitBadAt
            (C top) t delta u
            (cyclicSamplePhase t M r))
      ∧
      (∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u
            (cyclicSamplePhase t M r)) := by
  by_contra hnone
  push_neg at hnone

  have hcover :
      ∀ r : Fin M,
        (∃ u : CentreTurnUnitSlot (C top) t,
          CentreCyclicTurnUnitBadAt
            (C top) t delta u
            (cyclicSamplePhase t M r))
        ∨
        (∃ u : GlobalUnitGapSlot C t,
          GlobalCyclicCriticalUnitBadAt
            C t delta u
            (cyclicSamplePhase t M r)) := by
    intro r
    by_cases htop :
        ∃ u : CentreTurnUnitSlot (C top) t,
          CentreCyclicTurnUnitBadAt
            (C top) t delta u
            (cyclicSamplePhase t M r)
    · exact Or.inl htop
    · right
      have hcritNotAll :=
        hnone r
          (by
            intro u hu
            exact htop ⟨u, hu⟩)
      push_neg at hcritNotAll
      exact hcritNotAll

  let slot :
      Fin M →
        Sum (CentreTurnUnitSlot (C top) t)
          (GlobalUnitGapSlot C t) :=
    fun r =>
      if h :
          ∃ u : CentreTurnUnitSlot (C top) t,
            CentreCyclicTurnUnitBadAt
              (C top) t delta u
              (cyclicSamplePhase t M r)
      then Sum.inl (Classical.choose h)
      else Sum.inr
        (Classical.choose
          (Or.resolve_left (hcover r) h))

  have hbad :
      ∀ r : Fin M,
        match slot r with
        | Sum.inl u =>
            CentreCyclicTurnUnitBadAt
              (C top) t delta u
              (cyclicSamplePhase t M r)
        | Sum.inr u =>
            GlobalCyclicCriticalUnitBadAt
              C t delta u
              (cyclicSamplePhase t M r) := by
    intro r
    unfold slot
    split_ifs with h
    · simpa using Classical.choose_spec h
    · simpa using
        Classical.choose_spec
          (Or.resolve_left (hcover r) h)

  have hinj :
      Function.Injective slot :=
    topCritical_slot_assignment_injective
      C top ht hM hdelta0 hdelta slot hbad

  have hcardInj :
      M ≤
        Fintype.card
          (Sum (CentreTurnUnitSlot (C top) t)
            (GlobalUnitGapSlot C t)) := by
    simpa using Fintype.card_le_of_injective slot hinj
  simp only [Fintype.card_sum] at hcardInj
  omega

theorem lowerBranch_delta_lt_twoNPlusOne_spacing
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta) :
    delta < t / ((2 * n + 1 : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hden :
      (0 : ℝ) < (2 * n + 1 : ℕ) := by
    positivity
  rw [div_lt_iff₀ hden, ht]
  push_cast
  nlinarith

/-- For n>=10 there is a 2n+1 sample phase avoiding both every critical q=1
slot and every top-centred saturation turn slot. -/
theorem exists_topSafe_criticalUncovered_sample_of_n_ge_ten
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn10 : 10 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcardV : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin (2 * n + 1),
      (∀ u : CentreTurnUnitSlot (C top) t,
        ¬ CentreCyclicTurnUnitBadAt
            (C top) t delta u
            (cyclicSamplePhase t (2 * n + 1) r))
      ∧
      (∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u
            (cyclicSamplePhase t (2 * n + 1) r)) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htopCard :
      Fintype.card (CentreTurnUnitSlot (C top) t) = n :=
    centreTurnUnitSlot_card_eq_n_of_exponent_n_sub_one
      (C top) hn4 hdelta0 hdeltaHalf ht hTop
  have hcritCard :
      Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
    six_point_globalUnitGapSlot_card_le_ten
      C hn4 hdelta0 (by linarith : delta < 1) ht
      hcardV top hTop hMin
  have hslot :
      Fintype.card (CentreTurnUnitSlot (C top) t) +
          Fintype.card (GlobalUnitGapSlot C t)
        <
      2 * n + 1 := by
    rw [htopCard]
    omega
  exact exists_sample_outside_topTurn_and_critical
    C top htpos (by omega : 2 ≤ 2 * n + 1)
    hdelta0
    (lowerBranch_delta_lt_twoNPlusOne_spacing
      (by omega : 1 ≤ n) hdeltaHalf ht)
    hslot

/-- Actual projective-cut form.  For n>=10 the sampled cut is simultaneously
critical-uncovered and top-saturation-safe. -/
theorem exists_cut_topSafe_criticalUncovered_of_n_ge_ten
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn10 : 10 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcardV : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin (2 * n + 1),
      let x := cyclicSamplePhase t (2 * n + 1) r
      let c := projectiveCutOfPhase t x
      0 ≤ c ∧
      c < Real.pi ∧
      (∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi)) ∧
      ¬ CutSaturationBadAt
          hp hcap C
          (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
          hlam ht hdelta0
          (by linarith : delta < 1)
          (projectiveCutOfPhase_nonneg
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            (cyclicSamplePhase_nonneg
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
              (by omega : 1 ≤ 2 * n + 1) r))
          (projectiveCutOfPhase_lt_pi
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            (cyclicSamplePhase_lt_t
              (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
              (by omega : 1 ≤ 2 * n + 1) r))
          top := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨r, htopNo, hcritNo⟩ :=
    exists_topSafe_criticalUncovered_sample_of_n_ge_ten
      C hn4 hn10 hdelta0 hdeltaHalf ht
      hcardV top hTop hMin
  let x := cyclicSamplePhase t (2 * n + 1) r
  let c := projectiveCutOfPhase t x
  have hx0 : 0 ≤ x :=
    cyclicSamplePhase_nonneg
      htpos.le (by omega : 1 ≤ 2 * n + 1) r
  have hxt : x < t :=
    cyclicSamplePhase_lt_t
      htpos (by omega : 1 ≤ 2 * n + 1) r
  have hc0 : 0 ≤ c :=
    projectiveCutOfPhase_nonneg htpos hx0
  have hcpi : c < Real.pi :=
    projectiveCutOfPhase_lt_pi htpos hxt
  refine ⟨r, hc0, hcpi, ?_, ?_⟩
  · intro u hbad
    apply hcritNo u
    simpa [x, c, phase_projectiveCutOfPhase htpos] using hbad
  · intro hbad
    obtain ⟨u, hubad⟩ :=
      cutSaturationBadAt_has_canonical_turnUnit_bad
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi top hbad
    apply htopNo u
    simpa [x, c, phase_projectiveCutOfPhase htpos] using hubad

#print axioms topCritical_slot_assignment_injective
#print axioms exists_sample_outside_topTurn_and_critical
#print axioms lowerBranch_delta_lt_twoNPlusOne_spacing
#print axioms exists_topSafe_criticalUncovered_sample_of_n_ge_ten
#print axioms exists_cut_topSafe_criticalUncovered_of_n_ge_ten

end JSP000404Research
