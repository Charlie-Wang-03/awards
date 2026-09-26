import JSP000404Research.CutAdjacentUnitGapBridge
import JSP000404Research.SixPointUnitGapSlots
import JSP000404Research.CriticalPhaseInterval
import Mathlib.Tactic

/-!
# Cyclic critical unit phases and an eleven-sample terminal

A canonical q=1 slot has one canonical cyclic start coordinate alpha0.  A
critical obstruction attached to that slot may be viewed on the universal
cover of the normalized projective phase circle by replacing alpha0 with

  alpha0 + k*t,  k : Z.

If its scaled gap length s lies in [1,1+delta], then its critical bad interval

  [alpha+s-1, alpha+delta]

is contained in the simpler delta-arc

  [alpha, alpha+delta].

For n>=5 and delta<1/2, the eleven equally spaced phases

  r*t/11,  r=0,...,10

have cyclic separation strictly larger than delta because

  11*delta < n+delta = t.

Hence one cyclic delta-arc can contain at most one sample.  In the six-point
top + five-minimum terminal there are at most ten canonical q=1 slots, so the
eleven samples cannot all be critically obstructed.

This closes the cyclic counting backend independently of the remaining
boundary-triangle-to-obstruction geometry.
-/

namespace JSP000404Research

open Real

def centreUnitGapStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) : ℝ :=
  normalizedRayTheta hp t i
    (C.rays.get (gapToRayIndex C u.1))

def centreUnitGapScaledWidth
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) : ℝ :=
  t * C.gaps.get u.1

def globalUnitGapStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) : ℝ :=
  centreUnitGapStart (C u.1) t u.2

def globalUnitGapScaledWidth
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) : ℝ :=
  centreUnitGapScaledWidth (C u.1) t u.2

/-- Periodic critical badness for one canonical global q=1 slot. -/
def GlobalCyclicCriticalUnitBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalUnitGapSlot C t)
    (x : ℝ) : Prop :=
  ∃ k : ℤ,
    let alpha := globalUnitGapStart C t u + (k : ℝ) * t
    let s := globalUnitGapScaledWidth C t u
    1 ≤ s ∧
    s ≤ 1 + delta ∧
    criticalBadLeft alpha s ≤ x ∧
    x ≤ criticalBadRight alpha delta

def CyclicDeltaArcAt
    (t delta alpha x : ℝ) : Prop :=
  ∃ k : ℤ,
    alpha + (k : ℝ) * t ≤ x ∧
    x ≤ alpha + (k : ℝ) * t + delta

theorem globalUnitGapStart_nonneg
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : GlobalUnitGapSlot C t) :
    0 ≤ globalUnitGapStart C t u := by
  unfold globalUnitGapStart centreUnitGapStart
  exact normalizedRayTheta_nonneg
    hp ht u.1
      ((C u.1).rays.get
        (gapToRayIndex (C u.1) u.2.1))

theorem globalUnitGapStart_lt_t
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t)
    (u : GlobalUnitGapSlot C t) :
    globalUnitGapStart C t u < t := by
  unfold globalUnitGapStart centreUnitGapStart
  exact normalizedRayTheta_lt_t
    hp ht u.1
      ((C u.1).rays.get
        (gapToRayIndex (C u.1) u.2.1))

/-- Critical badness is contained in a periodic arc of length delta based at
the same canonical slot start. -/
theorem cyclicCriticalUnitBadAt_implies_deltaArc
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    {u : GlobalUnitGapSlot C t}
    {x : ℝ}
    (hbad : GlobalCyclicCriticalUnitBadAt C t delta u x) :
    CyclicDeltaArcAt t delta
      (globalUnitGapStart C t u) x := by
  rcases hbad with ⟨k, hs1, _hsTop, hxL, hxR⟩
  refine ⟨k, ?_, ?_⟩
  · unfold criticalBadLeft at hxL
    linarith
  · unfold criticalBadRight at hxR
    exact hxR

/-- Eleven equally spaced sample phases on one normalized projective circle. -/
def elevenPhase (t : ℝ) (r : Fin 11) : ℝ :=
  (r.val : ℝ) * t / 11

theorem elevenPhase_nonneg
    {t : ℝ} (ht : 0 ≤ t)
    (r : Fin 11) :
    0 ≤ elevenPhase t r := by
  unfold elevenPhase
  positivity

theorem elevenPhase_lt_t
    {t : ℝ} (ht : 0 < t)
    (r : Fin 11) :
    elevenPhase t r < t := by
  unfold elevenPhase
  have hr : (r.val : ℝ) < 11 := by
    exact_mod_cast r.isLt
  nlinarith

/-- Distinct Fin 11 indices differ by between one and ten in absolute real
value. -/
theorem fin11_val_abs_sub_bounds
    {r s : Fin 11}
    (hrs : r ≠ s) :
    1 ≤ |(r.val : ℝ) - (s.val : ℝ)| ∧
    |(r.val : ℝ) - (s.val : ℝ)| ≤ 10 := by
  have hv : r.val ≠ s.val := by
    intro h
    exact hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have h1Nat : r.val + 1 ≤ s.val := by omega
    have h1Cast :
        (r.val : ℝ) + 1 ≤ (s.val : ℝ) := by
      exact_mod_cast h1Nat
    have hs10Nat : s.val ≤ 10 := by omega
    have hs10 : (s.val : ℝ) ≤ 10 := by
      exact_mod_cast hs10Nat
    have hr0 : (0 : ℝ) ≤ r.val := by positivity
    have h1 : (1 : ℝ) ≤ (s.val : ℝ) - (r.val : ℝ) := by
      linarith
    have h10 : (s.val : ℝ) - (r.val : ℝ) ≤ 10 := by
      linarith
    rw [abs_of_nonpos]
    · constructor <;> linarith
    · exact_mod_cast hlt.le
  · have h1Nat : s.val + 1 ≤ r.val := by omega
    have h1Cast :
        (s.val : ℝ) + 1 ≤ (r.val : ℝ) := by
      exact_mod_cast h1Nat
    have hr10Nat : r.val ≤ 10 := by omega
    have hr10 : (r.val : ℝ) ≤ 10 := by
      exact_mod_cast hr10Nat
    have hs0 : (0 : ℝ) ≤ s.val := by positivity
    have h1 : (1 : ℝ) ≤ (r.val : ℝ) - (s.val : ℝ) := by
      linarith
    have h10 : (r.val : ℝ) - (s.val : ℝ) ≤ 10 := by
      linarith
    rw [abs_of_nonneg]
    · exact ⟨h1, h10⟩
    · exact_mod_cast hgt.le

theorem elevenPhase_abs_sub
    {t : ℝ} (ht : 0 < t)
    (r s : Fin 11) :
    |elevenPhase t r - elevenPhase t s| =
      |(r.val : ℝ) - (s.val : ℝ)| * t / 11 := by
  unfold elevenPhase
  have htAbs : |t| = t := abs_of_pos ht
  rw [show
      (r.val : ℝ) * t / 11 -
          (s.val : ℝ) * t / 11 =
        (((r.val : ℝ) - (s.val : ℝ)) * t) / 11 by ring,
      abs_div, abs_mul, htAbs]
  norm_num
  ring

/-- Any two distinct eleven-sample phases are separated by more than delta in
both the direct and complementary circular directions whenever delta<t/11. -/
theorem elevenPhase_cyclic_separation
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta : delta < t / 11)
    {r s : Fin 11}
    (hrs : r ≠ s) :
    delta < |elevenPhase t r - elevenPhase t s| ∧
    delta <
      t - |elevenPhase t r - elevenPhase t s| := by
  obtain ⟨hd1, hd10⟩ :=
    fin11_val_abs_sub_bounds hrs
  rw [elevenPhase_abs_sub ht r s]
  have h11 : (0 : ℝ) < 11 := by norm_num
  have hlower :
      t / 11 ≤
        |(r.val : ℝ) - (s.val : ℝ)| * t / 11 := by
    apply (div_le_div_iff_of_pos_right h11).2
    nlinarith
  have hupper :
      |(r.val : ℝ) - (s.val : ℝ)| * t / 11
        ≤ 10 * t / 11 := by
    apply (div_le_div_iff_of_pos_right h11).2
    nlinarith
  constructor
  · exact hdelta.trans_le hlower
  · have hcomp :
        t / 11 ≤
          t - |(r.val : ℝ) - (s.val : ℝ)| * t / 11 := by
      nlinarith
    exact hdelta.trans_le hcomp

/-- A periodic delta-arc meeting the fundamental interval [0,t) can only use
period shifts -1 or 0, provided 0<=alpha<t and 0<=delta<t. -/
theorem cyclicDeltaArc_shift_eq_neg_one_or_zero
    {t delta alpha x : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdeltaT : delta < t)
    (halpha0 : 0 ≤ alpha)
    (halphaT : alpha < t)
    (hx0 : 0 ≤ x)
    (hxT : x < t)
    {k : ℤ}
    (hk :
      alpha + (k : ℝ) * t ≤ x ∧
      x ≤ alpha + (k : ℝ) * t + delta) :
    k = -1 ∨ k = 0 := by
  have hkLe0 : k ≤ 0 := by
    by_contra hnot
    have hk1 : (1 : ℤ) ≤ k := by omega
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hk1
    have hlow :
        t ≤ alpha + (k : ℝ) * t := by
      nlinarith
    linarith
  have hneg1Le : (-1 : ℤ) ≤ k := by
    by_contra hnot
    have hk2 : k ≤ (-2 : ℤ) := by omega
    have hk2R : (k : ℝ) ≤ (-2 : ℝ) := by
      exact_mod_cast hk2
    have hupp :
        alpha + (k : ℝ) * t + delta < 0 := by
      nlinarith
    linarith
  omega

/-- Two points of the fundamental interval lying in the same periodic
delta-arc are delta-close either directly or across the circle seam. -/
theorem two_points_same_cyclicDeltaArc_close
    {t delta alpha x y : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdeltaT : delta < t)
    (halpha0 : 0 ≤ alpha)
    (halphaT : alpha < t)
    (hx0 : 0 ≤ x) (hxT : x < t)
    (hy0 : 0 ≤ y) (hyT : y < t)
    (hx : CyclicDeltaArcAt t delta alpha x)
    (hy : CyclicDeltaArcAt t delta alpha y) :
    |x - y| ≤ delta ∨
      t - |x - y| ≤ delta := by
  obtain ⟨kx, hxL, hxR⟩ := hx
  obtain ⟨ky, hyL, hyR⟩ := hy
  have hkx :=
    cyclicDeltaArc_shift_eq_neg_one_or_zero
      ht hdelta0 hdeltaT halpha0 halphaT
      hx0 hxT ⟨hxL, hxR⟩
  have hky :=
    cyclicDeltaArc_shift_eq_neg_one_or_zero
      ht hdelta0 hdeltaT halpha0 halphaT
      hy0 hyT ⟨hyL, hyR⟩
  rcases hkx with rfl | rfl <;>
    rcases hky with rfl | rfl
  · left
    have hxy : x - y ≤ delta := by
      nlinarith
    have hyx : y - x ≤ delta := by
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  · right
    have hxyOrder : x < y := by
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hxyOrder.le)]
    nlinarith
  · right
    have hyxOrder : y < x := by
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr hyxOrder.le)]
    nlinarith
  · left
    have hxy : x - y ≤ delta := by
      nlinarith
    have hyx : y - x ≤ delta := by
      nlinarith
    rw [abs_le]
    constructor <;> linarith

/-- Consequently one periodic delta-arc can contain at most one of the eleven
equally spaced samples. -/
theorem elevenPhase_injective_on_same_cyclicDeltaArc
    {t delta alpha : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / 11)
    (halpha0 : 0 ≤ alpha)
    (halphaT : alpha < t)
    {r s : Fin 11}
    (hr : CyclicDeltaArcAt t delta alpha (elevenPhase t r))
    (hs : CyclicDeltaArcAt t delta alpha (elevenPhase t s)) :
    r = s := by
  by_contra hrs
  have hsep :=
    elevenPhase_cyclic_separation ht hdelta hrs
  have hdeltaT : delta < t := by
    have ht11 : t / 11 < t := by
      nlinarith
    exact hdelta.trans ht11
  have hclose :=
    two_points_same_cyclicDeltaArc_close
      ht hdelta0 hdeltaT halpha0 halphaT
      (elevenPhase_nonneg ht.le r)
      (elevenPhase_lt_t ht r)
      (elevenPhase_nonneg ht.le s)
      (elevenPhase_lt_t ht s)
      hr hs
  rcases hclose with hdirect | hwrap
  · linarith
  · linarith

/-- Assigning a critical unit slot to every eleven-sample phase forces an
injective map into the global unit-slot type. -/
theorem critical_slot_assignment_on_elevenPhase_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < t / 11)
    (slot : Fin 11 → GlobalUnitGapSlot C t)
    (hbad :
      ∀ r : Fin 11,
        GlobalCyclicCriticalUnitBadAt
          C t delta (slot r) (elevenPhase t r)) :
    Function.Injective slot := by
  intro r s hrsSlot
  have hrArc :=
    cyclicCriticalUnitBadAt_implies_deltaArc
      C (hbad r)
  have hsArc :
      CyclicDeltaArcAt t delta
        (globalUnitGapStart C t (slot r))
        (elevenPhase t s) := by
    have h :=
      cyclicCriticalUnitBadAt_implies_deltaArc
        C (hbad s)
    simpa [hrsSlot] using h
  exact elevenPhase_injective_on_same_cyclicDeltaArc
    ht hdelta0 hdelta
    (globalUnitGapStart_nonneg C ht.le (slot r))
    (globalUnitGapStart_lt_t C ht (slot r))
    hrArc hsArc

/-- Cyclic six-point terminal for n>=5: at least one of the eleven equally
spaced phases is not carried by any critical canonical q=1 slot. -/
theorem exists_uncovered_elevenPhase_of_six_point_terminal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin 11,
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (elevenPhase t r) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hnR : (5 : ℝ) ≤ n := by
    exact_mod_cast hn5
  have h11delta :
      11 * delta < t := by
    rw [ht]
    nlinarith
  have hdelta :
      delta < t / 11 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11)).2
    nlinarith

  by_contra hnone
  push_neg at hnone
  let slot : Fin 11 → GlobalUnitGapSlot C t :=
    fun r => Classical.choose (hnone r)
  have hbad :
      ∀ r : Fin 11,
        GlobalCyclicCriticalUnitBadAt
          C t delta (slot r) (elevenPhase t r) := by
    intro r
    exact Classical.choose_spec (hnone r)
  have hinj :
      Function.Injective slot :=
    critical_slot_assignment_on_elevenPhase_injective
      C htpos hdelta0 hdelta slot hbad
  have hcardInj :
      11 ≤ Fintype.card (GlobalUnitGapSlot C t) := by
    have h :=
      Fintype.card_le_of_injective slot hinj
    simpa using h
  have hslot10 :
      Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
    six_point_globalUnitGapSlot_card_le_ten
      C hn4 hdelta0 (by linarith) ht
      hcard top hTop hMin
  omega

#print axioms cyclicCriticalUnitBadAt_implies_deltaArc
#print axioms elevenPhase_cyclic_separation
#print axioms elevenPhase_injective_on_same_cyclicDeltaArc
#print axioms critical_slot_assignment_on_elevenPhase_injective
#print axioms exists_uncovered_elevenPhase_of_six_point_terminal

end JSP000404Research
