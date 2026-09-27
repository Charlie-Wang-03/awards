import JSP000404Research.PositiveGapSlots
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# Periodic bad-phase arcs for arbitrary positive quotient gaps

For one canonical positive quotient coordinate let

  alpha = canonical normalized start,
  s     = scaled normalized gap length,
  q     = floor(s) >= 1.

The last-merge saturation calculation produces the same interval shape as the
q=1 critical-transition calculation, with q in place of one:

  [alpha + s - q, alpha + delta].

Its formal width is q + delta - s.  Since q=floor(s), q<=s.  Therefore every
nonempty such bad interval is contained in the canonical delta-arc

  [alpha, alpha+delta].

No assumption that q=1 is used.  This is the common periodic phase object for
q>=2 saturation obstructions.
-/

namespace JSP000404Research

def positiveGapBadLeft (alpha s : ℝ) (q : ℕ) : ℝ :=
  alpha + s - q

def positiveGapBadRight (alpha delta : ℝ) : ℝ :=
  alpha + delta

theorem positiveGap_bad_width
    (alpha s delta : ℝ) (q : ℕ) :
    positiveGapBadRight alpha delta -
        positiveGapBadLeft alpha s q
      =
    (q : ℝ) + delta - s := by
  simp [positiveGapBadLeft, positiveGapBadRight]
  ring

theorem positiveGap_bad_width_bounds
    {alpha s delta : ℝ} {q : ℕ}
    (hdelta0 : 0 ≤ delta)
    (hqs : (q : ℝ) ≤ s)
    (hsq : s ≤ (q : ℝ) + delta) :
    0 ≤
        positiveGapBadRight alpha delta -
          positiveGapBadLeft alpha s q
      ∧
    positiveGapBadRight alpha delta -
          positiveGapBadLeft alpha s q
        ≤ delta := by
  rw [positiveGap_bad_width]
  constructor <;> linarith

/-- Periodic generalized badness attached to one canonical positive gap. -/
def GlobalCyclicPositiveGapBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalPositiveGapSlot C t)
    (x : ℝ) : Prop :=
  ∃ k : ℤ,
    let alpha :=
      globalPositiveGapStart C t u + (k : ℝ) * t
    let s :=
      globalPositiveGapScaledLength C t u
    let q :=
      globalPositiveGapQuotient C t u
    positiveGapBadLeft alpha s q ≤ x ∧
      x ≤ positiveGapBadRight alpha delta

theorem globalPositiveGapStart_nonneg
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : GlobalPositiveGapSlot C t) :
    0 ≤ globalPositiveGapStart C t u := by
  unfold globalPositiveGapStart centrePositiveGapStart
  exact normalizedRayTheta_nonneg
    hp ht u.1
      ((C u.1).rays.get
        (gapToRayIndex (C u.1) u.2.1))

theorem globalPositiveGapStart_lt_t
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t)
    (u : GlobalPositiveGapSlot C t) :
    globalPositiveGapStart C t u < t := by
  unfold globalPositiveGapStart centrePositiveGapStart
  exact normalizedRayTheta_lt_t
    hp ht u.1
      ((C u.1).rays.get
        (gapToRayIndex (C u.1) u.2.1))

theorem globalPositiveGapScaledLength_nonneg
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : GlobalPositiveGapSlot C t) :
    0 ≤ globalPositiveGapScaledLength C t u := by
  unfold globalPositiveGapScaledLength
    centrePositiveGapScaledLength
  exact mul_nonneg ht
    ((C u.1).gaps_nonneg
      ((C u.1).gaps.get u.2.1)
      (List.get_mem _ _))

theorem globalPositiveGap_quotient_le_scaledLength
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : GlobalPositiveGapSlot C t) :
    (globalPositiveGapQuotient C t u : ℝ) ≤
      globalPositiveGapScaledLength C t u := by
  change
    ((Nat.floor
      (globalPositiveGapScaledLength C t u) : ℕ) : ℝ) ≤
        globalPositiveGapScaledLength C t u
  exact Nat.floor_le
    (globalPositiveGapScaledLength_nonneg C ht u)

/-- Every generalized positive-gap bad phase lies in the periodic delta-arc
based at the canonical start of that same slot. -/
theorem cyclicPositiveGapBadAt_implies_deltaArc
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 ≤ t)
    {u : GlobalPositiveGapSlot C t}
    {x : ℝ}
    (hbad : GlobalCyclicPositiveGapBadAt C t delta u x) :
    CyclicDeltaArcAt t delta
      (globalPositiveGapStart C t u) x := by
  rcases hbad with ⟨k, hxL, hxR⟩
  refine ⟨k, ?_, ?_⟩
  · have hqs :
        (globalPositiveGapQuotient C t u : ℝ) ≤
          globalPositiveGapScaledLength C t u :=
      globalPositiveGap_quotient_le_scaledLength C ht u
    unfold positiveGapBadLeft at hxL
    linarith
  · exact hxR

/-- The actual floor window of a positive canonical slot. -/
theorem globalPositiveGap_floor_window
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : GlobalPositiveGapSlot C t) :
    (globalPositiveGapQuotient C t u : ℝ) ≤
        globalPositiveGapScaledLength C t u
      ∧
    globalPositiveGapScaledLength C t u <
        (globalPositiveGapQuotient C t u : ℝ) + 1 := by
  constructor
  · exact globalPositiveGap_quotient_le_scaledLength C ht u
  · change
      globalPositiveGapScaledLength C t u <
        ((Nat.floor
          (globalPositiveGapScaledLength C t u) : ℕ) : ℝ) + 1
    exact Nat.lt_floor_add_one
      (globalPositiveGapScaledLength C t u)

/-- If the generalized bad interval is nonempty then its actual width is in
[0,delta]. -/
theorem cyclicPositiveGapBadAt_width_bounds
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 ≤ t)
    (hdelta0 : 0 ≤ delta)
    {u : GlobalPositiveGapSlot C t}
    {x : ℝ}
    (hbad : GlobalCyclicPositiveGapBadAt C t delta u x) :
    let s := globalPositiveGapScaledLength C t u
    let q := globalPositiveGapQuotient C t u
    0 ≤ (q : ℝ) + delta - s ∧
      (q : ℝ) + delta - s ≤ delta := by
  rcases hbad with ⟨k, hxL, hxR⟩
  dsimp
  have hqs :=
    globalPositiveGap_quotient_le_scaledLength C ht u
  have hsq :
      globalPositiveGapScaledLength C t u ≤
        (globalPositiveGapQuotient C t u : ℝ) + delta := by
    unfold positiveGapBadLeft positiveGapBadRight at hxL hxR
    linarith
  constructor <;> linarith

#print axioms cyclicPositiveGapBadAt_implies_deltaArc
#print axioms globalPositiveGap_floor_window
#print axioms cyclicPositiveGapBadAt_width_bounds

end JSP000404Research
