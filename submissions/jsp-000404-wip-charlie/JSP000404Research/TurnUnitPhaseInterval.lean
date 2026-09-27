import JSP000404Research.TurnUnitSlots
import JSP000404Research.PositiveGapPhaseInterval
import Mathlib.Tactic

/-!
# Periodic phase intervals carried by whole-unit turn subslots

For a canonical quotient gap with scaled length s and q=floor(s), its j-th
whole-unit turn subslot has universal-cover start

  alpha_j = alpha_gap + j,     0 <= j < q.

The saturation bad interval attached to this seam is

  [alpha_j + s - q, alpha_j + delta].

Its width is q+delta-s, independent of j, and is at most delta whenever
nonempty.  Since q<=s, the bad interval is contained in the simpler delta arc

  [alpha_j, alpha_j+delta].

This is the common phase object needed after a saturated seam has been mapped
back to a canonical CentreTurnUnitSlot.
-/

namespace JSP000404Research

def CentreCyclicTurnUnitBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : CentreTurnUnitSlot C t)
    (x : ℝ) : Prop :=
  ∃ k : ℤ,
    let alpha :=
      centreTurnUnitStart C t u + (k : ℝ) * t
    let s :=
      centreTurnUnitGapScaledLength C t u
    let q :=
      centreTurnUnitGapQuotient C t u
    positiveGapBadLeft alpha s q ≤ x ∧
      x ≤ positiveGapBadRight alpha delta

def GlobalCyclicTurnUnitBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalTurnUnitSlot C t)
    (x : ℝ) : Prop :=
  CentreCyclicTurnUnitBadAt
    (C u.1) t delta u.2 x

theorem centreTurnUnitGapScaledLength_nonneg
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : CentreTurnUnitSlot C t) :
    0 ≤ centreTurnUnitGapScaledLength C t u := by
  unfold centreTurnUnitGapScaledLength
  exact mul_nonneg ht
    (C.gaps_nonneg
      (C.gaps.get u.1)
      (List.get_mem _ _))

theorem centreTurnUnit_quotient_le_scaledLength
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 ≤ t)
    (u : CentreTurnUnitSlot C t) :
    (centreTurnUnitGapQuotient C t u : ℝ) ≤
      centreTurnUnitGapScaledLength C t u := by
  change
    ((Nat.floor
      (centreTurnUnitGapScaledLength C t u) : ℕ) : ℝ) ≤
        centreTurnUnitGapScaledLength C t u
  exact Nat.floor_le
    (centreTurnUnitGapScaledLength_nonneg C ht u)

def CyclicDeltaArcAtAnyBase
    (t delta alpha x : ℝ) : Prop :=
  ∃ k : ℤ,
    alpha + (k : ℝ) * t ≤ x ∧
      x ≤ alpha + (k : ℝ) * t + delta

/-- Every turn-unit bad interval sits inside a periodic delta arc based at the
same whole-unit seam start. -/
theorem cyclicTurnUnitBadAt_implies_deltaArc
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 ≤ t)
    {u : CentreTurnUnitSlot C t}
    {x : ℝ}
    (hbad : CentreCyclicTurnUnitBadAt C t delta u x) :
    CyclicDeltaArcAtAnyBase t delta
      (centreTurnUnitStart C t u) x := by
  rcases hbad with ⟨k, hxL, hxR⟩
  refine ⟨k, ?_, ?_⟩
  · have hqs :=
      centreTurnUnit_quotient_le_scaledLength
        C ht u
    unfold positiveGapBadLeft at hxL
    linarith
  · exact hxR

theorem cyclicGlobalTurnUnitBadAt_implies_deltaArc
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (ht : 0 ≤ t)
    {u : GlobalTurnUnitSlot C t}
    {x : ℝ}
    (hbad : GlobalCyclicTurnUnitBadAt C t delta u x) :
    CyclicDeltaArcAtAnyBase t delta
      (globalTurnUnitStart C t u) x := by
  exact cyclicTurnUnitBadAt_implies_deltaArc
    (C u.1) ht hbad

/-- Unit-gap slots use offset zero in the common turn-unit universe. -/
theorem unitGap_turnStart_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) :
    globalTurnUnitStart C t
        (globalUnitGapToTurnUnitSlot C t u)
      =
    globalUnitGapStart C t u := by
  rfl

#print axioms cyclicTurnUnitBadAt_implies_deltaArc
#print axioms cyclicGlobalTurnUnitBadAt_implies_deltaArc

end JSP000404Research
