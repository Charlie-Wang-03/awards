import JSP000404Research.PositiveGapPhaseInterval
import JSP000404Research.SixPointUnitGapSlots
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Canonical whole-unit turn subslots inside centre quotient gaps

A canonical quotient coordinate q_r=floor(t*g_r) contains q_r whole normalized
unit positions.  Package them directly as

  Sigma r : gap-index, Fin(q_r).

This is the correct slot universe for the final rotating-seam argument.

* q_r=0 contributes no slots;
* q_r=1 contributes exactly the familiar unit-gap slot;
* q_r>=2 contributes the multiple integer seam positions which may support a
  saturated last-merge failure.

The local slot cardinality is exactly the total quotient mass, not merely the
positive support.
-/

namespace JSP000404Research

open scoped BigOperators

abbrev CentreTurnUnitSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :=
  Σ r : Fin C.gaps.length, Fin (centreQuotient C t r)

abbrev GlobalTurnUnitSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :=
  Σ i : V, CentreTurnUnitSlot (C i) t

def centreTurnUnitGapIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    {C : CentreProjectiveCycle hp i}
    {t : ℝ}
    (u : CentreTurnUnitSlot C t) :
    Fin C.gaps.length :=
  u.1

def centreTurnUnitOffset
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    {C : CentreProjectiveCycle hp i}
    {t : ℝ}
    (u : CentreTurnUnitSlot C t) : ℕ :=
  u.2.val

def centreTurnUnitGapQuotient
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreTurnUnitSlot C t) : ℕ :=
  centreQuotient C t u.1

def centreTurnUnitGapScaledLength
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreTurnUnitSlot C t) : ℝ :=
  t * C.gaps.get u.1

/-- Universal-cover start of this whole-unit subslot. -/
def centreTurnUnitStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreTurnUnitSlot C t) : ℝ :=
  normalizedRayTheta hp t i
      (C.rays.get (gapToRayIndex C u.1))
    + u.2.val

def globalTurnUnitStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalTurnUnitSlot C t) : ℝ :=
  centreTurnUnitStart (C u.1) t u.2

def globalTurnUnitGapQuotient
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalTurnUnitSlot C t) : ℕ :=
  centreTurnUnitGapQuotient (C u.1) t u.2

def globalTurnUnitGapScaledLength
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalTurnUnitSlot C t) : ℝ :=
  centreTurnUnitGapScaledLength (C u.1) t u.2

theorem centreTurnUnitOffset_lt_quotient
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreTurnUnitSlot C t) :
    centreTurnUnitOffset u <
      centreTurnUnitGapQuotient C t u := by
  exact u.2.isLt

theorem centreTurnUnitSlot_card_eq_quotient_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (CentreTurnUnitSlot C t) =
      ∑ r, centreQuotient C t r := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  simp

theorem globalTurnUnitSlot_card_eq_quotient_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (GlobalTurnUnitSlot C t) =
      ∑ i : V, ∑ r, centreQuotient (C i) t r := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact centreTurnUnitSlot_card_eq_quotient_sum (C i) t

/-- Every canonical q=1 gap embeds as its unique whole-unit turn subslot. -/
def centreUnitGapToTurnUnitSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) :
    CentreTurnUnitSlot C t :=
  ⟨u.1, ⟨0, by simpa [u.2]⟩⟩

def globalUnitGapToTurnUnitSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) :
    GlobalTurnUnitSlot C t :=
  ⟨u.1, centreUnitGapToTurnUnitSlot (C u.1) t u.2⟩

@[simp] theorem globalUnitGapToTurnUnitSlot_start
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

/-- Every centre has at most n whole-unit quotient subslots in the lower
Sendov branch. -/
theorem centreTurnUnitSlot_card_le_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    Fintype.card (CentreTurnUnitSlot C t) ≤ n := by
  rw [centreTurnUnitSlot_card_eq_quotient_sum]
  exact centreQuotient_function_sum_le_n
    C n delta t hn hdelta0 hdelta1 ht

/-- Coarse six-point bound before any global geometric compression. -/
theorem six_point_globalTurnUnitSlot_card_le_six_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6) :
    Fintype.card (GlobalTurnUnitSlot C t) ≤ 6 * n := by
  rw [globalTurnUnitSlot_card_eq_quotient_sum C t]
  calc
    (∑ i : V, ∑ r, centreQuotient (C i) t r)
      ≤ ∑ _i : V, n := by
          exact Finset.sum_le_sum
            (fun i _ =>
              centreQuotient_function_sum_le_n
                (C i) n delta t hn hdelta0 hdelta1 ht)
    _ = 6 * n := by simp [hcard]

#print axioms centreTurnUnitSlot_card_eq_quotient_sum
#print axioms globalTurnUnitSlot_card_eq_quotient_sum
#print axioms centreTurnUnitSlot_card_le_n

end JSP000404Research
