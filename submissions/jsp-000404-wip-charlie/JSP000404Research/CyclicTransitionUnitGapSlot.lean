import JSP000404Research.SixPointUnitGapSlots
import JSP000404Research.TransitionUnitGapSlot
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Cut-independent cyclic unit-transition slots

GlobalUnitGapSlot already indexes every q=1 coordinate of every centre's
cyclic projective quotient list.  What was missing from the phase argument is
a cut-independent transition predicate: ordinary coordinates compare adjacent
sorted rays, while the final coordinate compares the last ray with the lifted
first sign.

The resulting subtype is independent of any later phase/cut rotation and
therefore provides one common finite slot universe for all phases.
-/

namespace JSP000404Research

/-- Convert a cyclic gap coordinate to the identically numbered ray index. -/
def gapToRayIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : Fin C.gaps.length) :
    Fin C.rays.length :=
  Fin.cast C.gaps_length r

@[simp] theorem gapToRayIndex_val
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : Fin C.gaps.length) :
    (gapToRayIndex C r).val = r.val := rfl

/-- The first ray index; centre ray lists are nonempty. -/
def firstRayIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i) :
    Fin C.rays.length :=
  ⟨0, List.length_pos.mpr C.nonempty⟩

/-- A cyclic gap coordinate is a genuine sign-transition position.

For an ordinary coordinate m this is the sign change m -> m+1.
For the final cyclic coordinate it is the lifted wrap step
last -> !first.
-/
def CentreUnitGapCyclicTransition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) : Prop :=
  let r := gapToRayIndex C u.1
  if h : r.val + 1 < C.rays.length then
    raySignAt hp i (C.rays.get r) ≠
      raySignAt hp i
        (C.rays.get ⟨r.val + 1, h⟩)
  else
    raySignAt hp i (C.rays.get r) ≠
      !raySignAt hp i (C.rays.get (firstRayIndex C))

def GlobalUnitGapCyclicTransition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) : Prop :=
  CentreUnitGapCyclicTransition (C u.1) t u.2

/-- Common cut-independent slot universe for terminal critical transitions. -/
abbrev GlobalCyclicTransitionUnitGapSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :=
  {u : GlobalUnitGapSlot C t //
    GlobalUnitGapCyclicTransition C t u}

/-- Forgetting the transition proof embeds cyclic transition slots into all
unit-gap slots. -/
theorem globalCyclicTransitionUnitGapSlot_card_le_all
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (GlobalCyclicTransitionUnitGapSlot C t) ≤
      Fintype.card (GlobalUnitGapSlot C t) := by
  let f : GlobalCyclicTransitionUnitGapSlot C t →
      GlobalUnitGapSlot C t :=
    fun u => u.1
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext h
  exact Fintype.card_le_of_injective f hf

/-- Six-point top + five-minimum specialization: at most ten cyclic q=1
transition slots, uniformly over all choices of projective cut. -/
theorem six_point_globalCyclicTransitionUnitGapSlot_card_le_ten
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    Fintype.card (GlobalCyclicTransitionUnitGapSlot C t) ≤ 10 := by
  exact
    (globalCyclicTransitionUnitGapSlot_card_le_all C t).trans
      (six_point_globalUnitGapSlot_card_le_ten
        C hn hdelta0 hdelta1 ht hcard top hTop hMin)

#print axioms globalCyclicTransitionUnitGapSlot_card_le_all
#print axioms six_point_globalCyclicTransitionUnitGapSlot_card_le_ten

end JSP000404Research
