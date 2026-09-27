import JSP000404Research.CutMergedOneExceptionTerminal
import JSP000404Research.CutSaturationTurnSlotBridge
import Mathlib.Tactic

/-!
# Every cut saturation-bad centre is witnessed by a canonical global turn slot

CutMergedOneExceptionTerminal defines the exact remaining local failure:
the old n+1 cut partition saturates its local one-layer bound, but colours
0 and n are not both active.

CutSaturationTurnSlotBridge canonicalizes precisely that situation.  This file
packages the result at the family/global sigma level.

Consequently all saturation failures at all projective cuts live in the fixed
cut-independent finite type

  GlobalTurnUnitSlot C t.

The final phase-selection problem can therefore be phrased entirely in terms
of periodic bad sets of canonical q=1 critical slots and canonical turn-unit
slots.
-/

namespace JSP000404Research

theorem cutSaturationBadAt_has_canonical_turnUnit_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ u : CentreTurnUnitSlot (C i) t,
      CentreCyclicTurnUnitBadAt
        (C i) t delta u (t * c / Real.pi) := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  have hbad' :
      SaturationCollisionFailure
        P (fun v => centreExponent (C v) t) i := by
    simpa [CutSaturationBadAt, P, htop] using hbad
  rcases hbad' with ⟨hsatCard, hfail⟩
  have hexpLe :
      centreExponent (C i) t ≤ n := by
    have hlt :=
      centreExponent_lt_n
        (C i) n delta t hn hdelta0
        (by linarith : delta < 1) ht
    omega
  have hsat :
      centreExponent (C i) t +
          (BinaryEdgePartition.active P i).card
        =
      n + 1 := by
    rw [hsatCard]
    omega
  exact exists_canonical_turnUnit_bad_of_cut_saturated_failure
    hp hcap hn htpos hlam ht hdelta0 hdeltaHalf
    hc0 hcpi (C i) hsat hfail

theorem cutSaturationBadAt_has_global_turnUnit_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ u : GlobalTurnUnitSlot C t,
      u.1 = i ∧
      GlobalCyclicTurnUnitBadAt
        C t delta u (t * c / Real.pi) := by
  obtain ⟨u, hubad⟩ :=
    cutSaturationBadAt_has_canonical_turnUnit_bad
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hbad
  exact ⟨⟨i, u⟩, rfl, hubad⟩

/-- Contrapositive outlet: if no canonical turn-unit slot centered at i is bad
at the current phase, then i is merge-safe. -/
theorem not_cutSaturationBadAt_of_no_turnUnit_bad_at_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hno :
      ∀ u : GlobalTurnUnitSlot C t,
        u.1 = i →
        ¬ GlobalCyclicTurnUnitBadAt
            C t delta u (t * c / Real.pi)) :
    ¬ CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i := by
  intro hbad
  obtain ⟨u, hui, hubad⟩ :=
    cutSaturationBadAt_has_global_turnUnit_bad
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hbad
  exact hno u hui hubad

#print axioms cutSaturationBadAt_has_canonical_turnUnit_bad
#print axioms cutSaturationBadAt_has_global_turnUnit_bad
#print axioms not_cutSaturationBadAt_of_no_turnUnit_bad_at_centre

end JSP000404Research
