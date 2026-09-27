import JSP000404Research.UncoveredBoundaryColoring
import JSP000404Research.CutProjectiveBandBudget
import JSP000404Research.ProjectiveBandLastMergeCapacity
import JSP000404Research.SixPointMergedOneExceptionCapacity
import Mathlib.Tactic

/-!
# Final merged six-point terminal at one arbitrary cut

This file isolates the exact phase-selection target left by the current
JSP-000404 route.

At one projective cut c let P be the n+1 cut projective-band partition.
Call a centre saturation-bad when

* its old local palette saturates the one-layer bound, and
* old colours 0 and n are not both active.

At a phase uncovered by every canonical q=1 critical slot,
UncoveredBoundaryColoring supplies a proper Boolean bit for the union of
old colours 0 and n, so BinaryEdgePartition.mergeLastPartition gives an
n-colour partition M.

For every centre v:

* if v is not saturation-bad, then
      active_M(v) <= n - exponent(v);
* without any safety assumption,
      active_M(v) <= n - exponent(v) + 1.

Therefore in the six-point profile

  exponent(top)=n-1,
  exponent(v)=n-3 for v!=top,

it is enough that the top is not saturation-bad and all saturation-bad
minima, if any, are concentrated at one distinguished non-top vertex.
The weighted one-exception terminal then contradicts existence of M.

Thus all remaining geometry is cleanly separated into one phase-selection
statement:

  find an uncovered cut phase at which top is safe and at most one minimum
  is saturation-bad.
-/

namespace JSP000404Research

open BinaryEdgePartition

def SaturationCollisionFailure
    {V : Type*} [LinearOrder V]
    {n : ℕ}
    (P : BinaryEdgePartition V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Prop :=
  (active P v).card = (n + 1) - exponent v ∧
    ¬ (
      (0 : Fin (n + 1)) ∈ active P v ∧
      Fin.last n ∈ active P v
    )

theorem merged_active_le_exact_of_not_saturationCollisionFailure
    {V : Type*} [LinearOrder V]
    {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hold :
      ∀ v, (active P v).card ≤
        (n + 1) - exponent v)
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V)
    (hsafe :
      ¬ SaturationCollisionFailure P exponent v) :
    (active
      (mergeLastPartition hn P wrapBit hwrap) v).card
      ≤
    n - exponent v := by
  by_cases hsat :
      (active P v).card = (n + 1) - exponent v
  · have hboundary :
        (0 : Fin (n + 1)) ∈ active P v ∧
        Fin.last n ∈ active P v := by
      by_contra hnot
      exact hsafe ⟨hsat, hnot⟩
    have hdrop :=
      mergeLastPartition_active_card_add_one_le
        hn P wrapBit hwrap v
        hboundary.1 hboundary.2
    have hk := hexp v
    omega
  · have holdv := hold v
    have hstrict :
        (active P v).card <
          (n + 1) - exponent v := by
      omega
    have hmono :=
      mergeLastPartition_active_card_le
        hn P wrapBit hwrap v
    have hk := hexp v
    omega

theorem merged_active_le_one_extra
    {V : Type*} [LinearOrder V]
    {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hold :
      ∀ v, (active P v).card ≤
        (n + 1) - exponent v)
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V) :
    (active
      (mergeLastPartition hn P wrapBit hwrap) v).card
      ≤
    n - exponent v + 1 := by
  have hmono :=
    mergeLastPartition_active_card_le
      hn P wrapBit hwrap v
  have holdv := hold v
  have hk := hexp v
  omega

/-- Concrete saturation-bad predicate for the cut projective-band partition. -/
def CutSaturationBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (v : V) : Prop :=
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  SaturationCollisionFailure
    P (fun i => centreExponent (C i) t) v

/-- At an uncovered cut phase, construct the actual merged n-colour binary
partition. -/
noncomputable def uncoveredCutMergedPartition
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
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi)) :
    BinaryEdgePartition V n := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let wrapBit :=
    cutBoundaryWrapBit hp n htpos htop hc0 hcpi
  have hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v := by
    simpa [P, wrapBit, htop] using
      cutBoundaryWrapBit_separates
        hp hcap C hn htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi huncovered
  exact mergeLastPartition hn P wrapBit hwrap

/-- Safe centres meet the exact n-colour local deficit after the uncovered
boundary merge. -/
theorem uncoveredCutMergedPartition_active_le_of_not_bad
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
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (v : V)
    (hsafe :
      ¬ CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi v) :
    (active
      (uncoveredCutMergedPartition
        hp hcap C hn htpos hlam ht hdelta0
        hdeltaHalf hc0 hcpi huncovered)
      v).card
      ≤
    n - centreExponent (C v) t := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun i => centreExponent (C i) t
  let wrapBit :=
    cutBoundaryWrapBit hp n htpos htop hc0 hcpi
  have hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v := by
    simpa [P, wrapBit, htop] using
      cutBoundaryWrapBit_separates
        hp hcap C hn htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi huncovered
  have hold :
      ∀ i, (active P i).card ≤
        (n + 1) - exponent i := by
    intro i
    dsimp [P, exponent]
    exact cutProjectiveBandPartition_active_card_le_deficit
      hp hcap htpos hlam ht hdelta0
      (by linarith : delta < 1) hc0 hcpi C i
  have hexp :
      ∀ i, exponent i ≤ n := by
    intro i
    dsimp [exponent]
    have hlt :=
      centreExponent_lt_n
        (C i) n delta t hn hdelta0
        (by linarith : delta < 1) ht
    omega
  have hsafe' :
      ¬ SaturationCollisionFailure P exponent v := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hsafe
  have h :=
    merged_active_le_exact_of_not_saturationCollisionFailure
      hn P exponent hexp hold wrapBit hwrap v hsafe'
  simpa [uncoveredCutMergedPartition, P, exponent,
    wrapBit, htop, hwrap] using h

/-- Every centre, including a saturation-bad one, misses the exact target by
at most one local colour after the merge. -/
theorem uncoveredCutMergedPartition_active_le_one_extra
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
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (v : V) :
    (active
      (uncoveredCutMergedPartition
        hp hcap C hn htpos hlam ht hdelta0
        hdeltaHalf hc0 hcpi huncovered)
      v).card
      ≤
    n - centreExponent (C v) t + 1 := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun i => centreExponent (C i) t
  let wrapBit :=
    cutBoundaryWrapBit hp n htpos htop hc0 hcpi
  have hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v := by
    simpa [P, wrapBit, htop] using
      cutBoundaryWrapBit_separates
        hp hcap C hn htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi huncovered
  have hold :
      ∀ i, (active P i).card ≤
        (n + 1) - exponent i := by
    intro i
    dsimp [P, exponent]
    exact cutProjectiveBandPartition_active_card_le_deficit
      hp hcap htpos hlam ht hdelta0
      (by linarith : delta < 1) hc0 hcpi C i
  have hexp :
      ∀ i, exponent i ≤ n := by
    intro i
    dsimp [exponent]
    have hlt :=
      centreExponent_lt_n
        (C i) n delta t hn hdelta0
        (by linarith : delta < 1) ht
    omega
  have h :=
    merged_active_le_one_extra
      hn P exponent hexp hold wrapBit hwrap v
  simpa [uncoveredCutMergedPartition, P, exponent,
    wrapBit, htop, hwrap] using h

/-- Six-point terminal at one cut.

The distinguished non-top vertex bad need not actually be saturation-bad.
The hypothesis only says that every bad minimum, if any, equals bad.
-/
theorem no_uncovered_cut_with_top_safe_and_atMostOne_bad_minimum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (hcard : Fintype.card V = 6)
    (top bad : V)
    (htb : top ≠ bad)
    (hTopExp :
      centreExponent (C top) t = n - 1)
    (hMinExp :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (hTopSafe :
      ¬ CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi top)
    (hBadUnique :
      ∀ v : V, v ≠ top →
        CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi v →
        v = bad) :
    False := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
  have hTop :
      (active M top).card ≤ 1 := by
    have h :=
      uncoveredCutMergedPartition_active_le_of_not_bad
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered top hTopSafe
    rw [hTopExp] at h
    omega
  have hBad :
      (active M bad).card ≤ 4 := by
    have h :=
      uncoveredCutMergedPartition_active_le_one_extra
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered bad
    have hbadMin : centreExponent (C bad) t = n - 3 :=
      hMinExp bad htb.symm
    rw [hbadMin] at h
    omega
  have hOther :
      ∀ v : V, v ≠ top → v ≠ bad →
        (active M v).card ≤ 3 := by
    intro v hvt hvb
    have hsafe :
        ¬ CutSaturationBadAt
            hp hcap C htpos hlam ht hdelta0
            (by linarith : delta < 1)
            hc0 hcpi v := by
      intro hbadV
      exact hvb (hBadUnique v hvt hbadV)
    have h :=
      uncoveredCutMergedPartition_active_le_of_not_bad
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered v hsafe
    rw [hMinExp v hvt] at h
    omega
  exact no_six_point_partition_with_one_min_exception
    hn M top bad htb hcard hTop hBad hOther

#print axioms merged_active_le_exact_of_not_saturationCollisionFailure
#print axioms merged_active_le_one_extra
#print axioms no_uncovered_cut_with_top_safe_and_atMostOne_bad_minimum

end JSP000404Research
