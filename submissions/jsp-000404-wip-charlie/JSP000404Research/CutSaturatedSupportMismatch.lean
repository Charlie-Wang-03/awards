import JSP000404Research.CutSupportInvariant
import JSP000404Research.SaturatedBandJumpMismatch
import JSP000404Research.CutMergedOneExceptionTerminal
import Mathlib.Tactic

/-!
# Exact support/mismatch count at a saturation-bad minimum

At a six-point minimum with exponent n-3, exact saturation of the old
(n+1)-band cut partition forces exactly four occupied cut bands.

Write the cut-sorted normalized ray values as

  a :: xs,

their actual cyclic floor-gap quotients as qs, and the cyclic jumps of their
integer band labels as bs.

Then:

* qs is pointwise dominated by bs;
* positiveCount(bs)=4, because positive cyclic band jumps count occupied bands;
* positiveCount(qs)=canonical positiveSupport, by CutSupportInvariant;
* both quotient and band-jump listExponent equal n-3.

Hence the number of positions with q=0 but b>0 is exactly

  4 - positiveSupport,

and every such extra band jump is exactly one unit.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem cutSaturationBadAt_support_mismatch_data
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n s : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hexp :
      centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = s)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        let qs := linearCyclicGapQuotients t (a :: xs)
        let bs :=
          cyclicBandJumps n
            ((a :: xs).map Nat.floor)
        List.Forall₂ (· ≤ ·) qs bs ∧
        listPositiveCount qs = s ∧
        listPositiveCount bs = 4 ∧
        zeroPositiveMismatchCount qs bs = 4 - s ∧
        List.Forall₂
          (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
          qs bs := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun v => centreExponent (C v) t

  have hbad' :
      SaturationCollisionFailure P exponent i := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hbad
  have hactive4 :
      (active P i).card = 4 := by
    rw [hbad'.1]
    dsimp [exponent]
    rw [hexp]
    omega

  let R : CentreCutRayCycle hp (C i) c :=
    Classical.choice
      (exists_centreCutRayCycle hp (C i) c)

  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, R.normalizedValues t = a :: xs := by
    cases hv : R.normalizedValues t with
    | nil =>
        exact False.elim
          (R.normalizedValues_nonempty t hv)
    | cons a xs =>
        exact ⟨a, xs, hv⟩

  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 : 0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using
      R.normalizedValues_pairwise htpos.le
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).1
  have hallT :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2
  have htTop : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith

  let qs := linearCyclicGapQuotients t (a :: xs)
  let bs :=
    cyclicBandJumps n
      ((a :: xs).map Nat.floor)

  have hdom0 :=
    cyclicFloorGaps_le_cyclicBandJumps
      a xs n ha0 hsorted hallT htTop
  have hdom :
      List.Forall₂ (· ≤ ·) qs bs := by
    dsimp [qs, bs]
    simpa [linearCyclicGapQuotients,
      cyclicRealGapsAt] using hdom0

  have hocc4 :
      (occupiedNatBands (a :: xs)).card = 4 := by
    have hoccR :
        (occupiedNatBands
          (R.normalizedValues t)).card
          =
        (occupiedCutProjectiveBands
          hp t c n i).card :=
      R.occupiedNatBands_normalizedValues_card_eq_occupiedCut
        hp htpos hc0 hcpi n htop
    rw [hvalues] at hoccR
    have hactiveOcc :
        (active P i).card =
          (occupiedCutProjectiveBands hp t c n i).card := by
      dsimp [P]
      rw [cutProjectiveBandPartition_active_eq_occupied
        hp hcap htpos hlam hc0 hcpi n htop i]
    omega

  have hfloorSorted :
      ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) :=
    floorLabels_pairwise a xs hsorted
  have hfloorBound :
      ∀ q ∈ (a :: xs).map Nat.floor, q ≤ n := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx)
      ((hallT x hx).trans htTop)

  have hbandSupport :
      listPositiveCount bs = 4 := by
    have h :=
      cyclicBandJumps_positiveCount_eq_toFinset_card
        n (Nat.floor a) (xs.map Nat.floor)
        (by simpa using hfloorSorted)
        (by
          intro q hq
          exact hfloorBound q (by simpa using hq))
    have hfin :
        ((a :: xs).map Nat.floor).toFinset.card = 4 := by
      simpa [occupiedNatBands] using hocc4
    dsimp [bs]
    rw [h]
    exact hfin

  have hquotSupport :
      listPositiveCount qs = s := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical
        hp htpos
    rw [hsupport] at h
    dsimp [qs]
    simpa [CentreCutRayCycle.gapQuotients,
      hvalues] using h

  have hqExp :
      listExponent qs = n - 3 := by
    have h :=
      R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    dsimp [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients] at h
    simpa [qs, hvalues] using h

  have hbExp :
      listExponent bs = n - 3 := by
    have h :=
      cyclicBandJumps_exponent_eq_total_sub_distinct
        n (Nat.floor a) (xs.map Nat.floor)
        (by simpa using hfloorSorted)
        (by
          intro q hq
          exact hfloorBound q (by simpa using hq))
    have hfin :
        ((a :: xs).map Nat.floor).toFinset.card = 4 := by
      simpa [occupiedNatBands] using hocc4
    dsimp [bs]
    rw [h, hfin]
    omega

  have hexpLists :
      listExponent qs = listExponent bs := by
    rw [hqExp, hbExp]

  have hmismatch :
      zeroPositiveMismatchCount qs bs = 4 - s := by
    rw [mismatchCount_eq_sub_positiveCounts hdom,
        hbandSupport, hquotSupport]

  have hunit :
      List.Forall₂
        (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
        qs bs :=
    forall₂_mismatch_is_unit_of_exact_exponent
      hdom hexpLists

  exact ⟨R, a, xs, hvalues,
    hdom, hquotSupport, hbandSupport,
    hmismatch, hunit⟩

/-- Support-one, support-two, and support-three bad minima carry respectively
three, two, and one zero-quotient positive band jumps. -/
theorem cutSaturationBadAt_mismatch_count_by_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n s : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    (hexp :
      centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = s)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        zeroPositiveMismatchCount
          (linearCyclicGapQuotients t (a :: xs))
          (cyclicBandJumps n
            ((a :: xs).map Nat.floor))
          =
        4 - s := by
  obtain ⟨R, a, xs, hvalues,
      _hdom, _hqs, _hbs, hmismatch, _hunit⟩ :=
    cutSaturationBadAt_support_mismatch_data
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      i hexp hsupport hbad
  exact ⟨R, a, xs, hvalues, hmismatch⟩

#print axioms cutSaturationBadAt_support_mismatch_data
#print axioms cutSaturationBadAt_mismatch_count_by_support

end JSP000404Research
