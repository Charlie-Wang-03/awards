import JSP000404Research.CutSaturatedSupportMismatch
import JSP000404Research.SaturatedSeamPhaseArithmetic
import Mathlib.Tactic

/-!
# Consecutive old-band palette at a support-one saturation-bad minimum

Let a cut-sorted exact n-3 minimum be saturation-bad and have quotient support
one.  The saturated seam arithmetic forces the cut-wrap quotient to be at
least two.  Since support is one, this wrap quotient is the unique positive
quotient.  The quotient identity

  exponent + positiveSupport = quotientSum

therefore gives

  q_wrap = (n-3)+1 = n-2.

Exact saturation also gives the wrap equality

  excess(q_wrap) =
    n - floor(last) + floor(first).

For n>=5 this becomes

  n-3 = n - floor(last) + floor(first),

hence

  floor(last) = floor(first) + 3.

The bad centre uses exactly four old cut bands.  Thus all four occupied labels
lie in the consecutive integer span from m=floor(first) through m+3; in
particular its old palette is a four-consecutive-band palette.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem list_sum_eq_member_of_positiveCount_one
    (qs : List ℕ) {q : ℕ}
    (hcount : listPositiveCount qs = 1)
    (hmem : q ∈ qs)
    (hq : q ≠ 0) :
    qs.sum = q := by
  induction qs with
  | nil =>
      simp at hmem
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        simp [listPositiveCount] at hcount
        simp only [List.sum_cons, zero_add]
        apply ih hcount
        · simpa using hmem
        · exact hq
      · have htailCount :
            listPositiveCount as = 0 := by
          simp [listPositiveCount, ha] at hcount
          omega
        have htailZero :
            ∀ x ∈ as, x = 0 :=
          (positiveCount_eq_zero_iff_all_zero as).1 htailCount
        have htailSum : as.sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          exact htailZero x hx
        simp only [List.mem_cons] at hmem
        rcases hmem with hqa | hqTail
        · subst q
          simp [htailSum]
        · have hq0 := htailZero q hqTail
          exact False.elim (hq hq0)

theorem le_getLastD_of_mem_pairwise
    {α : Type*} [LinearOrder α]
    (a : α) (xs : List α)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    {x : α}
    (hx : x ∈ a :: xs) :
    x ≤ xs.getLastD a := by
  induction xs generalizing a with
  | nil =>
      simp only [List.mem_singleton] at hx
      subst x
      simp
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hsorted
      simp only [List.mem_cons] at hx
      rcases hx with hxa | hxtail
      · subst x
        exact head_le_getLastD_of_pairwise a (b :: bs) hsorted
      · have htail :
            (b :: bs).Pairwise (· ≤ ·) :=
          hp.2
        have h :=
          ih b htail hxtail
        simpa [List.getLastD_cons] using h

/-- Main support-one bad-palette span theorem. -/
theorem cutSaturationBadAt_support_one_four_consecutive_band_span
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
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
      positiveSupport (centreQuotient (C i) t) = 1)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        (occupiedNatBands (a :: xs)).card = 4 ∧
        Nat.floor (xs.getLastD a) = Nat.floor a + 3 ∧
        (∀ q ∈ occupiedNatBands (a :: xs),
          Nat.floor a ≤ q ∧ q ≤ Nat.floor a + 3) := by
  obtain ⟨R, a, xs, hvalues,
      hdom, hqSupport, _hbSupport,
      _hmismatch, _hunit⟩ :=
    cutSaturationBadAt_support_mismatch_data
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      i hexp hsupport hbad

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
  have hsat :
      centreExponent (C i) t + (active P i).card = n + 1 := by
    simpa [exponent] using hbad'.1
  have hfail :
      ¬ ((0 : Fin (n + 1)) ∈ active P i ∧
        Fin.last n ∈ active P i) :=
    hbad'.2

  obtain ⟨a', xs', hvalues', hseam⟩ :=
    R.saturated_failure_has_wrap_unit_subslot_data
      hp hcap (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi (C i) R
      (by simpa [P, htop] using hsat)
      (by simpa [P, htop] using hfail)

  have hcons : a :: xs = a' :: xs' := by
    rw [← hvalues, hvalues']
  have haa : a = a' := (List.cons.inj hcons).1
  have hxx : xs = xs' := (List.cons.inj hcons).2
  subst a'
  subst xs'

  let z := xs.getLastD a
  let qWrap := Nat.floor (a + t - z)
  have hqWrap2 : 2 ≤ qWrap := by
    simpa [z, qWrap] using hseam.1

  let qs := linearCyclicGapQuotients t (a :: xs)
  have hqSupport' :
      listPositiveCount qs = 1 := by
    simpa [qs] using hqSupport
  have hqExp :
      listExponent qs = n - 3 := by
    have h :=
      R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    simpa [qs, CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using h
  have hqSum : qs.sum = n - 2 := by
    have hid := listExponent_add_listPositiveCount qs
    rw [hqExp, hqSupport'] at hid
    omega

  have hqWrapMem : qWrap ∈ qs := by
    dsimp [qs, qWrap, z]
    simp [linearCyclicGapQuotients]

  have hqWrapEq : qWrap = n - 2 := by
    have hsum :=
      list_sum_eq_member_of_positiveCount_one
        qs hqSupport' hqWrapMem (by omega)
    rw [hqSum] at hsum
    omega

  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using
      R.normalizedValues_pairwise htpos.le
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2

  have heqR :=
    R.local_band_equality_of_active_saturated
      hp hcap htpos hlam hc0 hcpi n htop
      (by simpa [P, htop] using hsat)
  have heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1 := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using heqR

  have htTop : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwrap :
      excess qWrap =
        n - Nat.floor z + Nat.floor a := by
    have h :=
      wrap_gap_excess_eq_outer_empty_of_global_equality
        a xs ha0 hsorted hall htTop heq
    simpa [qWrap, z] using h

  have hlastN :
      Nat.floor z ≤ n := by
    have hz0 :
        0 ≤ z :=
      ha0.trans (head_le_getLastD_of_pairwise a xs hsorted)
    have hzt :
        z < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact (hall z (List.getLastD_mem_cons a xs)).trans htTop
    have hf : Nat.floor z < n + 1 :=
      (Nat.floor_lt hz0).2 hzt
    omega

  have hfirstLast :
      Nat.floor a ≤ Nat.floor z :=
    Nat.floor_mono
      (head_le_getLastD_of_pairwise a xs hsorted)

  have hspan :
      Nat.floor z = Nat.floor a + 3 := by
    rw [hqWrapEq] at hwrap
    unfold excess at hwrap
    omega

  have hactive4 :
      (active P i).card = 4 := by
    rw [hbad'.1]
    dsimp [exponent]
    rw [hexp]
    omega
  have hoccR :
      (occupiedNatBands (R.normalizedValues t)).card =
        (occupiedCutProjectiveBands hp t c n i).card :=
    R.occupiedNatBands_normalizedValues_card_eq_occupiedCut
      hp htpos hc0 hcpi n htop
  have hactiveOcc :
      (active P i).card =
        (occupiedCutProjectiveBands hp t c n i).card := by
    dsimp [P]
    rw [cutProjectiveBandPartition_active_eq_occupied
      hp hcap htpos hlam hc0 hcpi n htop i]
  have hocc4 :
      (occupiedNatBands (a :: xs)).card = 4 := by
    rw [hvalues] at hoccR
    omega

  have hbounds :
      ∀ q ∈ occupiedNatBands (a :: xs),
        Nat.floor a ≤ q ∧ q ≤ Nat.floor a + 3 := by
    intro q hq
    rw [occupiedNatBands, List.mem_toFinset,
      List.mem_map] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hlo :=
      head_floor_le_of_mem_sorted hsorted hx
    have hxLast :
        x ≤ z := by
      dsimp [z]
      exact le_getLastD_of_mem_pairwise a xs hsorted hx
    have hhi :
        Nat.floor x ≤ Nat.floor z :=
      Nat.floor_mono hxLast
    rw [hspan] at hhi
    exact ⟨hlo, hhi⟩

  exact ⟨R, a, xs, hvalues, hocc4, hspan, hbounds⟩

#print axioms list_sum_eq_member_of_positiveCount_one
#print axioms le_getLastD_of_mem_pairwise
#print axioms cutSaturationBadAt_support_one_four_consecutive_band_span

end JSP000404Research
