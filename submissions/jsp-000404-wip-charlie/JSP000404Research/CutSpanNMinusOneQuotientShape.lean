import JSP000404Research.CutBadOrdinaryMismatchShape
import JSP000404Research.CutSaturationTurnSlotBridge
import Mathlib.Tactic

/-!
# Quotient shape from an exact n-1 cut-floor span

At an exact n-3 saturation-bad centre with quotient support s, suppose the
cut-sorted occupied palette spans exactly n-1 floor units.

Saturation equality gives

  excess(qWrap) = n - floor(last) + floor(first) = 1.

Bad-seam arithmetic gives qWrap >= 2, hence qWrap = 2.

Since the full quotient sum is

  exponent + support = (n-3)+s,

the ordinary quotient list has

  sum = n-5+s
  positiveSupport = s-1.

This is the numerical core of the mixed-support boundary-swap branch.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem cutSaturationBadAt_span_n_sub_one_quotient_shape
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
        hc0 hcpi i)
    (R : CentreCutRayCycle hp (C i) c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hspan :
      Nat.floor (xs.getLastD a) - Nat.floor a = n - 1) :
    let qOrd := (successiveDiffsFrom a xs).map Nat.floor
    let qWrap := Nat.floor (a + t - xs.getLastD a)
    qWrap = 2 ∧
    qOrd.sum = n - 5 + s ∧
    listPositiveCount qOrd = s - 1 ∧
    R.gapQuotients t = qOrd ++ [qWrap] := by
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
  let qOrd := (successiveDiffsFrom a xs).map Nat.floor
  let qWrap := Nat.floor (a + t - z)

  have hqWrapGe : 2 ≤ qWrap := by
    simpa [qWrap, z] using hseam.1

  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise htpos.le
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

  have hfirstLast :
      Nat.floor a ≤ Nat.floor z :=
    Nat.floor_mono
      (head_le_getLastD_of_pairwise a xs hsorted)
  have hspanEq :
      Nat.floor z = Nat.floor a + (n - 1) := by
    dsimp [z] at hspan
    omega
  have houter : n - Nat.floor z + Nat.floor a = 1 := by
    have hzMem :
        z ∈ R.normalizedValues t := by
      rw [hvalues]
      exact List.getLastD_mem_cons a xs
    have hzlt :=
      floor_lt_n_add_one_of_normalizedValue_mem
        R htpos hc0 hcpi htop hzMem
    rw [hspanEq]
    omega
  have hqWrap : qWrap = 2 := by
    rw [houter] at hwrap
    unfold excess at hwrap
    omega

  have hdecomp :
      R.gapQuotients t = qOrd ++ [qWrap] := by
    unfold CentreCutRayCycle.gapQuotients
    rw [hvalues]
    simpa [qOrd, qWrap, z] using
      linearCyclicGapQuotients_cons_decompose t a xs

  have hfullSupport :
      listPositiveCount (R.gapQuotients t) = s := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical hp htpos
    rw [hsupport] at h
    exact h
  have hfullExp :
      listExponent (R.gapQuotients t) = n - 3 := by
    have h := R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    exact h
  have hfullSum :
      (R.gapQuotients t).sum = (n - 3) + s := by
    have hid :=
      listExponent_add_listPositiveCount
        (R.gapQuotients t)
    rw [hfullExp, hfullSupport] at hid
    omega

  have hqOrdSupport :
      listPositiveCount qOrd = s - 1 := by
    rw [hdecomp, listPositiveCount_append] at hfullSupport
    have htwo : listPositiveCount [qWrap] = 1 := by
      rw [hqWrap]
      norm_num [listPositiveCount]
    rw [htwo] at hfullSupport
    omega

  have hqOrdSum :
      qOrd.sum = n - 5 + s := by
    rw [hdecomp, List.sum_append] at hfullSum
    simp only [List.sum_singleton] at hfullSum
    rw [hqWrap] at hfullSum
    omega

  exact ⟨hqWrap, hqOrdSum, hqOrdSupport, hdecomp⟩

theorem cutSaturationBadAt_span_n_sub_one_support_two_shape
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
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V)
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (C i) t) = 2)
    (hbad :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi i)
    (R : CentreCutRayCycle hp (C i) c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hspan :
      Nat.floor (xs.getLastD a) - Nat.floor a = n - 1) :
    let qOrd := (successiveDiffsFrom a xs).map Nat.floor
    let qWrap := Nat.floor (a + t - xs.getLastD a)
    qWrap = 2 ∧ qOrd.sum = n - 3 ∧
    listPositiveCount qOrd = 1 := by
  obtain ⟨hwrap, hsum, hpos, _hdecomp⟩ :=
    cutSaturationBadAt_span_n_sub_one_quotient_shape
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hexp hsupport hbad R hvalues hspan
  exact ⟨hwrap, by simpa using hsum, by simpa using hpos⟩

theorem cutSaturationBadAt_span_n_sub_one_support_three_shape
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
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V)
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (C i) t) = 3)
    (hbad :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi i)
    (R : CentreCutRayCycle hp (C i) c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hspan :
      Nat.floor (xs.getLastD a) - Nat.floor a = n - 1) :
    let qOrd := (successiveDiffsFrom a xs).map Nat.floor
    let qWrap := Nat.floor (a + t - xs.getLastD a)
    qWrap = 2 ∧ qOrd.sum = n - 2 ∧
    listPositiveCount qOrd = 2 := by
  obtain ⟨hwrap, hsum, hpos, _hdecomp⟩ :=
    cutSaturationBadAt_span_n_sub_one_quotient_shape
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hexp hsupport hbad R hvalues hspan
  exact ⟨hwrap, by simpa using hsum, by simpa using hpos⟩

#print axioms cutSaturationBadAt_span_n_sub_one_quotient_shape
#print axioms cutSaturationBadAt_span_n_sub_one_support_two_shape
#print axioms cutSaturationBadAt_span_n_sub_one_support_three_shape

end JSP000404Research
