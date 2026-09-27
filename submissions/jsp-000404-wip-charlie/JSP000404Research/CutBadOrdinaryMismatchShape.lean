import JSP000404Research.CutSaturatedSupportMismatch
import JSP000404Research.CutSaturationTurnSlotBridge
import Mathlib.Tactic

/-!
# Ordinary-prefix mismatch shape at a saturation-bad cut centre

For a cut-sorted local value cycle

  a :: xs,

write the cyclic quotient/band-jump lists as

  qOrd ++ [qWrap],
  bOrd ++ [bWrap].

At a saturation collision failure the seam arithmetic gives qWrap >= 2.
Therefore the wrap coordinate is never a zero-quotient/positive-band mismatch.

Combining this with CutSaturatedSupportMismatch shows that all

  4 - positiveSupport

mismatches lie in the four ordinary cut steps.  Exact exponent equality also
forces every such ordinary mismatch to be exactly

  q = 0,  b = 1.

This is the ordered-palette shape needed for the remaining two-bad-minimum
pair analysis.
-/

namespace JSP000404Research

theorem zeroPositiveMismatchCount_append
    (qs₁ qs₂ bs₁ bs₂ : List ℕ)
    (hlen : qs₁.length = bs₁.length) :
    zeroPositiveMismatchCount (qs₁ ++ qs₂) (bs₁ ++ bs₂)
      =
    zeroPositiveMismatchCount qs₁ bs₁ +
      zeroPositiveMismatchCount qs₂ bs₂ := by
  induction qs₁ generalizing bs₁ with
  | nil =>
      have hnil : bs₁ = [] := by
        exact List.length_eq_zero.mp (by simpa using hlen.symm)
      subst bs₁
      simp [zeroPositiveMismatchCount]
  | cons q qs ih =>
      cases bs₁ with
      | nil =>
          simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp [zeroPositiveMismatchCount, ih bs hlen, add_assoc]

theorem zeroPositiveMismatchCount_singleton_of_q_ne_zero
    {q b : ℕ}
    (hq : q ≠ 0) :
    zeroPositiveMismatchCount [q] [b] = 0 := by
  simp [zeroPositiveMismatchCount, hq]

/-- Exact cyclic decomposition of the linear quotient list. -/
theorem linearCyclicGapQuotients_cons_decompose
    (t a : ℝ) (xs : List ℝ) :
    linearCyclicGapQuotients t (a :: xs)
      =
    (successiveDiffsFrom a xs).map Nat.floor ++
      [Nat.floor (a + t - xs.getLastD a)] := by
  rfl

/-- Exact cyclic decomposition of the integer band-jump list. -/
theorem cyclicBandJumps_map_floor_cons_decompose
    (n : ℕ) (a : ℝ) (xs : List ℝ) :
    cyclicBandJumps n ((a :: xs).map Nat.floor)
      =
    successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor) ++
      [(n + 1 - Nat.floor (xs.getLastD a)) + Nat.floor a] := by
  simp [cyclicBandJumps, map_getLastD_eq]

/-- At a saturation-bad exact n-3 centre, all mismatch positions are ordinary
(non-wrap), their number is 4-s, and every one is a unit band jump. -/
theorem cutSaturationBadAt_ordinary_mismatch_shape
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
        let qOrd := (successiveDiffsFrom a xs).map Nat.floor
        let bOrd :=
          successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)
        zeroPositiveMismatchCount qOrd bOrd = 4 - s ∧
        List.Forall₂
          (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
          qOrd bOrd := by
  obtain ⟨R, a, xs, hvalues,
      hdom, hqSupport, hbSupport,
      hmismatch, hunit⟩ :=
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
      centreExponent (C i) t + (BinaryEdgePartition.active P i).card =
        n + 1 := by
    simpa [exponent] using hbad'.1
  have hfail :
      ¬ ((0 : Fin (n + 1)) ∈ BinaryEdgePartition.active P i ∧
        Fin.last n ∈ BinaryEdgePartition.active P i) :=
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

  let qOrd := (successiveDiffsFrom a xs).map Nat.floor
  let bOrd :=
    successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)
  let qWrap := Nat.floor (a + t - xs.getLastD a)
  let bWrap :=
    (n + 1 - Nat.floor (xs.getLastD a)) + Nat.floor a

  have hqWrapPos : qWrap ≠ 0 := by
    dsimp [qWrap]
    omega

  have hqDecomp :
      linearCyclicGapQuotients t (a :: xs) =
        qOrd ++ [qWrap] := by
    dsimp [qOrd, qWrap]
    exact linearCyclicGapQuotients_cons_decompose t a xs

  have hbDecomp :
      cyclicBandJumps n ((a :: xs).map Nat.floor) =
        bOrd ++ [bWrap] := by
    dsimp [bOrd, bWrap]
    exact cyclicBandJumps_map_floor_cons_decompose n a xs

  have hlenOrd : qOrd.length = bOrd.length := by
    dsimp [qOrd, bOrd]
    rw [List.length_map]
    induction xs generalizing a with
    | nil => rfl
    | cons b bs ih =>
        simp [successiveDiffsFrom, successiveNatDiffsFrom, ih b]

  have hmismatchOrd :
      zeroPositiveMismatchCount qOrd bOrd = 4 - s := by
    rw [hqDecomp, hbDecomp,
      zeroPositiveMismatchCount_append qOrd [qWrap] bOrd [bWrap] hlenOrd,
      zeroPositiveMismatchCount_singleton_of_q_ne_zero hqWrapPos]
      at hmismatch
    simpa using hmismatch

  have hunitOrd :
      List.Forall₂
        (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
        qOrd bOrd := by
    rw [hqDecomp, hbDecomp] at hunit
    exact (List.forall₂_append_left_iff.mp hunit).1

  exact ⟨R, a, xs, hvalues,
    hmismatchOrd, hunitOrd⟩

theorem cutSaturationBadAt_support_two_ordinary_mismatch_count
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
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (C i) t) = 2)
    (hbad :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        zeroPositiveMismatchCount
          ((successiveDiffsFrom a xs).map Nat.floor)
          (successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor))
        = 2 := by
  obtain ⟨R,a,xs,hvalues,hmismatch,_hunit⟩ :=
    cutSaturationBadAt_ordinary_mismatch_shape
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hexp hsupport hbad
  exact ⟨R,a,xs,hvalues, by simpa using hmismatch⟩

theorem cutSaturationBadAt_support_three_ordinary_mismatch_count
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
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (C i) t) = 3)
    (hbad :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi i) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        zeroPositiveMismatchCount
          ((successiveDiffsFrom a xs).map Nat.floor)
          (successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor))
        = 1 := by
  obtain ⟨R,a,xs,hvalues,hmismatch,_hunit⟩ :=
    cutSaturationBadAt_ordinary_mismatch_shape
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hexp hsupport hbad
  exact ⟨R,a,xs,hvalues, by simpa using hmismatch⟩

#print axioms zeroPositiveMismatchCount_append
#print axioms cutSaturationBadAt_ordinary_mismatch_shape
#print axioms cutSaturationBadAt_support_two_ordinary_mismatch_count
#print axioms cutSaturationBadAt_support_three_ordinary_mismatch_count

end JSP000404Research
