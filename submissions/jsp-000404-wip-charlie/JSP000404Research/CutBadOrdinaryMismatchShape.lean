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

theorem forall₂_left_of_append_of_length
    {α β : Type*} {R : α → β → Prop}
    (xs ys : List α) (as bs : List β)
    (hlen : xs.length = as.length)
    (h :
      List.Forall₂ R (xs ++ ys) (as ++ bs)) :
    List.Forall₂ R xs as := by
  induction xs generalizing as with
  | nil =>
      have has : as = [] :=
        List.length_eq_zero.mp (by simpa using hlen.symm)
      subst as
      exact List.Forall₂.nil
  | cons x xs ih =>
      cases as with
      | nil =>
          simp at hlen
      | cons a as =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.cons_append] at h
          cases h with
          | cons hxa htail =>
              exact List.Forall₂.cons hxa
                (ih as hlen htail)

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
    exact forall₂_left_of_append_of_length
      qOrd [qWrap] bOrd [bWrap] hlenOrd hunit

  exact ⟨R, a, xs, hvalues,
    hmismatchOrd, hunitOrd⟩

theorem successiveDiffsFrom_length_for_bad_shape
    (a : ℝ) (xs : List ℝ) :
    (successiveDiffsFrom a xs).length = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs =>
      simp [successiveDiffsFrom,
        successiveDiffsFrom_length_for_bad_shape b bs]

theorem successiveNatDiffsFrom_length
    (a : ℕ) (xs : List ℕ) :
    (successiveNatDiffsFrom a xs).length = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs =>
      simp [successiveNatDiffsFrom,
        successiveNatDiffsFrom_length b bs]

/-- Complete ordinary-step count profile at a saturation-bad exact n-3
six-point minimum.  The four ordinary positions split into:
* s-1 positive quotient positions;
* 4-s zero-quotient positive-band unit mismatches;
* one remaining same-band position.
-/
theorem cutSaturationBadAt_ordinary_step_counts
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n s : ℕ}
    (hcardV : Fintype.card V = 6)
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
        qOrd.length = 4 ∧
        bOrd.length = 4 ∧
        List.Forall₂ (· ≤ ·) qOrd bOrd ∧
        listPositiveCount qOrd = s - 1 ∧
        listPositiveCount bOrd = 3 ∧
        zeroPositiveMismatchCount qOrd bOrd = 4 - s ∧
        List.Forall₂
          (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
          qOrd bOrd := by
  obtain ⟨R, a, xs, hvalues,
      hdom, hqSupport, _hbSupport,
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
      centreExponent (C i) t +
          (BinaryEdgePartition.active P i).card
        =
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

  have hRlen : R.rays.length = 5 := by
    obtain ⟨k, hk⟩ := R.rotation
    rw [hk, List.length_rotate,
      centreRayList_length_eq_five_of_card_six (C i) hcardV]
  have hvalsLen : (R.normalizedValues t).length = 5 := by
    simp [CentreCutRayCycle.normalizedValues, hRlen]
  have hxsLen : xs.length = 4 := by
    rw [hvalues] at hvalsLen
    simp at hvalsLen
    omega
  have hqLen : qOrd.length = 4 := by
    dsimp [qOrd]
    rw [List.length_map,
      successiveDiffsFrom_length_for_bad_shape,
      hxsLen]
  have hbLen : bOrd.length = 4 := by
    dsimp [bOrd]
    rw [successiveNatDiffsFrom_length,
      List.length_map, hxsLen]

  have hdomOrd :
      List.Forall₂ (· ≤ ·) qOrd bOrd := by
    rw [hqDecomp, hbDecomp] at hdom
    exact forall₂_left_of_append_of_length
      qOrd [qWrap] bOrd [bWrap]
      (by rw [hqLen, hbLen]) hdom

  have hqOrdSupport :
      listPositiveCount qOrd = s - 1 := by
    rw [hqDecomp, listPositiveCount_append] at hqSupport
    have hwrapOne :
        listPositiveCount [qWrap] = 1 := by
      exact listPositiveCount_singleton_of_pos
        (Nat.one_le_iff_ne_zero.mpr hqWrapPos)
    rw [hwrapOne] at hqSupport
    omega

  have hmismatchOrd :
      zeroPositiveMismatchCount qOrd bOrd = 4 - s := by
    rw [hqDecomp, hbDecomp,
      zeroPositiveMismatchCount_append qOrd [qWrap]
        bOrd [bWrap] (by rw [hqLen, hbLen]),
      zeroPositiveMismatchCount_singleton_of_q_ne_zero hqWrapPos]
      at hmismatch
    simpa using hmismatch

  have hbOrdSupport :
      listPositiveCount bOrd = 3 := by
    have hcount :=
      positiveCount_eq_add_mismatch_of_forall₂_le hdomOrd
    rw [hqOrdSupport, hmismatchOrd] at hcount
    have hsLe4 : s ≤ 4 := by
      have hmis0 : 0 ≤ zeroPositiveMismatchCount qOrd bOrd := Nat.zero_le _
      omega
    omega

  have hunitOrd :
      List.Forall₂
        (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
        qOrd bOrd := by
    rw [hqDecomp, hbDecomp] at hunit
    exact forall₂_left_of_append_of_length
      qOrd [qWrap] bOrd [bWrap]
      (by rw [hqLen, hbLen]) hunit

  exact ⟨R, a, xs, hvalues,
    hqLen, hbLen, hdomOrd,
    hqOrdSupport, hbOrdSupport,
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
