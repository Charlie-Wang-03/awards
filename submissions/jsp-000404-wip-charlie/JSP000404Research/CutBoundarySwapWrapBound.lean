import JSP000404Research.CutSaturatedPositiveStepTight
import JSP000404Research.CutBadOrdinaryMismatchShape
import Mathlib.Tactic

/-!
# Wrap quotient bound from a large ordinary floor span

At an exact saturation-bad minimum, ordinary positive quotient steps are
exactly band-tight, while every q=0 positive band mismatch contributes exactly
one band unit.

Hence for the ordinary step lists

  sum(bOrd) = sum(qOrd) + mismatchCount.

For an exact n-3 centre of support s, mismatchCount=4-s and the full cyclic
quotient sum is (n-3)+s.  If the ordinary floor span is at least n-3, then

  sum(qOrd) >= n+s-7,

so the wrap quotient is at most four.

This is the key numerical consequence of the mixed-support boundary-swap
branch.
-/

namespace JSP000404Research

theorem sum_band_eq_sum_q_add_mismatch
    {qs bs : List ℕ}
    (hdom : List.Forall₂ (· ≤ ·) qs bs)
    (htight :
      List.Forall₂
        (fun q b => q ≠ 0 → q = b)
        qs bs)
    (hunit :
      List.Forall₂
        (fun q b => q = 0 ∧ b ≠ 0 → b = 1)
        qs bs) :
    bs.sum =
      qs.sum + zeroPositiveMismatchCount qs bs := by
  induction hdom generalizing htight hunit with
  | nil =>
      simp [zeroPositiveMismatchCount]
  | @cons q b qs bs hqb hrest ih =>
      cases htight with
      | cons htightHead htightTail =>
        cases hunit with
        | cons hunitHead hunitTail =>
          have hi := ih htightTail hunitTail
          by_cases hq0 : q = 0
          · subst q
            by_cases hb0 : b = 0
            · subst b
              simp [zeroPositiveMismatchCount, hi]
            · have hb1 := hunitHead ⟨rfl, hb0⟩
              subst b
              simp [zeroPositiveMismatchCount, hi]
          · have hqbEq := htightHead hq0
            subst b
            simp [zeroPositiveMismatchCount, hq0, hi]

/-- Ordinary band jumps telescope to the first/last floor span. -/
theorem ordinary_band_jump_sum_eq_floor_span
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    (successiveNatDiffsFrom (Nat.floor a)
      (xs.map Nat.floor)).sum =
    Nat.floor (xs.getLastD a) - Nat.floor a := by
  have hfloorSorted :
      (Nat.floor a :: xs.map Nat.floor).Pairwise (· ≤ ·) := by
    have h :=
      hsorted.imp (fun _ _ hxy => Nat.floor_mono hxy)
    simpa using h
  rw [successiveNatDiffsFrom_sum_eq_last_sub_first
    (Nat.floor a) (xs.map Nat.floor) hfloorSorted]
  rw [map_getLastD_eq]

/-- If a bad exact n-3 centre has ordinary floor span at least n-3, its cut
wrap quotient is at most four. -/
theorem cutSaturationBadAt_wrap_quotient_le_four_of_span_ge
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
    (hexp : centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = s)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i)
    (hspan :
      ∀ R a xs,
        R.normalizedValues t = a :: xs →
        n - 3 ≤ Nat.floor (xs.getLastD a) - Nat.floor a) :
    ∃ R : CentreCutRayCycle hp (C i) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        Nat.floor (a + t - xs.getLastD a) ≤ 4 := by
  obtain ⟨R,a,xs,hvalues,
      hqLen,hbLen,hdom,hqPos,hbPos,hmismatch,hunit⟩ :=
    cutSaturationBadAt_ordinary_step_counts
      hp hcap C hcardV hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      i hexp hsupport hbad

  obtain ⟨R',a',xs',hvalues',htight⟩ :=
    cutSaturationBadAt_positive_ordinary_steps_band_tight
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      i hexp hsupport hbad

  have hlistEq :
      a :: xs = a' :: xs' := by
    rw [← hvalues, hvalues']
  have haa : a = a' := (List.cons.inj hlistEq).1
  have hxx : xs = xs' := (List.cons.inj hlistEq).2
  subst a'
  subst xs'

  -- Both chosen cut cycles enumerate the same sorted values, so the ordinary
  -- tightness statement transfers to the first witness.
  have hvaluesRR :
      R.normalizedValues t = R'.normalizedValues t := by
    rw [hvalues, hvalues']
  have hRaysValues :
      (successiveDiffsFrom a xs).map Nat.floor =
        (successiveDiffsFrom a xs).map Nat.floor := rfl
  have htightOrd :
      List.Forall₂
        (fun q b => q ≠ 0 → q = b)
        ((successiveDiffsFrom a xs).map Nat.floor)
        (successiveNatDiffsFrom (Nat.floor a)
          (xs.map Nat.floor)) := by
    exact htight

  let qOrd := (successiveDiffsFrom a xs).map Nat.floor
  let bOrd :=
    successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)
  let qWrap := Nat.floor (a + t - xs.getLastD a)

  have hbandSum :
      bOrd.sum = qOrd.sum + (4 - s) := by
    have hsum :=
      sum_band_eq_sum_q_add_mismatch
        hdom htightOrd hunit
    rw [hmismatch] at hsum
    simpa [qOrd,bOrd] using hsum

  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise htpos.le
  have hbSpan :
      bOrd.sum =
        Nat.floor (xs.getLastD a) - Nat.floor a := by
    dsimp [bOrd]
    exact ordinary_band_jump_sum_eq_floor_span a xs hsorted
  have hspan0 := hspan R a xs hvalues

  have hqOrdLower :
      n + s - 7 ≤ qOrd.sum := by
    rw [hbSpan] at hbandSum
    omega

  have hfullSupport :
      listPositiveCount
        (linearCyclicGapQuotients t (a :: xs)) = s := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical hp htpos
    rw [hsupport] at h
    simpa [CentreCutRayCycle.gapQuotients, hvalues] using h
  have hfullExp :
      listExponent
        (linearCyclicGapQuotients t (a :: xs)) = n - 3 := by
    have h := R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using h
  have hfullSum :
      (linearCyclicGapQuotients t (a :: xs)).sum =
        (n - 3) + s := by
    have hid :=
      listExponent_add_listPositiveCount
        (linearCyclicGapQuotients t (a :: xs))
    rw [hfullExp,hfullSupport] at hid
    exact hid.symm

  have hdecomp :
      linearCyclicGapQuotients t (a :: xs) =
        qOrd ++ [qWrap] := by
    dsimp [qOrd,qWrap]
    exact linearCyclicGapQuotients_cons_decompose t a xs
  rw [hdecomp, List.sum_append] at hfullSum
  simp only [List.sum_singleton] at hfullSum

  have hqWrapLe : qWrap ≤ 4 := by
    omega
  exact ⟨R,a,xs,hvalues,by simpa [qWrap] using hqWrapLe⟩

#print axioms sum_band_eq_sum_q_add_mismatch
#print axioms ordinary_band_jump_sum_eq_floor_span
#print axioms cutSaturationBadAt_wrap_quotient_le_four_of_span_ge

end JSP000404Research
