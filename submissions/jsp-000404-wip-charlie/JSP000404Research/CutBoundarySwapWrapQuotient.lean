import JSP000404Research.CutSaturationTurnSlotBridge
import JSP000404Research.CyclicBandGapDomination
import Mathlib.Tactic

/-!
# Exact cut-wrap quotient from an n-1 floor span

At a saturation-bad cut centre, the cut-wrap quotient is at least two.

If the sorted cut-floor span is exactly n-1, then the corresponding cyclic
band-wrap jump is exactly two:

  (n+1-floor(last)) + floor(first) = 2.

The general floor-gap domination gives

  q_wrap <= band_wrap = 2,

so q_wrap=2.

This is the short arithmetic bridge needed in the support-one boundary-swap
branch, where the partner centre was already shown to have exact floor span
n-1.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem cutSaturationBadAt_wrap_quotient_eq_two_of_span_n_sub_one
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
    {i : V}
    (R : CentreCutRayCycle hp (C i) c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hspan :
      Nat.floor (xs.getLastD a) - Nat.floor a = n - 1)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i) :
    Nat.floor (a + t - xs.getLastD a) = 2 := by
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
          (active P i).card
        =
      n + 1 := by
    simpa [exponent] using hbad'.1
  have hfail :
      ¬ ((0 : Fin (n + 1)) ∈ active P i ∧
        Fin.last n ∈ active P i) := hbad'.2

  obtain ⟨a',xs',hvalues',hseam⟩ :=
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

  have hqLower :
      2 ≤ Nat.floor (a + t - xs.getLastD a) :=
    hseam.1

  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have hzMem :
      xs.getLastD a ∈ R.normalizedValues t := by
    rw [hvalues]
    exact List.getLastD_mem_cons a xs
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hzt :
      xs.getLastD a < t :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi hzMem).2
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using
      R.normalizedValues_pairwise htpos.le
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have htTopReal :
      t < (n : ℝ) + 1 := by
    rw [ht]
    linarith

  have hqUpper :
      Nat.floor (a + t - xs.getLastD a) ≤
        (n + 1 - Nat.floor (xs.getLastD a)) +
          Nat.floor a :=
    natFloor_wrap_le_band_wrap
      ha0 haz hzt htTopReal

  have hz0 : 0 ≤ xs.getLastD a := ha0.trans haz
  have hfloorLe :
      Nat.floor a ≤ Nat.floor (xs.getLastD a) :=
    Nat.floor_mono haz
  have hzN :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlt :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hz0).2
        (hzt.trans htTopReal)
    omega
  have hbandWrap :
      (n + 1 - Nat.floor (xs.getLastD a)) +
          Nat.floor a
        =
      2 := by
    omega

  rw [hbandWrap] at hqUpper
  omega

#print axioms cutSaturationBadAt_wrap_quotient_eq_two_of_span_n_sub_one

end JSP000404Research
