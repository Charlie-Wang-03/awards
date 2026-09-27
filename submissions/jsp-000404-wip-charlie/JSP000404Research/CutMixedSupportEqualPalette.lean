import JSP000404Research.CutEqualPaletteSpanTransfer
import JSP000404Research.CutBadFourConsecutiveStepShape
import JSP000404Research.CutBadOrdinaryMismatchShape
import Mathlib.Tactic

/-!
# Mixed-support rigidity under equal old palettes

Let bad1 be a support-one saturation-bad minimum and bad2 another exact n-3
saturation-bad minimum of support s in {2,3}.  If their old cut-projective
active palettes are equal, then:

1. support-one badness forces bad1's cut floor span to be exactly three;
2. active-palette equality transports the same span to bad2;
3. bad2's ordinary saturation step profile has exactly three positive band
   jumps;
4. therefore every ordinary band jump is 0 or 1, and every ordinary quotient
   is 0 or 1.

In particular every positive ordinary quotient at bad2 is exactly one.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem support_one_equal_palette_forces_other_ordinary_quotients_le_one
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
    {i j : V}
    (hExpI : centreExponent (C i) t = n - 3)
    (hExpJ : centreExponent (C j) t = n - 3)
    (hSupportI :
      positiveSupport (centreQuotient (C i) t) = 1)
    (hSupportJ :
      positiveSupport (centreQuotient (C j) t) = s)
    (hBadI :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i)
    (hBadJ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi j)
    (hactiveEq :
      active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) i
        =
      active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) j) :
    ∃ R : CentreCutRayCycle hp (C j) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        Nat.floor (xs.getLastD a) = Nat.floor a + 3 ∧
        let qOrd := (successiveDiffsFrom a xs).map Nat.floor
        let bOrd :=
          successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)
        qOrd.length = 4 ∧
        bOrd.length = 4 ∧
        List.Forall₂ (· ≤ ·) qOrd bOrd ∧
        listPositiveCount qOrd = s - 1 ∧
        listPositiveCount bOrd = 3 ∧
        (∀ q ∈ qOrd, q ≤ 1) := by
  obtain ⟨Ri, ai, xsi, hvi, _hocc4, hspanI, _hbounds⟩ :=
    cutSaturationBadAt_support_one_four_consecutive_band_span
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi i hExpI hSupportI hBadI

  obtain ⟨Rj, aj, xsj, hvj,
      hqLen, hbLen, hdom,
      hqPos, hbPos, _hmismatch, _hunit⟩ :=
    cutSaturationBadAt_ordinary_step_counts
      hp hcap C hcardV hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      j hExpJ hSupportJ hBadJ

  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith

  obtain ⟨aj', xsj', hvj', hspanJ'⟩ :=
    normalized_floor_span_three_of_equal_active
      hp hcap htpos hlam hc0 hcpi n htop
      (C i) (C j) Ri Rj hvi hspanI hactiveEq

  have hcons :
      aj :: xsj = aj' :: xsj' := by
    rw [← hvj, hvj']
  have haj : aj = aj' := (List.cons.inj hcons).1
  have hxs : xsj = xsj' := (List.cons.inj hcons).2
  subst aj'
  subst xsj'

  have hsorted :
      (aj :: xsj).Pairwise (· ≤ ·) := by
    simpa [hvj] using Rj.normalizedValues_pairwise htpos.le

  have hqLe :=
    (ordinary_step_shape_of_span_three
      aj xsj hsorted hspanJ' hdom hbPos).2

  exact ⟨Rj, aj, xsj, hvj, hspanJ',
    hqLen, hbLen, hdom, hqPos, hbPos, hqLe⟩

theorem support_one_equal_palette_other_positive_ordinary_eq_one
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
    {i j : V}
    (hExpI : centreExponent (C i) t = n - 3)
    (hExpJ : centreExponent (C j) t = n - 3)
    (hSupportI :
      positiveSupport (centreQuotient (C i) t) = 1)
    (hSupportJ :
      positiveSupport (centreQuotient (C j) t) = s)
    (hBadI :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i)
    (hBadJ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi j)
    (hactiveEq :
      active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) i
        =
      active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) j) :
    ∃ R : CentreCutRayCycle hp (C j) c,
      ∃ a : ℝ, ∃ xs : List ℝ,
        R.normalizedValues t = a :: xs ∧
        Nat.floor (xs.getLastD a) = Nat.floor a + 3 ∧
        ∀ q ∈ (successiveDiffsFrom a xs).map Nat.floor,
          q ≠ 0 → q = 1 := by
  obtain ⟨R,a,xs,hvalues,hspan,
      _hqLen,_hbLen,_hdom,_hqPos,_hbPos,hqLe⟩ :=
    support_one_equal_palette_forces_other_ordinary_quotients_le_one
      hp hcap C hcardV hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hExpI hExpJ hSupportI hSupportJ
      hBadI hBadJ hactiveEq
  refine ⟨R,a,xs,hvalues,hspan,?_⟩
  intro q hqmem hq0
  have hle := hqLe q hqmem
  omega

#print axioms support_one_equal_palette_forces_other_ordinary_quotients_le_one
#print axioms support_one_equal_palette_other_positive_ordinary_eq_one

end JSP000404Research
