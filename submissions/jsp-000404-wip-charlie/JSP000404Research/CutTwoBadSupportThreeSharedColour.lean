import JSP000404Research.CutSupportThreeBadSmallAngle
import JSP000404Research.CutMergedTwoBadActiveRigidity
import JSP000404Research.CutMergedRepeatedSmallAngle
import Mathlib.Tactic

/-!
# Shared merged colour for two support-three bad minima

In the exact two-bad branch the two exceptional minima have the same merged
active palette.  After deleting the unique top root colour, this common
palette has cardinality three.

A support-three saturation-bad minimum supplies a delta-small adjacent-band
pair.  The sharp top is not an endpoint of that pair.  Therefore the two
incident merged colours both avoid the root.  They are also distinct: the old
cut-band labels are consecutive, and saturation-badness makes the final 0/n
merge injective on that old local palette.

Thus each support-three bad minimum selects a two-element subset of the same
three-element reduced palette.  Two such subsets must intersect.  This file
packages that shared-colour coupling.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem two_pairs_in_card_three_intersect
    {α : Type*} [DecidableEq α]
    (S : Finset α)
    (hcard : S.card = 3)
    {a b c d : α}
    (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b)
    (hcd : c ≠ d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨hac, had, hbc, hbd⟩
  have hsub : ({a, b, c, d} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hfour : ({a, b, c, d} : Finset α).card = 4 := by
    simp [hab, hac, had, hbc, hbd, hcd]
  have hle := Finset.card_le_card hsub
  rw [hfour, hcard] at hle
  omega

theorem uncovered_cut_two_bad_support_three_share_small_pair_colour
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
    (hcardV : Fintype.card V = 6)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hTopExp :
      centreExponent (C top) t = n - 1)
    (hMinExp :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupport₁ :
      positiveSupport (centreQuotient (C bad₁) t) = 3)
    (hsupport₂ :
      positiveSupport (centreQuotient (C bad₂) t) = 3)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (hTopSafe :
      ¬ CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi top)
    (hBad₁ :
      CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad₁)
    (hBad₂ :
      CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad₂)
    (hOtherSafe :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ¬ CutSaturationBadAt
            hp hcap C htpos hlam ht hdelta0
            (by linarith : delta < 1)
            hc0 hcpi v) :
    let M :=
      uncoveredCutMergedPartition
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered
    ∃ u₁ v₁ : OtherVertex bad₁,
      ∃ u₂ v₂ : OtherVertex bad₂,
        u₁ ≠ v₁ ∧
        u₂ ≠ v₂ ∧
        u₁.1 ≠ top ∧ v₁.1 ≠ top ∧
        u₂.1 ≠ top ∧ v₂.1 ≠ top ∧
        EuclideanGeometry.angle
            (p u₁.1) (p bad₁) (p v₁.1)
          ≤ delta * lam ∧
        EuclideanGeometry.angle
            (p u₂.1) (p bad₂) (p v₂.1)
          ≤ delta * lam ∧
        (
          localIncidentColor M bad₁ u₁.1 =
              localIncidentColor M bad₂ u₂.1
          ∨
          localIncidentColor M bad₁ u₁.1 =
              localIncidentColor M bad₂ v₂.1
          ∨
          localIncidentColor M bad₁ v₁.1 =
              localIncidentColor M bad₂ u₂.1
          ∨
          localIncidentColor M bad₁ v₁.1 =
              localIncidentColor M bad₂ v₂.1
        ) := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
  let exponent : V → ℕ :=
    fun v => centreExponent (C v) t

  obtain ⟨hSharp, root, _hrootTop, _hrootAll,
      hrootEdges, hrootBad₁, _hrootBad₂, _hrootOther,
      _tu₁, _tu₂, _htu₁, _htu₂, _htuNe,
      _htuBad₁, _htuBad₂⟩ :=
    uncovered_cut_two_bad_minima_rigidity
      hp hcap C (by omega : 4 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcardV
      top bad₁ bad₂ htb₁ htb₂ hb₁₂
      hTopExp hMinExp huncovered
      hTopSafe hBad₁ hBad₂ hOtherSafe

  have hExp₁ :
      centreExponent (C bad₁) t = n - 3 :=
    hMinExp bad₁ htb₁.symm
  have hExp₂ :
      centreExponent (C bad₂) t = n - 3 :=
    hMinExp bad₂ htb₂.symm

  obtain ⟨u₁, v₁, huv₁, hu₁Top, hv₁Top,
      hband₁, hsmall₁⟩ :=
    cutSaturationBadAt_support_three_small_pair_avoids_sharp
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi htb₁ hSharp hExp₁ hsupport₁ hBad₁

  obtain ⟨u₂, v₂, huv₂, hu₂Top, hv₂Top,
      hband₂, hsmall₂⟩ :=
    cutSaturationBadAt_support_three_small_pair_avoids_sharp
      hp hcap C hn5 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi htb₂ hSharp hExp₂ hsupport₂ hBad₂

  have hBad₁' :
      SaturationCollisionFailure P exponent bad₁ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₁
  have hBad₂' :
      SaturationCollisionFailure P exponent bad₂ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₂

  let a₁ : Fin n := localIncidentColor M bad₁ u₁.1
  let b₁ : Fin n := localIncidentColor M bad₁ v₁.1
  let a₂ : Fin n := localIncidentColor M bad₂ u₂.1
  let b₂ : Fin n := localIncidentColor M bad₂ v₂.1

  have ha₁Mem :
      a₁ ∈ (active M bad₁).erase root := by
    apply Finset.mem_erase.mpr
    constructor
    · exact localIncidentColor_ne_root_of_nonTop
        M htb₁.symm hu₁Top u₁.2.symm hrootEdges
    · exact localIncidentColor_mem_active M u₁.2.symm
  have hb₁Mem :
      b₁ ∈ (active M bad₁).erase root := by
    apply Finset.mem_erase.mpr
    constructor
    · exact localIncidentColor_ne_root_of_nonTop
        M htb₁.symm hv₁Top v₁.2.symm hrootEdges
    · exact localIncidentColor_mem_active M v₁.2.symm
  have ha₂Mem0 :
      a₂ ∈ (active M bad₂).erase root := by
    apply Finset.mem_erase.mpr
    constructor
    · exact localIncidentColor_ne_root_of_nonTop
        M htb₂.symm hu₂Top u₂.2.symm hrootEdges
    · exact localIncidentColor_mem_active M u₂.2.symm
  have hb₂Mem0 :
      b₂ ∈ (active M bad₂).erase root := by
    apply Finset.mem_erase.mpr
    constructor
    · exact localIncidentColor_ne_root_of_nonTop
        M htb₂.symm hv₂Top v₂.2.symm hrootEdges
    · exact localIncidentColor_mem_active M v₂.2.symm

  have hActiveEq :
      active M bad₁ = active M bad₂ := by
    simpa [M] using
      uncovered_cut_two_bad_minima_active_eq
        hp hcap C hn5 htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi hcardV
        top bad₁ bad₂ htb₁ htb₂ hb₁₂
        hTopExp hMinExp huncovered
        hTopSafe hBad₁ hBad₂ hOtherSafe

  have ha₂Mem :
      a₂ ∈ (active M bad₁).erase root := by
    rw [hActiveEq]
    exact ha₂Mem0
  have hb₂Mem :
      b₂ ∈ (active M bad₁).erase root := by
    rw [hActiveEq]
    exact hb₂Mem0

  have hOldNe₁ :
      localIncidentColor P bad₁ u₁.1 ≠
        localIncidentColor P bad₁ v₁.1 := by
    intro heq
    have hv := congrArg Fin.val heq
    have huVal :
        (localIncidentColor P bad₁ u₁.1).val =
          Nat.floor
            (cutNormalizedRayTheta hp t c bad₁ u₁) := by
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop u₁.2.symm]
      simpa using
        cutProjectiveBandColor_val
          hp htpos hc0 hcpi n htop u₁.2.symm
    have hvVal :
        (localIncidentColor P bad₁ v₁.1).val =
          Nat.floor
            (cutNormalizedRayTheta hp t c bad₁ v₁) := by
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop v₁.2.symm]
      simpa using
        cutProjectiveBandColor_val
          hp htpos hc0 hcpi n htop v₁.2.symm
    rw [huVal, hvVal] at hv
    omega

  have hOldNe₂ :
      localIncidentColor P bad₂ u₂.1 ≠
        localIncidentColor P bad₂ v₂.1 := by
    intro heq
    have hv := congrArg Fin.val heq
    have huVal :
        (localIncidentColor P bad₂ u₂.1).val =
          Nat.floor
            (cutNormalizedRayTheta hp t c bad₂ u₂) := by
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop u₂.2.symm]
      simpa using
        cutProjectiveBandColor_val
          hp htpos hc0 hcpi n htop u₂.2.symm
    have hvVal :
        (localIncidentColor P bad₂ v₂.1).val =
          Nat.floor
            (cutNormalizedRayTheta hp t c bad₂ v₂) := by
      rw [localIncidentColor_cutProjective_eq
        hp hcap htpos hlam hc0 hcpi n htop v₂.2.symm]
      simpa using
        cutProjectiveBandColor_val
          hp htpos hc0 hcpi n htop v₂.2.symm
    rw [huVal, hvVal] at hv
    omega

  have hab₁ : a₁ ≠ b₁ := by
    intro hab
    have hmerge :
        mergeLastColor (by omega : 1 ≤ n)
            (localIncidentColor P bad₁ u₁.1)
          =
        mergeLastColor (by omega : 1 ≤ n)
            (localIncidentColor P bad₁ v₁.1) := by
      rw [← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₁ u₁.1,
        ← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₁ v₁.1]
      exact hab
    have holdEq :=
      mergeLastColor_injOn_of_not_both_boundary
        (by omega : 1 ≤ n)
        (active P bad₁) hBad₁'.2
        (localIncidentColor_mem_active P u₁.2.symm)
        (localIncidentColor_mem_active P v₁.2.symm)
        hmerge
    exact hOldNe₁ holdEq

  have hab₂ : a₂ ≠ b₂ := by
    intro hab
    have hmerge :
        mergeLastColor (by omega : 1 ≤ n)
            (localIncidentColor P bad₂ u₂.1)
          =
        mergeLastColor (by omega : 1 ≤ n)
            (localIncidentColor P bad₂ v₂.1) := by
      rw [← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₂ u₂.1,
        ← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₂ v₂.1]
      exact hab
    have holdEq :=
      mergeLastColor_injOn_of_not_both_boundary
        (by omega : 1 ≤ n)
        (active P bad₂) hBad₂'.2
        (localIncidentColor_mem_active P u₂.2.symm)
        (localIncidentColor_mem_active P v₂.2.symm)
        hmerge
    exact hOldNe₂ holdEq

  have hintersect :
      a₁ = a₂ ∨ a₁ = b₂ ∨ b₁ = a₂ ∨ b₁ = b₂ :=
    two_pairs_in_card_three_intersect
      ((active M bad₁).erase root)
      hrootBad₁
      ha₁Mem hb₁Mem ha₂Mem hb₂Mem hab₁ hab₂

  refine ⟨u₁, v₁, u₂, v₂,
    huv₁, huv₂, hu₁Top, hv₁Top, hu₂Top, hv₂Top,
    hsmall₁, hsmall₂, ?_⟩
  simpa [a₁, b₁, a₂, b₂] using hintersect

#print axioms two_pairs_in_card_three_intersect
#print axioms uncovered_cut_two_bad_support_three_share_small_pair_colour

end JSP000404Research
