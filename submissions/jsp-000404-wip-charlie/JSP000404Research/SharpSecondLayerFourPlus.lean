import JSP000404Research.GeneralMixedContradiction
import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.TopTwoTailMultiplicity
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Sharp second-layer multiplicity for configurations of size at least four

With a fixed top centre s, two distinct n-2 companions can have support types

  (1,1), (2,2), (1,2), or (2,1).

The first case is ruled out by transition-arc packing, the second by the
sharp-pinned narrow-cluster theorem, and the mixed cases by
GeneralMixedContradiction once a fourth distinct point is available.

Hence for ambient cardinality at least four there is at most one n-2 companion
of a top n-1 centre.  Consequently the threshold n-3 exponent tail contains at
most two vertices total.
-/

namespace JSP000404Research

theorem exists_fourth_of_fintype_card_ge_four
    {V : Type*} [Fintype V]
    (hcard : 4 ≤ Fintype.card V)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b) :
    ∃ c : V, c ≠ s ∧ c ≠ a ∧ c ≠ b := by
  classical
  by_contra h
  push_neg at h
  have hsub :
      (Finset.univ : Finset V) ⊆ {s, a, b} := by
    intro x hx
    by_cases hxs : x = s
    · simp [hxs]
    by_cases hxa : x = a
    · simp [hxa]
    have hxb : x = b := by
      by_contra hxb
      exact h x hxs hxa hxb
    simp [hxb]
  have hle := Finset.card_le_card hsub
  have htri :
      ({s, a, b} : Finset V).card = 3 := by
    simp [hsa, hsb, hab, hsa.symm, hsb.symm, hab.symm]
  rw [Finset.card_univ, htri] at hle
  omega

theorem no_top_with_two_deficitTwo_companions_of_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 4 ≤ Fintype.card V)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hS : centreExponent (C s) t = n - 1)
    (hA : centreExponent (C a) t = n - 2)
    (hB : centreExponent (C b) t = n - 2) :
    False := by
  obtain ⟨c, hcs, hca, hcb⟩ :=
    exists_fourth_of_fintype_card_ge_four
      hcard hsa hsb hab
  have hsc : s ≠ c := hcs.symm
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  have hdelta1 : delta < 1 := by linarith
  have hs :
      SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      s (C s) hS
  have hsupA :=
    deficit_two_support_one_or_two_concrete
      (C a) hn hdelta0 hdeltaHalf ht hA
  have hsupB :=
    deficit_two_support_one_or_two_concrete
      (C b) hn hdelta0 hdeltaHalf ht hB
  rcases hsupA with hA1 | hA2 <;>
    rcases hsupB with hB1 | hB2
  · exact no_two_supportOne_deficitTwo_around_top
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab
      (C s) (C a) (C b)
      hS hA hB hA1 hB1
  · exact no_top_mixed_deficitTwo_with_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      (C s) (C a) (C b)
      hS hA hB hA1 hB2
  · exact no_top_mixed_deficitTwo_with_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsa hsc hab.symm hbc hac
      (C s) (C b) (C a)
      hS hB hA hB1 hA2
  · exact no_two_supportTwo_deficitTwo_around_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      hs (C a) (C b)
      hA hB hA2 hB2

/-- Relative to a fixed top centre, at most one other centre can occupy the
second exponent layer once the configuration has at least four points. -/
theorem secondLayer_companion_card_le_one_of_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 4 ≤ Fintype.card V)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hS : centreExponent (C s) t = n - 1) :
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 2)).card ≤ 1 := by
  classical
  let S : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 2)
  by_contra hnot
  have hgt : 1 < S.card := by omega
  rcases (Finset.one_lt_card.mp hgt) with
    ⟨a, ha, b, hb, hab⟩
  have ha' :
      a ≠ s ∧ centreExponent (C a) t = n - 2 := by
    simpa [S] using ha
  have hb' :
      b ≠ s ∧ centreExponent (C b) t = n - 2 := by
    simpa [S] using hb
  exact no_top_with_two_deficitTwo_companions_of_card_ge_four
    hp hcap hcard hn hdelta0 hdeltaHalf ht hlam C
    ha'.1.symm hb'.1.symm hab
    hS ha'.2 hb'.2

/-- The top-two exponent tail is comb-optimal in every configuration with at
least four points and a top centre. -/
theorem topTwo_tailCount_le_two_of_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 4 ≤ Fintype.card V)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hS : centreExponent (C s) t = n - 1) :
    tailCount
      (fun i => centreExponent (C i) t)
      (n - 3) ≤ 2 := by
  classical
  let T : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => n - 3 < centreExponent (C i) t)
  let S2 : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 2)
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ i : V, centreExponent (C i) t < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t
      (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hsub : T ⊆ insert s S2 := by
    intro i hi
    have hiTail :
        n - 3 < centreExponent (C i) t := by
      simpa [T] using hi
    have hiLt := hexpLt i
    have hcases :
        centreExponent (C i) t = n - 1 ∨
          centreExponent (C i) t = n - 2 := by
      omega
    rcases hcases with htop | hsecond
    · have his :
          i = s :=
        topExponent_eq_fixed_top
          hp hcap (by omega : 3 ≤ Fintype.card V)
          hn hdelta0 hdeltaHalf
          ht hlam C s i hS htop
      simp [his]
    · have his : i ≠ s := by
        intro hisEq
        subst i
        rw [hS] at hsecond
        omega
      simp [S2, his, hsecond]
  have hcardS2 :
      S2.card ≤ 1 :=
    secondLayer_companion_card_le_one_of_card_ge_four
      hp hcap hcard hn hdelta0 hdeltaHalf
      ht hlam C s hS
  have hcardT :
      T.card ≤ 2 := by
    have hmono := Finset.card_le_card hsub
    have hins :
        (insert s S2).card ≤ S2.card + 1 :=
      Finset.card_insert_le s S2
    omega
  unfold tailCount
  simpa [T] using hcardT

#print axioms exists_fourth_of_fintype_card_ge_four
#print axioms no_top_with_two_deficitTwo_companions_of_card_ge_four
#print axioms secondLayer_companion_card_le_one_of_card_ge_four
#print axioms topTwo_tailCount_le_two_of_card_ge_four

end JSP000404Research
