import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.CentreExponentBounds
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Top-two tail bound in the presence of a top centre

Fix a centre s with exponent n-1 in the lower branch.

* Another exponent n-1 centre is impossible as soon as the ambient finite
  configuration has at least three points: both would be sharp, and any third
  point contradicts two_sharp_no_third_small_delta.
* There are at most two exponent n-2 companions by
  secondLayer_companion_card_le_two.

Since every exponent is strictly below n, the threshold n-3 tail can contain
only the top layer n-1 and the second layer n-2.  Therefore

  tailCount k (n-3) <= 3.

This is the second profile-level tail inequality available for arbitrary
finite configurations with a top centre.
-/

namespace JSP000404Research

theorem exists_third_of_fintype_card_ge_three
    {V : Type*} [Fintype V]
    (hcard : 3 ≤ Fintype.card V)
    {a b : V} (hab : a ≠ b) :
    ∃ c : V, c ≠ a ∧ c ≠ b := by
  classical
  by_contra h
  push_neg at h
  have hsub :
      (Finset.univ : Finset V) ⊆ {a,b} := by
    intro x hx
    have hx' := h x
    rcases hx' with hxa | hxb
    · simp [hxa]
    · simp [hxb]
  have hle :=
    Finset.card_le_card hsub
  have hpair : ({a,b} : Finset V).card = 2 :=
    Finset.card_pair hab
  rw [Finset.card_univ, hpair] at hle
  omega

theorem topExponent_eq_fixed_top
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 3 ≤ Fintype.card V)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s i : V)
    (hS : centreExponent (C s) t = n - 1)
    (hI : centreExponent (C i) t = n - 1) :
    i = s := by
  by_contra his
  obtain ⟨c, hci, hcs⟩ :=
    exists_third_of_fintype_card_ge_three
      hcard his
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsSharp :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      s (C s) hS
  have hiSharp :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      i (C i) hI
  exact two_sharp_no_third_small_delta
    hp hcap hdeltaHalf hlampos
    his.symm hcs.symm hci.symm
    hsSharp hiSharp

theorem topTwo_tailCount_le_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 3 ≤ Fintype.card V)
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
      (n - 3) ≤ 3 := by
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
          hp hcap hcard hn hdelta0 hdeltaHalf
          ht hlam C s i hS htop
      simp [his]
    · have his : i ≠ s := by
        intro hisEq
        subst i
        rw [hS] at hsecond
        omega
      simp [S2, his, hsecond]
  have hcardS2 :
      S2.card ≤ 2 := by
    exact secondLayer_companion_card_le_two
      hp hcap hn hdelta0 hdeltaHalf ht hlam C s hS
  have hcardT :
      T.card ≤ 3 := by
    have hmono := Finset.card_le_card hsub
    have hins :
        (insert s S2).card ≤ S2.card + 1 :=
      Finset.card_insert_le s S2
    omega
  unfold tailCount
  simpa [T] using hcardT

#print axioms exists_third_of_fintype_card_ge_three
#print axioms topExponent_eq_fixed_top
#print axioms topTwo_tailCount_le_three

end JSP000404Research
