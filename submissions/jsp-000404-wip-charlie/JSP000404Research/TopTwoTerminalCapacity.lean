
import JSP000404Research.ExactMinimumLayerReduction
import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.TopTwoTailMultiplicity
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# The terminal exact-witness branch cannot have minimum exponent n-2

Suppose every centre exponent is at least n-2.  Since every exponent is
strictly below n in the lower branch, all centres lie in the top two layers
n-2 and n-1.

If the n-2 layer has cardinality at most three, then:

* with no top centre, all vertices lie in the n-2 layer, so total dyadic mass
  is at most 3*2^(n-2) < 2^n;
* with a top centre s, s is unique and
  SharpSecondLayerMultiplicity gives at most two n-2 companions, so total mass
  is at most 2^(n-1)+2*2^(n-2)=2^n.

In the exact-witness terminal branch the minimum layer is contained in the
three witness vertices, so its cardinality is at most three.  Therefore an
overweight terminal configuration must have minimum exponent at most n-3.
-/

namespace JSP000404Research

open scoped BigOperators

def secondExponentLayer
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (n : ℕ) : Finset V :=
  Finset.univ.filter fun i => exponent i = n - 2

@[simp] theorem mem_secondExponentLayer
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (n : ℕ) (i : V) :
    i ∈ secondExponentLayer exponent n ↔
      exponent i = n - 2 := by
  simp [secondExponentLayer]

theorem three_mul_pow_n_sub_two_le_pow_n
    {n : ℕ} (hn : 2 ≤ n) :
    3 * 2 ^ (n - 2) ≤ 2 ^ n := by
  have hnEq : n = (n - 2) + 2 := by omega
  rw [hnEq, pow_add]
  norm_num
  omega

theorem pow_n_sub_one_add_two_mul_pow_n_sub_two_eq_pow_n
    {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 1) + 2 * 2 ^ (n - 2) = 2 ^ n := by
  have h1 : n - 1 = (n - 2) + 1 := by omega
  have hnEq : n = (n - 2) + 2 := by omega
  rw [h1, hnEq, pow_add, pow_add]
  norm_num
  ring

/-- Pure two-layer capacity once the second layer is small, with the geometric
top-centre theorem supplying the stronger cardinality in the top-present
case. -/
theorem top_two_layer_capacity_of_second_card_le_three
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
    (hlower :
      ∀ i : V, n - 2 ≤ centreExponent (C i) t)
    (hsecond :
      (secondExponentLayer
        (fun i => centreExponent (C i) t) n).card ≤ 3) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  have hdelta1 : delta < 1 := by linarith
  have hlt :
      ∀ i : V, centreExponent (C i) t < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t
      (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  by_cases htop :
      ∃ s : V, centreExponent (C s) t = n - 1
  · obtain ⟨s, hs⟩ := htop
    have hunique :
        ∀ i : V,
          centreExponent (C i) t = n - 1 → i = s := by
      intro i hi
      exact topExponent_eq_fixed_top
        hp hcap hcard hn hdelta0 hdeltaHalf
        ht hlam C s i hs hi
    have hother :
        ∀ i : V, i ≠ s →
          centreExponent (C i) t = n - 2 := by
      intro i his
      have hlo := hlower i
      have hhi := hlt i
      have hcases :
          centreExponent (C i) t = n - 2 ∨
          centreExponent (C i) t = n - 1 := by
        omega
      rcases hcases with hsecondEq | htopEq
      · exact hsecondEq
      · exact False.elim (his (hunique i htopEq))
    let S :
        Finset V :=
      (Finset.univ : Finset V).erase s
    have hScard : S.card ≤ 2 := by
      have hcomp :=
        secondLayer_companion_card_le_two
          hp hcap hn hdelta0 hdeltaHalf
          ht hlam C s hs
      have hset :
          S =
          (Finset.univ : Finset V).filter
            (fun i => i ≠ s ∧
              centreExponent (C i) t = n - 2) := by
        ext i
        simp [S]
        constructor
        · intro his
          exact ⟨his, hother i his⟩
        · intro hi
          exact hi.1
      rw [hset]
      exact hcomp
    have hsumS :
        (∑ i ∈ S, 2 ^ centreExponent (C i) t)
          =
        S.card * 2 ^ (n - 2) := by
      calc
        (∑ i ∈ S, 2 ^ centreExponent (C i) t)
            =
          ∑ _i ∈ S, 2 ^ (n - 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            have his : i ≠ s := by
              simpa [S] using hi
            rw [hother i his]
        _ = S.card * 2 ^ (n - 2) := by
          simp [Nat.mul_comm]
    have hsumSBound :
        (∑ i ∈ S, 2 ^ centreExponent (C i) t)
          ≤
        2 * 2 ^ (n - 2) := by
      rw [hsumS]
      exact Nat.mul_le_mul_right _ hScard
    have hsplit :
        (∑ i : V, 2 ^ centreExponent (C i) t)
          =
        2 ^ centreExponent (C s) t +
          ∑ i ∈ S, 2 ^ centreExponent (C i) t := by
      have hadd :=
        Finset.add_sum_erase
          (Finset.univ : Finset V)
          (fun i => 2 ^ centreExponent (C i) t)
          (Finset.mem_univ s)
      simpa [S] using hadd.symm
    rw [hsplit, hs]
    exact (Nat.add_le_add_left hsumSBound _).trans_eq
      (pow_n_sub_one_add_two_mul_pow_n_sub_two_eq_pow_n
        (by omega : 2 ≤ n))
  · have hallSecond :
        ∀ i : V, centreExponent (C i) t = n - 2 := by
      intro i
      have hlo := hlower i
      have hhi := hlt i
      have hcases :
          centreExponent (C i) t = n - 2 ∨
          centreExponent (C i) t = n - 1 := by
        omega
      rcases hcases with h | h
      · exact h
      · exact False.elim (htop ⟨i, h⟩)
    have hsecondUniv :
        secondExponentLayer
            (fun i => centreExponent (C i) t) n
          =
        (Finset.univ : Finset V) := by
      ext i
      simp [secondExponentLayer, hallSecond i]
    have hcardV :
        Fintype.card V ≤ 3 := by
      rw [hsecondUniv] at hsecond
      simpa using hsecond
    have hsum :
        (∑ i : V, 2 ^ centreExponent (C i) t)
          =
        Fintype.card V * 2 ^ (n - 2) := by
      calc
        (∑ i : V, 2 ^ centreExponent (C i) t)
            =
          ∑ _i : V, 2 ^ (n - 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hallSecond i]
        _ = Fintype.card V * 2 ^ (n - 2) := by
          simp [Nat.mul_comm]
    rw [hsum]
    calc
      Fintype.card V * 2 ^ (n - 2)
          ≤ 3 * 2 ^ (n - 2) :=
        Nat.mul_le_mul_right _ hcardV
      _ ≤ 2 ^ n :=
        three_mul_pow_n_sub_two_le_pow_n
          (by omega : 2 ≤ n)

/-- Exact-witness terminal specialization. -/
theorem exactWitness_terminal_capacity_if_minimum_n_sub_two
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
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (r0 : V)
    (hminEq :
      centreExponent (C r0) t = n - 2)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hsub :
      minimumExponentVertices
          (fun i => centreExponent (C i) t) r0
        ⊆ exactWitnessTriple W) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hlower :
      ∀ i : V, n - 2 ≤ centreExponent (C i) t := by
    intro i
    rw [← hminEq]
    exact hmin i
  have hsecondSub :
      secondExponentLayer
          (fun i => centreExponent (C i) t) n
        ⊆ exactWitnessTriple W := by
    intro i hi
    have hiEq :
        centreExponent (C i) t = n - 2 :=
      (mem_secondExponentLayer
        (fun j => centreExponent (C j) t) n i).1 hi
    apply hsub
    apply (mem_minimumExponentVertices
      (fun j => centreExponent (C j) t) r0 i).2
    rw [hminEq, hiEq]
  have hsecondCard :
      (secondExponentLayer
        (fun i => centreExponent (C i) t) n).card ≤ 3 := by
    exact (Finset.card_le_card hsecondSub).trans_eq
      (exactWitnessTriple_card_eq_three W)
  exact top_two_layer_capacity_of_second_card_le_three
    hp hcap hcard hn hdelta0 hdeltaHalf ht hlam C
    hlower hsecondCard

/-- Therefore an overweight terminal branch cannot have minimum exponent
n-2. -/
theorem exactWitness_terminal_minimum_ne_n_sub_two_of_overweight
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
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (r0 : V)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hsub :
      minimumExponentVertices
          (fun i => centreExponent (C i) t) r0
        ⊆ exactWitnessTriple W)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    centreExponent (C r0) t ≠ n - 2 := by
  intro hminEq
  have hcapDyadic :=
    exactWitness_terminal_capacity_if_minimum_n_sub_two
      hp hcap hcard hn hdelta0 hdeltaHalf
      ht hlam W C r0 hminEq hmin hsub
  omega

#print axioms top_two_layer_capacity_of_second_card_le_three
#print axioms exactWitness_terminal_capacity_if_minimum_n_sub_two
#print axioms exactWitness_terminal_minimum_ne_n_sub_two_of_overweight

end JSP000404Research
