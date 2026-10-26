import JSP000404Research.PlanarFourSixExactIntegerCapacity
import JSP000404Research.ThreeFiveNoTopWeight
import Mathlib.Tactic

/-!
# Original n=3 exact-integer geometry: at most TWO next-layer centres

For ANY number of actual original planar centres >=5, at exact t=3
the genuine AngleCap strict gaps rule out all k=2 exponents. Moreover,
each k=1 centre has EXACTLY ONE positive quotient, and ANY fourth
original centre has support at most two since its exponent is at least
n-3=0.

The original 4-centre transition-packing obstruction forbids three
different k=1 centres together with a fourth original centre.
Thus at most TWO real centres can have k=1, and:
    sum_{i} 2^k_i <= card V + 2.
This is a genuine geometric bound, not the complete dyadic
capacity for unbounded cardinality.

As unconditional concrete payoffs, at t=3:
* 5 genuine centres have total dyadic weight <=7 (stronger than 8),
* 6 genuine centres have total dyadic weight <=8 (the ORIGINAL target).

No nonreusing matching, translated hole, unused surplus or sorry enters
any theorem here.
-/

namespace JSP000404Research
open scoped BigOperators

/-- For any original planar configuration with at least five actual
centres satisfying AngleCap at the exact integer scale t=3, there
are at most TWO exponent-one centres. -/
theorem planar_three_integer_many_centres_next_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 5 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ((Finset.univ : Finset V).filter
      (fun i => centreExponent (C i) t = 1)).card ≤ 2 := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  let S1 : Finset V := Finset.univ.filter (fun i => k i = 1)
  have ht3 : t = 3 := by rw [hdeltaExact] at ht; linarith
  have hcard5 : (3 : ℕ) + 2 ≤ Fintype.card V := by omega
  change S1.card ≤ 2
  by_contra hnot
  have hthree : 3 ≤ S1.card := by omega
  obtain ⟨s,a,b,hs,ha,hb,hsa,hsb,hab⟩ :=
    exists_three_distinct_mem_of_card_ge_three S1 hthree
  have hks : k s = 1 := (Finset.mem_filter.mp hs).2
  have hka : k a = 1 := (Finset.mem_filter.mp ha).2
  have hkb : k b = 1 := (Finset.mem_filter.mp hb).2
  have htripcard : ({s,a,b} : Finset V).card = 3 := by
    simp [hsa, hsb, hab]
  have hFourth : ∃ c : V, c ∉ ({s,a,b} : Finset V) := by
    by_contra hnone
    have hall : (Finset.univ : Finset V) ⊆ {s,a,b} := by
      intro c _
      by_contra hcnot
      exact hnone ⟨c,hcnot⟩
    have hle := Finset.card_le_card hall
    simp only [Finset.card_univ, htripcard] at hle
    omega
  obtain ⟨c,hc⟩ := hFourth
  have hsc : s ≠ c := by
    intro h
    apply hc
    simp [h]
  have hac : a ≠ c := by
    intro h
    apply hc
    simp [h]
  have hbc : b ≠ c := by
    intro h
    apply hc
    simp [h]
  exact planar_integer_no_three_next_with_third_layer_companion
    hp hcap (by decide : 3 ≤ (3 : ℕ)) hcard5 ht3 hlam
    hsa hsb hsc hab hac hbc C
    (by simpa [k] using hks)
    (by simpa [k] using hka)
    (by simpa [k] using hkb)
    (by omega : (3 : ℕ) - 3 ≤ centreExponent (C c) t)

/-- Exact t=3 TRUE planar AngleCap configurations with >=5 actual
centres have dyadic weight at most (number of centres)+2. -/
theorem planar_three_integer_many_centres_dyadic_le_card_add_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 5 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) ≤
      Fintype.card V + 2 := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  have ht3 : t = 3 := by rw [hdeltaExact] at ht; linarith
  have hk : ∀ i : V, k i ≤ 1 := by
    intro i
    exact planar_exact_integer_many_centres_exponent_le_n_sub_two
      hp hcap (by decide : 2 ≤ (3 : ℕ))
      (by omega : (3 : ℕ) + 2 ≤ Fintype.card V) ht3 hlam i (C i)
  have hmass := zero_one_dyadic_sum_eq_card_add_ones k hk
  have hcnt : ((Finset.univ : Finset V).filter (fun i => k i = 1)).card ≤ 2 :=
    planar_three_integer_many_centres_next_card_le_two
      hp hcap hcard hdelta0 hdeltaHalf hdeltaExact ht hlam C
  omega

/-- New completely unconditional ORIGINAL n=3 SIX-point exact integer
dyadic capacity. The earlier five-point theorem was not sufficient
for this six-point geometric case. -/
theorem planar_three_six_exact_integer_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hdeltaExact : delta = 0)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) ≤ 8 := by
  have hbudget := planar_three_integer_many_centres_dyadic_le_card_add_two
    hp hcap (by omega : 5 ≤ Fintype.card V)
    hdelta0 hdeltaHalf hdeltaExact ht hlam C
  omega

#print axioms planar_three_integer_many_centres_next_card_le_two
#print axioms planar_three_integer_many_centres_dyadic_le_card_add_two
#print axioms planar_three_six_exact_integer_dyadic_capacity

end JSP000404Research
