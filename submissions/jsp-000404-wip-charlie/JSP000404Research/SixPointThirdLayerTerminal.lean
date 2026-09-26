import JSP000404Research.MinimalOverweightKraftProfile
import JSP000404Research.SharpSecondLayerFourPlus
import Mathlib.Tactic

/-!
# Six-point rigidity of the large n-3 minimum layer with a top centre

In the one-child minimal-overweight situation, let the minimum exponent be
exactly n-3.  The exact overweight identity is

  sum_i 2^k_i = 2^n + 2^(n-3).

After dividing by 2^(n-3), every vertex contributes weight

  1  if k_i = n-3,
  2  if k_i = n-2,
  4  if k_i = n-1,

because all exponents are < n.

If a top n-1 centre exists and the ambient configuration has at least four
points, SharpSecondLayerFourPlus gives at most one n-2 companion.  If the
minimum layer has more than three vertices, parity already forces at least
five minima.  The normalized mass equation then leaves a unique possibility:

  five n-3 vertices, zero n-2 vertices, one n-1 vertex.

Hence the entire configuration has exactly six vertices.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Pure normalized dyadic arithmetic behind the six-point terminal. -/
theorem normalized_three_layer_profile_eq_six
    {V : Type*} [Fintype V]
    (k : V → ℕ)
    (n : ℕ)
    (hn : 3 ≤ n)
    (hexpLt : ∀ i : V, k i < n)
    (hmin : ∀ i : V, n - 3 ≤ k i)
    (s : V)
    (hTop : k s = n - 1)
    (hTopUnique :
      ∀ i : V, k i = n - 1 → i = s)
    (hSecond :
      ((Finset.univ : Finset V).filter
        (fun i => i ≠ s ∧ k i = n - 2)).card ≤ 1)
    (hMass :
      (∑ i : V, 2 ^ k i) =
        2 ^ n + 2 ^ (n - 3))
    (hMinCard :
      5 ≤
        ((Finset.univ : Finset V).filter
          (fun i => k i = n - 3)).card) :
    ((Finset.univ : Finset V).filter
        (fun i => k i = n - 3)).card = 5
      ∧
    ((Finset.univ : Finset V).filter
        (fun i => i ≠ s ∧ k i = n - 2)).card = 0
      ∧
    Fintype.card V = 6 := by
  classical
  let M : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => k i = n - 3)
  let S2 : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧ k i = n - 2)

  have hclass :
      ∀ i : V,
        k i = n - 3 ∨ k i = n - 2 ∨ k i = n - 1 := by
    intro i
    have hlo := hmin i
    have hhi := hexpLt i
    omega

  have hsNotM : s ∉ M := by
    simp [M, hTop]
    omega
  have hsNotS2 : s ∉ S2 := by
    simp [S2]

  have hdisjMS2 : Disjoint M S2 := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiM hiS
    have hm : k i = n - 3 := by simpa [M] using hiM
    have hs2 : k i = n - 2 := by
      exact (by simpa [S2] using hiS).2
    omega

  have huniv :
      (Finset.univ : Finset V) =
        insert s (M ∪ S2) := by
    ext i
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
      Finset.mem_union]
    by_cases his : i = s
    · exact Or.inl his
    · right
      rcases hclass i with hminI | hsecondI | htopI
      · exact Or.inl (by simp [M, hminI])
      · exact Or.inr (by simp [S2, his, hsecondI])
      · exact False.elim (his (hTopUnique i htopI))

  have hcard :
      Fintype.card V = 1 + M.card + S2.card := by
    rw [← Finset.card_univ]
    rw [huniv, Finset.card_insert_of_notMem]
    · rw [Finset.card_union_of_disjoint hdisjMS2]
      omega
    · simp [hsNotM, hsNotS2]

  have hpowN :
      2 ^ n = 8 * 2 ^ (n - 3) := by
    have hnEq : n = (n - 3) + 3 := by omega
    rw [hnEq, pow_add]
    norm_num
    ring

  have hweight :
      ∀ i : V,
        2 ^ k i =
          if i = s then 4 * 2 ^ (n - 3)
          else if i ∈ S2 then 2 * 2 ^ (n - 3)
          else 2 ^ (n - 3) := by
    intro i
    by_cases his : i = s
    · subst i
      simp [hTop, hpowN]
      have hsub : n - 1 = (n - 3) + 2 := by omega
      rw [hsub, pow_add]
      norm_num
      ring
    · have htopNe : k i ≠ n - 1 := by
        intro h
        exact his (hTopUnique i h)
      rcases hclass i with hminI | hsecondI | htopI
      · simp [his, S2, hminI]
      · have hiS2 : i ∈ S2 := by simp [S2, his, hsecondI]
        simp [his, hiS2, hsecondI]
        have hsub : n - 2 = (n - 3) + 1 := by omega
        rw [hsub, pow_add]
        norm_num
      · exact False.elim (htopNe htopI)

  have hMass' :
      (M.card + 2 * S2.card + 4) * 2 ^ (n - 3)
        =
      9 * 2 ^ (n - 3) := by
    have hsumClass :
        (∑ i : V, 2 ^ k i) =
          (M.card + 2 * S2.card + 4) *
            2 ^ (n - 3) := by
      rw [← Finset.sum_univ]
      rw [huniv]
      rw [Finset.sum_insert]
      · rw [Finset.sum_union hdisjMS2]
        simp only [Finset.sum_filter]
        have hMsum :
            ∑ i ∈ M, 2 ^ k i =
              M.card * 2 ^ (n - 3) := by
          apply Finset.sum_const_nat
          intro i hi
          have hiK : k i = n - 3 := by simpa [M] using hi
          rw [hiK]
        have hS2sum :
            ∑ i ∈ S2, 2 ^ k i =
              S2.card * (2 * 2 ^ (n - 3)) := by
          calc
            ∑ i ∈ S2, 2 ^ k i
                = ∑ _i ∈ S2, 2 * 2 ^ (n - 3) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    have hiK : k i = n - 2 := by
                      exact (by simpa [S2] using hi).2
                    have hsub : n - 2 = (n - 3) + 1 := by omega
                    rw [hiK, hsub, pow_add]
                    norm_num
            _ = S2.card * (2 * 2 ^ (n - 3)) := by
                    simp
        rw [hMsum, hS2sum]
        have hsPow :
            2 ^ k s = 4 * 2 ^ (n - 3) := by
          rw [hTop]
          have hsub : n - 1 = (n - 3) + 2 := by omega
          rw [hsub, pow_add]
          norm_num
          ring
        rw [hsPow]
        ring
      · simp [hsNotM, hsNotS2]
    rw [hsumClass] at hMass
    have hright :
        2 ^ n + 2 ^ (n - 3) =
          9 * 2 ^ (n - 3) := by
      rw [hpowN]
      ring
    rw [hright] at hMass
    exact hMass

  have hpos : 0 < 2 ^ (n - 3) := pow_pos (by norm_num) _
  have hEqNat :
      M.card + 2 * S2.card + 4 = 9 := by
    nlinarith

  have hM5 : M.card = 5 := by
    have hS2le : S2.card ≤ 1 := hSecond
    have hMge : 5 ≤ M.card := by simpa [M] using hMinCard
    omega
  have hS20 : S2.card = 0 := by
    omega
  have hcard6 : Fintype.card V = 6 := by
    rw [hcard, hM5, hS20]
  exact ⟨by simpa [M] using hM5,
    by simpa [S2] using hS20,
    hcard6⟩

/-- Geometric Sendov specialization.

The exact overweight identity is supplied by one bounded minimum deletion
column; the top-two multiplicity theorem removes any n-2 companion. -/
theorem large_n_sub_three_minimum_with_top_forces_six_points
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 4 ≤ Fintype.card V)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (r0 s : V)
    (hminExp : centreExponent (C r0) t = n - 3)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hS : centreExponent (C s) t = n - 1)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchildR0 :
      deletionPostWeight
          (concreteDeletionAfter C (by omega) t) r0
        ≤ 2 ^ n)
    (hminCard :
      5 ≤
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card) :
    (minimumExponentVertices
        (fun i => centreExponent (C i) t) r0).card = 5
      ∧
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 2)).card = 0
      ∧
    Fintype.card V = 6 := by
  classical
  let h3 : 3 ≤ Fintype.card V := by omega
  have hexpLe :
      ∀ i : V, centreExponent (C i) t ≤ n := by
    intro i
    have hdelta1 : delta < 1 := by linarith
    have hlt :=
      centreExponent_lt_n
        (C i) n delta t (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht
    omega
  have hrig :=
    concrete_minimum_deletion_rigidity_of_child_bound
      C h3 (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
      n r0 hexpLe hover hchildR0 hmin
  have hMass :
      (∑ i : V, 2 ^ centreExponent (C i) t)
        =
      2 ^ n + 2 ^ (n - 3) := by
    have hexcess := hrig.1
    rw [hminExp] at hexcess
    omega
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ i : V, centreExponent (C i) t < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hminLower :
      ∀ i : V, n - 3 ≤ centreExponent (C i) t := by
    intro i
    rw [← hminExp]
    exact hmin i
  have hTopUnique :
      ∀ i : V,
        centreExponent (C i) t = n - 1 → i = s := by
    intro i hi
    exact topExponent_eq_fixed_top
      hp hcap (by omega) (by omega)
      hdelta0 hdeltaHalf ht hlam C s i hS hi
  have hSecond :=
    secondLayer_companion_card_le_one_of_card_ge_four
      hp hcap hcard (by omega) hdelta0 hdeltaHalf
      ht hlam C s hS
  have hProfile :=
    normalized_three_layer_profile_eq_six
      (fun i => centreExponent (C i) t)
      n (by omega) hexpLt hminLower
      s hS hTopUnique hSecond hMass
      (by
        simpa [minimumExponentVertices, hminExp]
          using hminCard)
  have hMinSet :
      (minimumExponentVertices
        (fun i => centreExponent (C i) t) r0)
        =
      (Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 3) := by
    ext i
    simp [minimumExponentVertices, hminExp]
  rw [hMinSet]
  exact hProfile

#print axioms normalized_three_layer_profile_eq_six
#print axioms large_n_sub_three_minimum_with_top_forces_six_points

end JSP000404Research
