import JSP000404Research.WeightedHanselSlice
import JSP000404Research.SixPointMergedEqualityRoot
import Mathlib.Tactic

/-!
# The two exceptional minima have the same active palette

In the exact six-point two-exception profile

  1,4,4,3,3,3,

the completed partial Boolean cubes tile the full n-cube.

Fix a colour c which is active at bad1 but not bad2.  The top root colour is
active at bad2, so c is not the root and is therefore free at the top.

Count the half-cube word(c)=false in units

  B = 2^(n-5).

All local contributions except bad2 are even multiples of B:

* top: c free, contribution 8B;
* bad1: c fixed, contribution 0 or 2B;
* each ordinary minimum: contribution 0, 2B, or 4B.

But bad2 has four specified coordinates and c is free, so it contributes
exactly B.  The full false half-cube has size 16B.  This is an odd/even
contradiction.

Thus active(bad1) is contained in active(bad2); symmetry gives equality.
-/

namespace JSP000404Research

open scoped BigOperators
open BinaryEdgePartition

theorem no_exclusive_colour_at_first_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn5 : 5 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3)
    (c : Fin n)
    (hc₁ : c ∈ active P bad₁)
    (hc₂ : c ∉ active P bad₂) :
    False := by
  classical
  have hn4 : 4 ≤ n := by omega
  have hexact :=
    six_point_two_min_exceptions_active_exact
      hn4 P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  obtain ⟨root, hrootTop, hrootAll, _hrootEdges,
      _hrootBad₁, _hrootBad₂, _hrootOther⟩ :=
    six_point_two_exception_root_factorization
      hn4 P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  have hcRoot : c ≠ root := by
    intro h
    subst c
    exact hc₂ (hrootAll bad₂ htb₂).1
  have hcTop : c ∉ active P top := by
    rw [hrootTop]
    simp [hcRoot]

  have hbij :=
    six_point_two_min_exceptions_completeWord_bijective
      hn4 P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  let F : V → ℕ :=
    fun v =>
      Fintype.card
        (FalseCompletionAt P.bit (active P) c v)
  let B : ℕ := 2 ^ (n - 5)

  have hpow4 :
      2 ^ (n - 4) = 2 * B := by
    have he : n - 4 = (n - 5) + 1 := by omega
    rw [he, pow_add]
    simp [B, Nat.mul_comm]
  have hpow3 :
      2 ^ (n - 3) = 4 * B := by
    have he : n - 3 = (n - 5) + 2 := by omega
    rw [he, pow_add]
    norm_num
    ring
  have hpow2 :
      2 ^ (n - 2) = 8 * B := by
    have he : n - 2 = (n - 5) + 3 := by omega
    rw [he, pow_add]
    norm_num
    ring
  have hpow1 :
      2 ^ (n - 1) = 16 * B := by
    have he : n - 1 = (n - 5) + 4 := by omega
    rw [he, pow_add]
    norm_num
    ring

  have hBad₂False : F bad₂ = B := by
    dsimp [F]
    rw [card_falseCompletionAt,
      dif_neg hc₂,
      Finset.card_insert_of_not_mem hc₂,
      hexact.2.2.1]
    have he : n - (4 + 1) = n - 5 := by omega
    rw [he]

  have hEven :
      ∀ v : V, v ≠ bad₂ →
        ∃ q : ℕ, F v = (2 * B) * q := by
    intro v hvb₂
    by_cases hvt : v = top
    · subst v
      dsimp [F]
      rw [card_falseCompletionAt,
        dif_neg hcTop,
        Finset.card_insert_of_not_mem hcTop,
        hexact.1]
      have he : n - (1 + 1) = n - 2 := by omega
      rw [he, hpow2]
      exact ⟨4, by ring⟩
    by_cases hvb₁ : v = bad₁
    · subst v
      dsimp [F]
      rw [card_falseCompletionAt, dif_pos hc₁]
      by_cases hb : P.bit bad₁ c = false
      · rw [if_pos hb, hexact.2.1, hpow4]
        exact ⟨1, by ring⟩
      · rw [if_neg hb]
        exact ⟨0, by simp⟩
    · have hcardV :
          (active P v).card = 3 :=
        hexact.2.2.2 v hvt hvb₁ hvb₂
      dsimp [F]
      by_cases hcv : c ∈ active P v
      · rw [card_falseCompletionAt, dif_pos hcv]
        by_cases hb : P.bit v c = false
        · rw [if_pos hb, hcardV, hpow3]
          exact ⟨2, by ring⟩
        · rw [if_neg hb]
          exact ⟨0, by simp⟩
      · rw [card_falseCompletionAt,
          dif_neg hcv,
          Finset.card_insert_of_not_mem hcv,
          hcardV]
        have he : n - (3 + 1) = n - 4 := by omega
        rw [he, hpow4]
        exact ⟨1, by ring⟩

  let q : V → ℕ :=
    fun v =>
      if h : v = bad₂ then 0
      else Classical.choose (hEven v h)

  have hq :
      ∀ v ∈ (Finset.univ.erase bad₂ : Finset V),
        F v = (2 * B) * q v := by
    intro v hv
    have hvne : v ≠ bad₂ :=
      (Finset.mem_erase.mp hv).1
    dsimp [q]
    rw [dif_neg hvne]
    exact Classical.choose_spec (hEven v hvne)

  let Q : ℕ :=
    ∑ v ∈ (Finset.univ.erase bad₂ : Finset V), q v

  have hrest :
      (∑ v ∈ (Finset.univ.erase bad₂ : Finset V), F v)
        =
      (2 * B) * Q := by
    calc
      (∑ v ∈ (Finset.univ.erase bad₂ : Finset V), F v)
          =
        ∑ v ∈ (Finset.univ.erase bad₂ : Finset V),
          (2 * B) * q v := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hq v hv
      _ = (2 * B) *
          (∑ v ∈ (Finset.univ.erase bad₂ : Finset V), q v) := by
            rw [Finset.mul_sum]
      _ = (2 * B) * Q := rfl

  have hslice :=
    false_slice_card_sum_eq
      P.bit (active P) c hbij

  have hsumDecomp :
      (∑ v : V, F v) =
        F bad₂ +
          ∑ v ∈ (Finset.univ.erase bad₂ : Finset V), F v := by
    rw [← Finset.sum_erase_add F (Finset.mem_univ bad₂)]
    simp [add_comm]

  have hmain :
      B + (2 * B) * Q = 16 * B := by
    rw [← hpow1]
    rw [← hslice]
    rw [hsumDecomp, hBad₂False, hrest]

  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hmul :
      (1 + 2 * Q) * B = 16 * B := by
    calc
      (1 + 2 * Q) * B
          = B + (2 * B) * Q := by ring
      _ = 16 * B := hmain
  have hcoef :
      1 + 2 * Q = 16 :=
    Nat.eq_of_mul_eq_mul_right hBpos hmul
  omega

/-- Equality rigidity: the two exceptional minima have exactly the same
active-coordinate set. -/
theorem six_point_two_min_exceptions_active_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn5 : 5 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3) :
    active P bad₁ = active P bad₂ := by
  classical
  apply Finset.Subset.antisymm
  · intro c hc₁
    by_contra hc₂
    exact no_exclusive_colour_at_first_bad
      hn5 P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
      c hc₁ hc₂
  · intro c hc₂
    by_contra hc₁
    exact no_exclusive_colour_at_first_bad
      hn5 P top bad₂ bad₁
      htb₂ htb₁ hb₁₂.symm hcard
      hTop hBad₂ hBad₁
      (by
        intro v hvt hvb₂ hvb₁
        exact hOther v hvt hvb₁ hvb₂)
      c hc₂ hc₁

#print axioms no_exclusive_colour_at_first_bad
#print axioms six_point_two_min_exceptions_active_eq

end JSP000404Research
