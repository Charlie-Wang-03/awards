import JSP000404Research.CutMergedTwoBadOldPaletteRigidity
import JSP000404Research.CutSupportOneBadPalette
import JSP000404Research.CutActiveFloorEquiv
import Mathlib.Tactic

/-!
# Floor-span lower bound in the support-one boundary-swap branch

Suppose bad centre i has support one.  Its old cut palette occupies four
consecutive bands, so its cut-sorted floor span is exactly three.

If the two bad old palettes are not equal but differ by the unique final-merge
boundary swap 0 <-> n, then the other bad centre j has a much larger cut floor
span:

* low-end swap:
    i contains 0 and not n, j contains n and not 0.
  Since i's span is three, its maximal floor is 3.  This interior band is also
  active at j, while j has top band n, so
      floor(last_j) - floor(first_j) >= n-3.

* high-end swap:
    i contains n and not 0, j contains 0 and not n.
  Symmetrically i's minimal floor is n-3; this interior band is active at j,
  while j has band zero, so again j's span is at least n-3.

This is the numerical entry point for ruling out the mixed-support boundary
swap.
-/

namespace JSP000404Research

open BinaryEdgePartition

/-- Active band zero forces the first floor of a sorted cut-value list to be
zero. -/
theorem first_floor_eq_zero_of_zero_active
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t) (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ) (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hzero :
      (0 : Fin (n + 1)) ∈
        active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop) i) :
    Nat.floor a = 0 := by
  obtain ⟨x, hx, hxfloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop C R
      (0 : Fin (n + 1))).1 hzero
  have hs :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise ht.le
  have hle :=
    floor_head_le_floor_of_mem_sorted hs
      (by simpa [hvalues] using hx)
  simpa using hle

/-- Active top band n forces the last floor of a sorted cut-value list to be
n. -/
theorem last_floor_eq_n_of_top_active
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t) (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ) (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (htopActive :
      Fin.last n ∈
        active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop) i) :
    Nat.floor (xs.getLastD a) = n := by
  obtain ⟨x, hx, hxfloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop C R
      (Fin.last n)).1 htopActive
  have hs :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise ht.le
  have hle :=
    floor_of_mem_le_floor_last_sorted hs
      (by simpa [hvalues] using hx)
  have hlastMem :
      xs.getLastD a ∈ R.normalizedValues t := by
    rw [hvalues]
    exact List.getLastD_mem_cons a xs
  have hlastTop :=
    floor_lt_n_add_one_of_normalizedValue_mem
      R ht hc0 hcpi htop hlastMem
  have hxn : Nat.floor x = n := by simpa using hxfloor
  rw [hxn] at hle
  omega

/-- An active interior band b bounds the first/last floors around b. -/
theorem floor_bounds_of_active_band
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t) (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ) (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (b : Fin (n + 1))
    (hb :
      b ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i) :
    Nat.floor a ≤ b.val ∧
      b.val ≤ Nat.floor (xs.getLastD a) := by
  obtain ⟨x, hx, hxfloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop C R b).1 hb
  have hs :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using R.normalizedValues_pairwise ht.le
  have hlo :=
    floor_head_le_floor_of_mem_sorted hs
      (by simpa [hvalues] using hx)
  have hhi :=
    floor_of_mem_le_floor_last_sorted hs
      (by simpa [hvalues] using hx)
  rw [hxfloor] at hlo hhi
  exact ⟨hlo,hhi⟩

/-- Low-end 0->n boundary swap from a support-one span-three centre forces
the other centre's floor span to be at least n-3. -/
theorem support_one_low_boundary_swap_other_span_ge
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t) (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {n : ℕ} (hn5 : 5 ≤ n)
    (htop : t < (n + 1 : ℕ))
    {i j : V}
    (Ci : CentreProjectiveCycle hp i)
    (Cj : CentreProjectiveCycle hp j)
    (Ri : CentreCutRayCycle hp Ci c)
    (Rj : CentreCutRayCycle hp Cj c)
    {ai aj : ℝ} {xsi xsj : List ℝ}
    (hvi : Ri.normalizedValues t = ai :: xsi)
    (hvj : Rj.normalizedValues t = aj :: xsj)
    (hspanI :
      Nat.floor (xsi.getLastD ai) = Nat.floor ai + 3)
    (hzeroI :
      (0 : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i)
    (htopJ :
      Fin.last n ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)
    (hinterior :
      ∀ b : Fin (n + 1),
        0 < b.val → b.val < n →
        (b ∈ active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i ↔
         b ∈ active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)) :
    n - 3 ≤
      Nat.floor (xsj.getLastD aj) - Nat.floor aj := by
  have hfirstI :=
    first_floor_eq_zero_of_zero_active
      hp hcap ht hlam hc0 hcpi n htop Ci Ri hvi hzeroI
  have hlastI : Nat.floor (xsi.getLastD ai) = 3 := by
    rw [hspanI, hfirstI]
  have h3lt : 3 < n := by omega
  let b3 : Fin (n + 1) := ⟨3, by omega⟩
  have hb3I :
      b3 ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    apply (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Ci Ri b3).2
    refine ⟨xsi.getLastD ai, ?_, ?_⟩
    · rw [hvi]
      exact List.getLastD_mem_cons ai xsi
    · simpa [b3] using hlastI
  have hb3J :
      b3 ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j :=
    (hinterior b3 (by simp [b3]) (by simpa [b3] using h3lt)).1 hb3I
  have hboundsJ :=
    floor_bounds_of_active_band
      hp hcap ht hlam hc0 hcpi n htop
      Cj Rj hvj b3 hb3J
  have hlastJ :=
    last_floor_eq_n_of_top_active
      hp hcap ht hlam hc0 hcpi n htop
      Cj Rj hvj htopJ
  rw [hlastJ]
  have hfirstLe3 : Nat.floor aj ≤ 3 := by
    simpa [b3] using hboundsJ.1
  omega

/-- High-end n->0 boundary swap has the same span lower bound. -/
theorem support_one_high_boundary_swap_other_span_ge
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t) (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {n : ℕ} (hn5 : 5 ≤ n)
    (htop : t < (n + 1 : ℕ))
    {i j : V}
    (Ci : CentreProjectiveCycle hp i)
    (Cj : CentreProjectiveCycle hp j)
    (Ri : CentreCutRayCycle hp Ci c)
    (Rj : CentreCutRayCycle hp Cj c)
    {ai aj : ℝ} {xsi xsj : List ℝ}
    (hvi : Ri.normalizedValues t = ai :: xsi)
    (hvj : Rj.normalizedValues t = aj :: xsj)
    (hspanI :
      Nat.floor (xsi.getLastD ai) = Nat.floor ai + 3)
    (htopI :
      Fin.last n ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i)
    (hzeroJ :
      (0 : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)
    (hinterior :
      ∀ b : Fin (n + 1),
        0 < b.val → b.val < n →
        (b ∈ active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i ↔
         b ∈ active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)) :
    n - 3 ≤
      Nat.floor (xsj.getLastD aj) - Nat.floor aj := by
  have hlastI :=
    last_floor_eq_n_of_top_active
      hp hcap ht hlam hc0 hcpi n htop Ci Ri hvi htopI
  have hfirstI : Nat.floor ai = n - 3 := by
    rw [hspanI] at hlastI
    omega
  have hn3pos : 0 < n - 3 := by omega
  have hn3lt : n - 3 < n := by omega
  let bm : Fin (n + 1) := ⟨n - 3, by omega⟩
  have hbmI :
      bm ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    apply (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Ci Ri bm).2
    refine ⟨ai, ?_, ?_⟩
    · rw [hvi]; simp
    · simpa [bm] using hfirstI
  have hbmJ :
      bm ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j :=
    (hinterior bm (by simpa [bm] using hn3pos)
      (by simpa [bm] using hn3lt)).1 hbmI
  have hboundsJ :=
    floor_bounds_of_active_band
      hp hcap ht hlam hc0 hcpi n htop Cj Rj hvj bm hbmJ
  have hfirstJ :=
    first_floor_eq_zero_of_zero_active
      hp hcap ht hlam hc0 hcpi n htop Cj Rj hvj hzeroJ
  rw [hfirstJ]
  have hlastGe : n - 3 ≤ Nat.floor (xsj.getLastD aj) := by
    simpa [bm] using hboundsJ.2
  omega

#print axioms support_one_low_boundary_swap_other_span_ge
#print axioms support_one_high_boundary_swap_other_span_ge

end JSP000404Research
