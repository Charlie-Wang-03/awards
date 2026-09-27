import JSP000404Research.CutActiveFloorEquiv
import JSP000404Research.CutSupportOneBadPalette
import Mathlib.Tactic

/-!
# Transporting a four-consecutive old palette across equal active sets

Suppose two centres use the same old cut-projective active palette.  If one
cut-sorted local value list has floor span exactly three, then so does the
other.

The proof uses the exact active-band/floor equivalence.  The first floor is
the minimum occupied band of a sorted local value list and the last floor is
the maximum.  Equality of active palettes therefore transports both extrema.

This is the equal-old-palette branch needed for the mixed support-one /
support-two-or-three two-bad terminal.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem floor_lt_n_add_one_of_normalizedValue_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {n : ℕ}
    (htop : t < (n + 1 : ℕ))
    {x : ℝ}
    (hx : x ∈ R.normalizedValues t) :
    Nat.floor x < n + 1 := by
  have hxBounds :=
    R.normalizedValues_mem_bounds ht hc0 hcpi hx
  exact (Nat.floor_lt hxBounds.1).2
    (hxBounds.2.trans (by simpa using htop))

theorem floor_head_le_floor_of_mem_sorted
    {a x : ℝ} {xs : List ℝ}
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hx : x ∈ a :: xs) :
    Nat.floor a ≤ Nat.floor x := by
  have hax :
      a ≤ x := by
    rcases hx with rfl | hx
    · rfl
    · exact (List.pairwise_cons.mp hsorted).1 x hx
  exact Nat.floor_mono hax

theorem floor_of_mem_le_floor_last_sorted
    {a x : ℝ} {xs : List ℝ}
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hx : x ∈ a :: xs) :
    Nat.floor x ≤ Nat.floor (xs.getLastD a) := by
  exact Nat.floor_mono
    (le_getLastD_of_mem_pairwise a xs hsorted hx)

/-- Equality of old active palettes transports exact floor-span three. -/
theorem normalized_floor_span_three_of_equal_active
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i j : V}
    (Ci : CentreProjectiveCycle hp i)
    (Cj : CentreProjectiveCycle hp j)
    (Ri : CentreCutRayCycle hp Ci c)
    (Rj : CentreCutRayCycle hp Cj c)
    {ai : ℝ} {xsi : List ℝ}
    (hvi : Ri.normalizedValues t = ai :: xsi)
    (hspanI :
      Nat.floor (xsi.getLastD ai) = Nat.floor ai + 3)
    (hactiveEq :
      active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop) i
        =
      active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop) j) :
    ∃ aj xsj,
      Rj.normalizedValues t = aj :: xsj ∧
      Nat.floor (xsj.getLastD aj) = Nat.floor aj + 3 := by
  obtain ⟨aj, xsj, hvj⟩ :
      ∃ aj xsj, Rj.normalizedValues t = aj :: xsj := by
    cases h : Rj.normalizedValues t with
    | nil =>
        exact False.elim (Rj.normalizedValues_nonempty t h)
    | cons a xs =>
        exact ⟨a, xs, h⟩

  have hsi :
      (ai :: xsi).Pairwise (· ≤ ·) := by
    simpa [hvi] using Ri.normalizedValues_pairwise ht.le
  have hsj :
      (aj :: xsj).Pairwise (· ≤ ·) := by
    simpa [hvj] using Rj.normalizedValues_pairwise ht.le

  have haiMem : ai ∈ Ri.normalizedValues t := by
    rw [hvi]; simp
  have hziMem :
      xsi.getLastD ai ∈ Ri.normalizedValues t := by
    rw [hvi]
    exact List.getLastD_mem_cons ai xsi
  have hajMem : aj ∈ Rj.normalizedValues t := by
    rw [hvj]; simp
  have hzjMem :
      xsj.getLastD aj ∈ Rj.normalizedValues t := by
    rw [hvj]
    exact List.getLastD_mem_cons aj xsj

  have haiTop :
      Nat.floor ai < n + 1 :=
    floor_lt_n_add_one_of_normalizedValue_mem
      Ri ht hc0 hcpi htop haiMem
  have hziTop :
      Nat.floor (xsi.getLastD ai) < n + 1 :=
    floor_lt_n_add_one_of_normalizedValue_mem
      Ri ht hc0 hcpi htop hziMem
  have hajTop :
      Nat.floor aj < n + 1 :=
    floor_lt_n_add_one_of_normalizedValue_mem
      Rj ht hc0 hcpi htop hajMem
  have hzjTop :
      Nat.floor (xsj.getLastD aj) < n + 1 :=
    floor_lt_n_add_one_of_normalizedValue_mem
      Rj ht hc0 hcpi htop hzjMem

  let biHead : Fin (n + 1) :=
    ⟨Nat.floor ai, haiTop⟩
  let biLast : Fin (n + 1) :=
    ⟨Nat.floor (xsi.getLastD ai), hziTop⟩
  let bjHead : Fin (n + 1) :=
    ⟨Nat.floor aj, hajTop⟩
  let bjLast : Fin (n + 1) :=
    ⟨Nat.floor (xsj.getLastD aj), hzjTop⟩

  have hbiHead :
      biHead ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    apply (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Ci Ri biHead).2
    exact ⟨ai, haiMem, rfl⟩
  have hbiLast :
      biLast ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    apply (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Ci Ri biLast).2
    exact ⟨xsi.getLastD ai, hziMem, rfl⟩
  have hbjHead :
      bjHead ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j := by
    apply (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Cj Rj bjHead).2
    exact ⟨aj, hajMem, rfl⟩
  have hbjLast :
      bjLast ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j := by
    apply (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Cj Rj bjLast).2
    exact ⟨xsj.getLastD aj, hzjMem, rfl⟩

  have hHeadJinI :
      bjHead ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    rw [hactiveEq]
    exact hbjHead
  obtain ⟨xHeadJ, hxHeadJMem, hxHeadJFloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Ci Ri bjHead).1 hHeadJinI
  have hmLeHeadJ :
      Nat.floor ai ≤ Nat.floor aj := by
    have hle :=
      floor_head_le_floor_of_mem_sorted hsi
        (by simpa [hvi] using hxHeadJMem)
    simpa [bjHead] using hxHeadJFloor ▸ hle

  have hHeadIinJ :
      biHead ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j := by
    rw [← hactiveEq]
    exact hbiHead
  obtain ⟨xHeadI, hxHeadIMem, hxHeadIFloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Cj Rj biHead).1 hHeadIinJ
  have hHeadJLeM :
      Nat.floor aj ≤ Nat.floor ai := by
    have hle :=
      floor_head_le_floor_of_mem_sorted hsj
        (by simpa [hvj] using hxHeadIMem)
    simpa [biHead] using hxHeadIFloor ▸ hle
  have hheadEq :
      Nat.floor aj = Nat.floor ai :=
    le_antisymm hHeadJLeM hmLeHeadJ

  have hLastJinI :
      bjLast ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    rw [hactiveEq]
    exact hbjLast
  obtain ⟨xLastJ, hxLastJMem, hxLastJFloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Ci Ri bjLast).1 hLastJinI
  have hLastJLeI :
      Nat.floor (xsj.getLastD aj) ≤
        Nat.floor (xsi.getLastD ai) := by
    have hle :=
      floor_of_mem_le_floor_last_sorted hsi
        (by simpa [hvi] using hxLastJMem)
    simpa [bjLast] using hxLastJFloor ▸ hle

  have hLastIinJ :
      biLast ∈ active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j := by
    rw [← hactiveEq]
    exact hbiLast
  obtain ⟨xLastI, hxLastIMem, hxLastIFloor⟩ :=
    (active_iff_exists_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop Cj Rj biLast).1 hLastIinJ
  have hLastILeJ :
      Nat.floor (xsi.getLastD ai) ≤
        Nat.floor (xsj.getLastD aj) := by
    have hle :=
      floor_of_mem_le_floor_last_sorted hsj
        (by simpa [hvj] using hxLastIMem)
    simpa [biLast] using hxLastIFloor ▸ hle
  have hlastEq :
      Nat.floor (xsj.getLastD aj) =
        Nat.floor (xsi.getLastD ai) :=
    le_antisymm hLastJLeI hLastILeJ

  refine ⟨aj, xsj, hvj, ?_⟩
  rw [hlastEq, hspanI, hheadEq]

#print axioms normalized_floor_span_three_of_equal_active

end JSP000404Research
