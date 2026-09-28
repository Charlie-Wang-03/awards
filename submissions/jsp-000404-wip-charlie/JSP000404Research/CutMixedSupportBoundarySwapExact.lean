import JSP000404Research.CutMixedSupportBoundarySwapSpan
import JSP000404Research.FourBandIntervalRigidity
import Mathlib.Tactic

/-!
# Exact floor span in the support-one boundary-swap branch

A support-one saturation-bad centre occupies four consecutive old bands.

If its bad partner has the same merged palette but the old palettes differ by
the unique 0/n swap, then the partner's four old bands are exactly

  {1,2,3,n}          or          {0,n-3,n-2,n-1}.

Consequently its cut-sorted floor span is exactly n-1.

This strengthens the previous lower bound n-3 and is the numerical input for
the exact mixed-support quotient shapes.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem active_of_occupiedNatBand_value
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
    (q : ℕ)
    (hqBound : q < n + 1)
    (hq :
      q ∈ occupiedNatBands (a :: xs)) :
    (⟨q, hqBound⟩ : Fin (n + 1)) ∈
      active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
  have hmem :
      ∃ x ∈ R.normalizedValues t, Nat.floor x = q := by
    rw [hvalues]
    rw [occupiedNatBands, List.mem_toFinset,
      List.mem_map] at hq
    obtain ⟨x,hx,hfloor⟩ := hq
    exact ⟨x,hx,hfloor⟩
  exact
    (CentreCutRayCycle.active_of_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop
      C R ⟨q,hqBound⟩
      (by
        obtain ⟨x,hx,hfloor⟩ := hmem
        exact ⟨x,hx,by simpa using hfloor⟩))

/-- Low-end swap: support-one centre uses 0 but not n, partner uses n but
not 0.  The partner span is exactly n-1. -/
theorem support_one_low_boundary_swap_other_span_eq
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
    (hocc4 :
      (occupiedNatBands (ai :: xsi)).card = 4)
    (hspanI :
      Nat.floor (xsi.getLastD ai) = Nat.floor ai + 3)
    (hboundsI :
      ∀ q ∈ occupiedNatBands (ai :: xsi),
        Nat.floor ai ≤ q ∧ q ≤ Nat.floor ai + 3)
    (hzeroI :
      (0 : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i)
    (hzeroJ :
      (0 : Fin (n + 1)) ∉
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)
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
    Nat.floor (xsj.getLastD aj) - Nat.floor aj = n - 1 := by
  have hfirstI :=
    first_floor_eq_zero_of_zero_active
      hp hcap ht hlam hc0 hcpi n htop
      Ci Ri hvi hzeroI
  have hbounds0 :
      ∀ q ∈ occupiedNatBands (ai :: xsi),
        0 ≤ q ∧ q ≤ 3 := by
    intro q hq
    have h := hboundsI q hq
    rw [hfirstI] at h
    norm_num at h ⊢
    exact h
  have hinner :=
    finset_card_four_interval_three_inner_mem
      (occupiedNatBands (ai :: xsi)) 0 hocc4
      (by
        intro q hq
        have h := hbounds0 q hq
        simpa using h)
  have hband1I :
      (⟨1, by omega⟩ : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    exact active_of_occupiedNatBand_value
      hp hcap ht hlam hc0 hcpi n htop
      Ci Ri hvi 1 (by omega) (by simpa using hinner.1)
  have hband1J :
      (⟨1, by omega⟩ : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j :=
    (hinterior ⟨1,by omega⟩ (by simp) (by omega)).1 hband1I
  have hboundsJ :=
    floor_bounds_of_active_band
      hp hcap ht hlam hc0 hcpi n htop
      Cj Rj hvj ⟨1,by omega⟩ hband1J
  have hlastJ :=
    last_floor_eq_n_of_top_active
      hp hcap ht hlam hc0 hcpi n htop
      Cj Rj hvj htopJ
  have hfirstJpos : 1 ≤ Nat.floor aj := by
    by_contra hnot
    have hzero : Nat.floor aj = 0 := by omega
    have hmem :
        ∃ x ∈ Rj.normalizedValues t,
          Nat.floor x = (0 : Fin (n + 1)).val := by
      refine ⟨aj, ?_, ?_⟩
      · rw [hvj]; simp
      · simpa using hzero
    have hact :=
      CentreCutRayCycle.active_of_normalizedValue_floor
        hp hcap ht hlam hc0 hcpi n htop
        Cj Rj (0 : Fin (n + 1)) hmem
    exact hzeroJ hact
  have hfirstJle : Nat.floor aj ≤ 1 := by
    simpa using hboundsJ.1
  have hfirstJ : Nat.floor aj = 1 := by omega
  rw [hlastJ, hfirstJ]
  omega

/-- High-end swap: support-one centre uses n but not 0, partner uses 0 but
not n.  The partner span is exactly n-1. -/
theorem support_one_high_boundary_swap_other_span_eq
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
    (hocc4 :
      (occupiedNatBands (ai :: xsi)).card = 4)
    (hspanI :
      Nat.floor (xsi.getLastD ai) = Nat.floor ai + 3)
    (hboundsI :
      ∀ q ∈ occupiedNatBands (ai :: xsi),
        Nat.floor ai ≤ q ∧ q ≤ Nat.floor ai + 3)
    (htopI :
      Fin.last n ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i)
    (hzeroJ :
      (0 : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)
    (htopJ :
      Fin.last n ∉
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)
    (hinterior :
      ∀ b : Fin (n + 1),
        0 < b.val → b.val < n →
        (b ∈ active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i ↔
         b ∈ active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j)) :
    Nat.floor (xsj.getLastD aj) - Nat.floor aj = n - 1 := by
  have hlastI :=
    last_floor_eq_n_of_top_active
      hp hcap ht hlam hc0 hcpi n htop
      Ci Ri hvi htopI
  have hfirstI : Nat.floor ai = n - 3 := by
    rw [hspanI] at hlastI
    omega
  have hboundsM :
      ∀ q ∈ occupiedNatBands (ai :: xsi),
        n - 3 ≤ q ∧ q ≤ (n - 3) + 3 := by
    intro q hq
    have h := hboundsI q hq
    rw [hfirstI] at h
    exact h
  have hinner :=
    finset_card_four_interval_three_inner_mem
      (occupiedNatBands (ai :: xsi)) (n - 3)
      hocc4 hboundsM
  have hnm1 :
      n - 3 + 2 = n - 1 := by omega
  have hbandNm1I :
      (⟨n - 1, by omega⟩ : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) i := by
    have hm :
        n - 1 ∈ occupiedNatBands (ai :: xsi) := by
      rw [← hnm1]
      exact hinner.2
    exact active_of_occupiedNatBand_value
      hp hcap ht hlam hc0 hcpi n htop
      Ci Ri hvi (n - 1) (by omega) hm
  have hbandNm1J :
      (⟨n - 1, by omega⟩ : Fin (n + 1)) ∈
        active (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop) j :=
    (hinterior ⟨n - 1,by omega⟩ (by omega) (by omega)).1
      hbandNm1I
  have hboundsJ :=
    floor_bounds_of_active_band
      hp hcap ht hlam hc0 hcpi n htop
      Cj Rj hvj ⟨n - 1,by omega⟩ hbandNm1J
  have hfirstJ :=
    first_floor_eq_zero_of_zero_active
      hp hcap ht hlam hc0 hcpi n htop
      Cj Rj hvj hzeroJ
  have hlastJle : Nat.floor (xsj.getLastD aj) ≤ n - 1 := by
    have hlastMem :
        xsj.getLastD aj ∈ Rj.normalizedValues t := by
      rw [hvj]
      exact List.getLastD_mem_cons aj xsj
    have hlt :=
      floor_lt_n_add_one_of_normalizedValue_mem
        Rj ht hc0 hcpi htop hlastMem
    have hleN : Nat.floor (xsj.getLastD aj) ≤ n := by omega
    by_contra hnot
    have heqN : Nat.floor (xsj.getLastD aj) = n := by omega
    have hmem :
        ∃ x ∈ Rj.normalizedValues t,
          Nat.floor x = (Fin.last n).val := by
      refine ⟨xsj.getLastD aj, hlastMem, ?_⟩
      simpa using heqN
    have hact :=
      CentreCutRayCycle.active_of_normalizedValue_floor
        hp hcap ht hlam hc0 hcpi n htop
        Cj Rj (Fin.last n) hmem
    exact htopJ hact
  have hlastJge : n - 1 ≤ Nat.floor (xsj.getLastD aj) := by
    simpa using hboundsJ.2
  have hlastJ : Nat.floor (xsj.getLastD aj) = n - 1 := by omega
  rw [hfirstJ, hlastJ]
  omega

#print axioms support_one_low_boundary_swap_other_span_eq
#print axioms support_one_high_boundary_swap_other_span_eq

end JSP000404Research
