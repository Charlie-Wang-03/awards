
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualUnsafeEdgeBudget
import Mathlib.Tactic

/-!
# Through colours force higher-band cross diagonals

Work in the standard residual colouring of DirectionData of width < n+1.

Suppose a<u<v<w, the middle edge u--v is residual, and the two outer edges
a--u and v--w have the same retained colour c.

Write

  x = value(a,u),  y = value(u,v),  z = value(v,w).

Then x,z lie in the same unit band [c,c+1), while y>=n.

The diagonal A=value(a,v) lies between x and y.  The triple a<v<w also says
A and z are separated by at least one unit.  Since x,z differ by less than
one unit, A cannot lie below z-1; hence A>=z+1>=c+1.

Symmetrically B=value(u,w)>=x+1>=c+1.

Thus every through colour c on a residual edge forces both cross diagonals
into strictly higher direction bands.  This is the geometric ladder hidden
behind the purely combinatorial through-colour credit.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Same standard band implies direction difference strictly below one. -/
theorem value_sub_abs_lt_one_of_same_standardBand
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (k : ℕ) (hk : 0 < k) (hwidth : width < (k : ℝ))
    {x y : V} (hxy : x < y)
    {x' y' : V} (hx'y' : x' < y')
    (heq :
      standardBandColor D k hk hwidth x y =
        standardBandColor D k hk hwidth x' y') :
    |D.value x y - D.value x' y'| < 1 := by
  let c := standardBandColor D k hk hwidth x y
  have hband1 :=
    (standardBandColor_eq_iff D k hk hwidth hxy c).1 rfl
  have hband2 :=
    (standardBandColor_eq_iff D k hk hwidth hx'y' c).1 heq.symm
  rw [abs_lt]
  constructor <;> linarith

/-- Left cross diagonal of a same-band / residual / same-band four-chain
moves at least one full band upward. -/
theorem left_cross_value_ge_succ_of_through
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {a u v w : V}
    (hau : a < u) (huv : u < v) (hvw : v < w)
    {c : Fin n}
    (hAU :
      standardBandColor D (n + 1) (Nat.succ_pos n)
        hwidth a u = c.castSucc)
    (hVW :
      standardBandColor D (n + 1) (Nat.succ_pos n)
        hwidth v w = c.castSucc)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    (c : ℝ) + 1 ≤ D.value a v := by
  have hAV : a < v := hau.trans huv
  have hbandAU :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n) hwidth hau c.castSucc).1 hAU
  have hbandVW :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n) hwidth hvw c.castSucc).1 hVW
  have hresHigh :=
    (standardResidual_iff_high D n hwidth huv).1 hres
  have hbetween :=
    D.between hau huv
  have hAVbetween :
      D.value a u ≤ D.value a v ∧
        D.value a v ≤ D.value u v := by
    rcases hbetween with hforward | hreverse
    · exact hforward
    · have hAUltN :
          D.value a u < (n : ℝ) := by
        have hcLt : (c : ℕ) < n := c.isLt
        have hcSuccLe : (c : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr hcLt
        exact hbandAU.2.trans_le hcSuccLe
      exfalso
      linarith
  have hsep :
      1 ≤ |D.value a v - D.value v w| :=
    D.middleSeparated hAV hvw
  have hsmallOuter :
      |D.value a u - D.value v w| < 1 := by
    have heq :
        standardBandColor D (n + 1) (Nat.succ_pos n)
            hwidth a u =
          standardBandColor D (n + 1) (Nat.succ_pos n)
            hwidth v w := by
      rw [hAU, hVW]
    exact value_sub_abs_lt_one_of_same_standardBand
      D (n + 1) (Nat.succ_pos n) hwidth hau hvw heq
  have hNotLow :
      ¬ D.value a v ≤ D.value v w - 1 := by
    intro hlow
    have hdiff :
        D.value a v < D.value a u := by
      rw [abs_lt] at hsmallOuter
      linarith
    linarith
  have hhigh :
      D.value v w + 1 ≤ D.value a v := by
    by_cases horder : D.value v w ≤ D.value a v
    · have habs :
          |D.value a v - D.value v w| =
            D.value a v - D.value v w := by
        rw [abs_of_nonneg]
        linarith
      rw [habs] at hsep
      linarith
    · have hlt : D.value a v < D.value v w := lt_of_not_ge horder
      have habs :
          |D.value a v - D.value v w| =
            D.value v w - D.value a v := by
        rw [abs_of_nonpos]
        linarith
      rw [habs] at hsep
      have hlow : D.value a v ≤ D.value v w - 1 := by
        linarith
      exact False.elim (hNotLow hlow)
  linarith

/-- Right cross diagonal moves at least one full band upward. -/
theorem right_cross_value_ge_succ_of_through
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {a u v w : V}
    (hau : a < u) (huv : u < v) (hvw : v < w)
    {c : Fin n}
    (hAU :
      standardBandColor D (n + 1) (Nat.succ_pos n)
        hwidth a u = c.castSucc)
    (hVW :
      standardBandColor D (n + 1) (Nat.succ_pos n)
        hwidth v w = c.castSucc)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    (c : ℝ) + 1 ≤ D.value u w := by
  have hUW : u < w := huv.trans hvw
  have hbandAU :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n) hwidth hau c.castSucc).1 hAU
  have hbandVW :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n) hwidth hvw c.castSucc).1 hVW
  have hresHigh :=
    (standardResidual_iff_high D n hwidth huv).1 hres
  have hbetween :=
    D.between huv hvw
  have hUWbetween :
      D.value v w ≤ D.value u w ∧
        D.value u w ≤ D.value u v := by
    rcases hbetween with hforward | hreverse
    · exfalso
      have hVWltN :
          D.value v w < (n : ℝ) := by
        have hcLt : (c : ℕ) < n := c.isLt
        have hcSuccLe : (c : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast Nat.succ_le_iff.mpr hcLt
        exact hbandVW.2.trans_le hcSuccLe
      linarith
    · exact ⟨hreverse.1, hreverse.2⟩
  have hsep :
      1 ≤ |D.value a u - D.value u w| :=
    D.middleSeparated hau hUW
  have hsmallOuter :
      |D.value a u - D.value v w| < 1 := by
    have heq :
        standardBandColor D (n + 1) (Nat.succ_pos n)
            hwidth a u =
          standardBandColor D (n + 1) (Nat.succ_pos n)
            hwidth v w := by
      rw [hAU, hVW]
    exact value_sub_abs_lt_one_of_same_standardBand
      D (n + 1) (Nat.succ_pos n) hwidth hau hvw heq
  have hNotLow :
      ¬ D.value u w ≤ D.value a u - 1 := by
    intro hlow
    have hVWleUW := hUWbetween.1
    rw [abs_lt] at hsmallOuter
    linarith
  have hhigh :
      D.value a u + 1 ≤ D.value u w := by
    by_cases horder : D.value a u ≤ D.value u w
    · have habs :
          |D.value a u - D.value u w| =
            D.value u w - D.value a u := by
        rw [abs_of_nonpos]
        linarith
      rw [habs] at hsep
      linarith
    · have hlt : D.value u w < D.value a u := lt_of_not_ge horder
      have habs :
          |D.value a u - D.value u w| =
            D.value a u - D.value u w := by
        rw [abs_of_nonneg]
        linarith
      rw [habs] at hsep
      have hlow : D.value u w ≤ D.value a u - 1 := by
        linarith
      exact False.elim (hNotLow hlow)
  linarith

/-- Package both cross-diagonal ladder bounds. -/
theorem through_four_chain_cross_values_ge_succ
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {a u v w : V}
    (hau : a < u) (huv : u < v) (hvw : v < w)
    {c : Fin n}
    (hAU :
      standardBandColor D (n + 1) (Nat.succ_pos n)
        hwidth a u = c.castSucc)
    (hVW :
      standardBandColor D (n + 1) (Nat.succ_pos n)
        hwidth v w = c.castSucc)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    (c : ℝ) + 1 ≤ D.value a v ∧
      (c : ℝ) + 1 ≤ D.value u w := by
  exact ⟨
    left_cross_value_ge_succ_of_through
      D n hn hwidth hau huv hvw hAU hVW hres,
    right_cross_value_ge_succ_of_through
      D n hn hwidth hau huv hvw hAU hVW hres⟩

#print axioms value_sub_abs_lt_one_of_same_standardBand
#print axioms left_cross_value_ge_succ_of_through
#print axioms right_cross_value_ge_succ_of_through
#print axioms through_four_chain_cross_values_ge_succ

end DirectionData
end JSP000404Research
