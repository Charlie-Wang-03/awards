
import JSP000404Research.ResidualUnsafeWitnessCount
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Through-colours promote cross edges in the standard residual geometry

Let C be the standard (n+1)-band colouring of ordered direction data of width
less than n+1.  Suppose u<v is residual and a retained colour c is both
incoming at u and outgoing at v.

Then there are witnesses

  a < u < v < w

with the outer edges a--u and v--w in the same unit band c, while u--v lies
in the residual top band.

The direction-data betweenness axioms force

  value(a,u) <= value(a,v) <= value(u,v),
  value(v,w) <= value(u,w) <= value(u,v).

The two outer directions differ by less than one because they lie in the same
unit band.  Applying middle separation to the triples a<v<w and a<u<w rules
out the lower alternative and promotes both cross edges by a full unit:

  c+1 <= value(a,v),
  c+1 <= value(u,w).

Thus a through-colour creates a one-level direction ladder.  In particular,
if c is the top retained colour n-1, both cross edges are themselves residual.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Concrete standard-band witnesses for one through colour. -/
theorem standardResidual_throughColour_witnesses
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V} (huv : u < v)
    {c : Fin n}
    (hc :
      c ∈ residualThroughColours
        (standardResidualColoring D n hwidth) u v) :
    ∃ a w : V,
      a < u ∧ v < w ∧
      (c : ℝ) ≤ D.value a u ∧
      D.value a u < (c : ℝ) + 1 ∧
      (c : ℝ) ≤ D.value v w ∧
      D.value v w < (c : ℝ) + 1 := by
  let C := standardResidualColoring D n hwidth
  obtain ⟨hleft, hright⟩ :=
    throughColour_has_outer_witnesses C hc
  obtain ⟨a, hau, hcolAU⟩ := hleft
  obtain ⟨w, hvw, hcolVW⟩ := hright
  have hbandAU :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast hwidth)
      hau c.castSucc).1 hcolAU
  have hbandVW :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast hwidth)
      hvw c.castSucc).1 hcolVW
  refine ⟨a, w, hau, hvw, ?_, ?_, ?_, ?_⟩ <;>
    simpa using hbandAU.1 <;>
    try simpa using hbandAU.2 <;>
    try simpa using hbandVW.1 <;>
    try simpa using hbandVW.2

/-- The residual middle edge has normalized direction at least n. -/
theorem standardResidual_value_ge_n
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    (n : ℝ) ≤ D.value u v :=
  (standardResidual_iff_high D n hwidth huv).1 hres

/-- First cross edge lies between the incoming outer direction and the
residual middle direction. -/
theorem standardResidual_cross_left_between
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {a u v : V}
    (hau : a < u) (huv : u < v)
    {c : Fin n}
    (hAUlo : (c : ℝ) ≤ D.value a u)
    (hAUhi : D.value a u < (c : ℝ) + 1)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    D.value a u ≤ D.value a v ∧
      D.value a v ≤ D.value u v := by
  have hmid :
      (n : ℝ) ≤ D.value u v :=
    standardResidual_value_ge_n D n hwidth huv hres
  have hcN : (c : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast c.isLt
  have hstrict :
      D.value a u < D.value u v := by
    linarith
  rcases D.between hau huv with hforward | hreverse
  · exact hforward
  · exfalso
    linarith

/-- Second cross edge lies between the outgoing outer direction and the
residual middle direction. -/
theorem standardResidual_cross_right_between
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    {c : Fin n}
    (hVWlo : (c : ℝ) ≤ D.value v w)
    (hVWhi : D.value v w < (c : ℝ) + 1)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    D.value v w ≤ D.value u w ∧
      D.value u w ≤ D.value u v := by
  have hmid :
      (n : ℝ) ≤ D.value u v :=
    standardResidual_value_ge_n D n hwidth huv hres
  have hcN : (c : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast c.isLt
  have hstrict :
      D.value v w < D.value u v := by
    linarith
  rcases D.between huv hvw with hforward | hreverse
  · exfalso
    linarith
  · exact hreverse

/-- Same-band outer edges plus a residual middle edge promote the left cross
edge by at least one full normalized unit. -/
theorem standardResidual_cross_left_promoted
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {a u v w : V}
    (hau : a < u) (huv : u < v) (hvw : v < w)
    {c : Fin n}
    (hAUlo : (c : ℝ) ≤ D.value a u)
    (hAUhi : D.value a u < (c : ℝ) + 1)
    (hVWlo : (c : ℝ) ≤ D.value v w)
    (hVWhi : D.value v w < (c : ℝ) + 1)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    (c : ℝ) + 1 ≤ D.value a v := by
  have hbetween :=
    standardResidual_cross_left_between
      D n hwidth hau huv hAUlo hAUhi hres
  have havw : a < v := hau.trans huv
  have hsep := D.middleSeparated havw hvw
  by_cases hle : D.value a v ≤ D.value v w
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hsep
    have hclose :
        D.value v w - D.value a u < 1 := by
      linarith
    have hAUav :
        D.value a u ≤ D.value a v :=
      hbetween.1
    linarith
  · have hge : D.value v w ≤ D.value a v :=
      le_of_not_ge hle
    rw [abs_of_nonneg (sub_nonneg.mpr hge)] at hsep
    linarith

/-- Symmetric promotion of the right cross edge. -/
theorem standardResidual_cross_right_promoted
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {a u v w : V}
    (hau : a < u) (huv : u < v) (hvw : v < w)
    {c : Fin n}
    (hAUlo : (c : ℝ) ≤ D.value a u)
    (hAUhi : D.value a u < (c : ℝ) + 1)
    (hVWlo : (c : ℝ) ≤ D.value v w)
    (hVWhi : D.value v w < (c : ℝ) + 1)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    (c : ℝ) + 1 ≤ D.value u w := by
  have hbetween :=
    standardResidual_cross_right_between
      D n hwidth huv hvw hVWlo hVWhi hres
  have huw : u < w := huv.trans hvw
  have hsep := D.middleSeparated hau huw
  by_cases hle : D.value u w ≤ D.value a u
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hsep
    have hclose :
        D.value a u - D.value v w < 1 := by
      linarith
    have hVWuw :
        D.value v w ≤ D.value u w :=
      hbetween.1
    linarith
  · have hge : D.value a u ≤ D.value u w :=
      le_of_not_ge hle
    rw [abs_of_nonpos (sub_nonpos.mpr hge)] at hsep
    linarith

/-- Packaged one-through-colour ladder. -/
theorem standardResidual_throughColour_promotes_cross_edges
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    {c : Fin n}
    (hc :
      c ∈ residualThroughColours
        (standardResidualColoring D n hwidth) u v) :
    ∃ a w : V,
      a < u ∧ v < w ∧
      (c : ℝ) + 1 ≤ D.value a v ∧
      (c : ℝ) + 1 ≤ D.value u w := by
  obtain ⟨a, w, hau, hvw,
      hAUlo, hAUhi, hVWlo, hVWhi⟩ :=
    standardResidual_throughColour_witnesses
      D n hn hwidth huv hc
  refine ⟨a, w, hau, hvw, ?_, ?_⟩
  · exact standardResidual_cross_left_promoted
      D n hwidth hau huv hvw
      hAUlo hAUhi hVWlo hVWhi hres
  · exact standardResidual_cross_right_promoted
      D n hwidth hau huv hvw
      hAUlo hAUhi hVWlo hVWhi hres

/-- A top retained through-colour creates two additional residual cross edges. -/
theorem standardResidual_topThrough_creates_cross_residuals
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    {c : Fin n}
    (hcTop : c.val + 1 = n)
    (hc :
      c ∈ residualThroughColours
        (standardResidualColoring D n hwidth) u v) :
    ∃ a w : V,
      a < u ∧ v < w ∧
      IsResidual
        (standardResidualColoring D n hwidth) a v ∧
      IsResidual
        (standardResidualColoring D n hwidth) u w := by
  obtain ⟨a, w, hau, hvw, havLower, huwLower⟩ :=
    standardResidual_throughColour_promotes_cross_edges
      D n hn hwidth huv hres hc
  have hav : a < v := hau.trans huv
  have huw : u < w := huv.trans hvw
  have hcReal :
      (c : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hcTop
  rw [hcReal] at havLower huwLower
  refine ⟨a, w, hau, hvw, ?_, ?_⟩
  · exact (standardResidual_iff_high
      D n hwidth hav).2 havLower
  · exact (standardResidual_iff_high
      D n hwidth huw).2 huwLower

#print axioms standardResidual_throughColour_witnesses
#print axioms standardResidual_cross_left_promoted
#print axioms standardResidual_cross_right_promoted
#print axioms standardResidual_throughColour_promotes_cross_edges
#print axioms standardResidual_topThrough_creates_cross_residuals

end DirectionData
end JSP000404Research
