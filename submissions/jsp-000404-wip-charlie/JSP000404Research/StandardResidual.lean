import JSP000404Research.ResidualRecolor
import JSP000404Research.StandardBandColor
import Mathlib.Tactic

/-!
# The standard residual band

Specialize the standard (n+1)-band ordered colouring to a direction width
strictly below n+1.  The retained colours are exactly the first n canonical
unit bands.  The unique residual old colour is exactly the short top interval
[n,width).

This identifies the abstract residual-recolouring interface with the actual
nonintegral direction partition used in the lower Sendov branch.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Standard old colouring with n+1 unit-band slots. -/
noncomputable def standardResidualColoring
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width < (n + 1 : ℕ)) :
    OrderedEdgeColoring V (n + 1) :=
  standardBandColoring D (n + 1) (Nat.succ_pos n) (by
    exact_mod_cast hwidth)

/-- On an increasing edge, being residual is equivalent to having normalized
direction at least n. -/
theorem standardResidual_iff_high
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V} (huv : u < v) :
    ¬((standardResidualColoring D n hwidth).color u v).val < n ↔
      (n : ℝ) ≤ D.value u v := by
  have hx0 := D.nonnegative huv
  change ¬(Nat.floor (D.value u v) < n) ↔ (n : ℝ) ≤ D.value u v
  constructor
  · intro hnot
    have hnfloor : n ≤ Nat.floor (D.value u v) := by omega
    have hfloorx : ((Nat.floor (D.value u v) : ℕ) : ℝ) ≤ D.value u v :=
      Nat.floor_le hx0
    exact (by exact_mod_cast hnfloor).trans hfloorx
  · intro hnx hlt
    have hfloorlt : Nat.floor (D.value u v) < n := hlt
    have hxlt : D.value u v < (n : ℝ) :=
      (Nat.floor_lt hx0).1 hfloorlt
    exact (not_lt_of_ge hnx) hxlt

/-- The retained active colours of the standard (n+1)-band colouring are
exactly the canonical first-n incident bands. -/
theorem standardResidual_retainedActive_eq_incidentBands
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    (v : V) :
    retainedActive (standardResidualColoring D n hwidth) v =
      incidentBands D n v := by
  classical
  ext c
  simp only [retainedActive, incidentBands,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases h with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
    · left
      refine ⟨a, hav, ?_, ?_⟩
      have hb :=
        (standardBandColor_eq_iff D (n + 1) (Nat.succ_pos n)
          (by exact_mod_cast hwidth) hav c.castSucc).1 hcol
      · simpa using hb.1
      · simpa using hb.2
    · right
      refine ⟨w, hvw, ?_, ?_⟩
      have hb :=
        (standardBandColor_eq_iff D (n + 1) (Nat.succ_pos n)
          (by exact_mod_cast hwidth) hvw c.castSucc).1 hcol
      · simpa using hb.1
      · simpa using hb.2
  · intro h
    rcases h with ⟨a, hav, hlo, hhi⟩ | ⟨w, hvw, hlo, hhi⟩
    · left
      refine ⟨a, hav, ?_⟩
      apply (standardBandColor_eq_iff D (n + 1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth) hav c.castSucc).2
      simpa using And.intro hlo hhi
    · right
      refine ⟨w, hvw, ?_⟩
      apply (standardBandColor_eq_iff D (n + 1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth) hvw c.castSucc).2
      simpa using And.intro hlo hhi

/-- The full active set of the standard residual colouring agrees with the
(n+1)-band incident set. -/
theorem standardResidual_active_eq_incidentBands_succ
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    (v : V) :
    active (standardResidualColoring D n hwidth) v =
      incidentBands D (n + 1) v := by
  exact standardBand_active_eq_incidentBands
    D (n + 1) (Nat.succ_pos n) (by exact_mod_cast hwidth) v

#print axioms standardResidual_iff_high
#print axioms standardResidual_retainedActive_eq_incidentBands
#print axioms standardResidual_active_eq_incidentBands_succ

end DirectionData
end JSP000404Research
