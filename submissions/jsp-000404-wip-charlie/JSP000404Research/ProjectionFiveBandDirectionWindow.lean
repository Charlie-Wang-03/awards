import JSP000404Research.ThreeColourPaletteFiveEnvelope
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Five-band palette envelope gives a five-unit direction window

For the standard residual colouring, a retained edge colour is exactly the
floor of the normalized DirectionData value.  Hence if the retained colour
label lies in {m,...,m+4}, the edge value lies in [m,m+5).
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem standardResidual_retained_edge_value_mem_five_window
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    {n m : ℕ}
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hret :
      ((standardResidualColoring D n hwidth).color u v).val < n)
    (hband :
      (retainedColor
        (standardResidualColoring D n hwidth)
        u v hret).val ∈ fiveNatInterval m) :
    (m : ℝ) ≤ D.value u v ∧
      D.value u v < (m : ℝ) + 5 := by
  let R := standardResidualColoring D n hwidth
  let c : Fin n := retainedColor R u v hret

  have hcBounds :=
    mem_fiveNatInterval_iff_bounds.mp hband

  have hfull :
      R.color u v = c.castSucc := by
    apply Fin.ext
    simp [R,c,retainedColor]

  have hbandValue :
      ((c.castSucc : Fin (n + 1)) : ℝ) ≤ D.value u v ∧
      D.value u v < ((c.castSucc : Fin (n + 1)) : ℝ) + 1 := by
    apply
      (standardBandColor_eq_iff
        D (n + 1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        huv c.castSucc).1
    simpa [R, standardResidualColoring, standardBandColoring] using hfull

  have hcLo : m ≤ c.val := hcBounds.1
  have hcHi : c.val ≤ m + 4 := hcBounds.2
  constructor
  · exact le_trans (by exact_mod_cast hcLo) hbandValue.1
  · have hcHiR : (c.val : ℝ) ≤ (m : ℝ) + 4 := by
      exact_mod_cast hcHi
    have hcast :
        ((c.castSucc : Fin (n + 1)) : ℝ) = (c.val : ℝ) := by
      rfl
    rw [hcast] at hbandValue
    linarith

theorem projectedLoss_pair_value_mem_five_window
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    {n m : ℕ}
    (hwidth : width < (n + 1 : ℕ))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q,
        (OrderedEdgeColoring.active
          (standardResidualColoring D n hwidth) q).card
          ≤ n - exponent q + 1)
    {u v : V}
    (huv : u < v)
    (huLoss :
      u ∈ OrderedEdgeColoring.projectedLossVertices
        (standardResidualColoring D n hwidth) exponent)
    (hpalette :
      (OrderedEdgeColoring.retainedActive
        (standardResidualColoring D n hwidth) u).map
          Fin.valEmbedding
        ⊆ fiveNatInterval m) :
    (m : ℝ) ≤ D.value u v ∧
      D.value u v < (m : ℝ) + 5 := by
  let R := standardResidualColoring D n hwidth
  have hret :
      (R.color u v).val < n :=
    OrderedEdgeColoring.projectedLoss_edge_right_retained
      R exponent hexp honeLoss huLoss huv
  let c : Fin n := OrderedEdgeColoring.retainedColor R u v hret
  have hcActive :
      c ∈ OrderedEdgeColoring.retainedActive R u :=
    OrderedEdgeColoring.retainedColor_mem_retainedActive_left
      R huv hret
  have hcMap :
      c.val ∈
        (OrderedEdgeColoring.retainedActive R u).map
          Fin.valEmbedding := by
    exact Finset.mem_map.mpr ⟨c,hcActive,rfl⟩
  have hcBand : c.val ∈ fiveNatInterval m := by
    apply hpalette
    simpa [R] using hcMap
  exact standardResidual_retained_edge_value_mem_five_window
    D hwidth huv hret (by simpa [R,c] using hcBand)

#print axioms standardResidual_retained_edge_value_mem_five_window
#print axioms projectedLoss_pair_value_mem_five_window

end DirectionData
end JSP000404Research
