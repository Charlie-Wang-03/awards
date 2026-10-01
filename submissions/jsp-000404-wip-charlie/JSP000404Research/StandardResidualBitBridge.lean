import JSP000404Research.StandardResidual
import JSP000404Research.ResidualBitMerge
import JSP000404Research.OrderedBandCode
import Mathlib.Tactic

/-!
# Standard residual retained bits are the standard unit-band bits

For the standard residual colouring, the retained colour c is exactly the
unit band [c,c+1).  Hence the abstract retained incoming bit agrees pointwise
with DirectionData.bandBit on the first n bands.
-/

namespace JSP000404Research
namespace DirectionData

theorem standardResidual_retainedBit_eq_bandBit
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    (v : V)
    (c : Fin n) :
    OrderedEdgeColoring.retainedBit
        (standardResidualColoring D n hwidth) v c
      =
    bandBit D n v c := by
  apply Bool.eq_iff_iff.mpr
  rw [OrderedEdgeColoring.retainedBit]
  rw [OrderedEdgeColoring.bit_eq_true_iff]
  -- Unfolding bandBit exposes the same incoming-band existential.
  simp only [bandBit, Bool.decide_eq_true]
  constructor
  · rintro ⟨a,hav,hcol⟩
    refine ⟨a,hav,?_,?_⟩
    have hb :=
      (standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hav c.castSucc).1
        (by
          simpa [standardResidualColoring] using hcol)
    · simpa using hb.1
    · simpa using hb.2
  · rintro ⟨a,hav,hlo,hhi⟩
    refine ⟨a,hav,?_⟩
    apply (standardBandColor_eq_iff
      D (n+1) (Nat.succ_pos n)
      (by exact_mod_cast hwidth)
      hav c.castSucc).2
    simpa using And.intro hlo hhi

#print axioms standardResidual_retainedBit_eq_bandBit

end DirectionData
end JSP000404Research
