
import JSP000404Research.CyclicGapRotationInvariant

/-!
# Compatibility aliases for cyclic exponent rotation

The canonical rotation invariance theorem now lives in
CyclicGapRotationInvariant.  This module intentionally introduces only
distinctly named aliases, avoiding duplicate declarations when both modules
are imported.
-/

namespace JSP000404Research

theorem dyadic_listExponent_rotate
    (qs : List ℕ) (k : ℕ) :
    2 ^ listExponent (qs.rotate k) =
      2 ^ listExponent qs := by
  rw [listExponent_rotate]

#print axioms dyadic_listExponent_rotate

end JSP000404Research
