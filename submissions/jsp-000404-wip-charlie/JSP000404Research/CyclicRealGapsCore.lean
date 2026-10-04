import JSP000404Research.CyclicProjectiveGaps

/-!
# Lightweight cyclic real-gap data

This module contains only the raw cyclic real-gap construction used by local
zero-floor mass arguments.  It is deliberately separated from the much larger
historical cyclic band-capacity proof.
-/

namespace JSP000404Research

/-- Cyclic real gaps at circumference t. -/
def cyclicRealGaps (t : ℝ) : List ℝ → List ℝ
  | [] => []
  | a :: xs =>
      successiveDiffsFrom a xs ++
        [t + a - xs.getLastD a]

end JSP000404Research
