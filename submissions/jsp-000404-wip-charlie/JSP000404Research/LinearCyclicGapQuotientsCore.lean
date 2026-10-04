import JSP000404Research.CyclicProjectiveGaps

/-!
# Lightweight linear cyclic gap quotient data

Only the quotient-list construction is kept here.  Capacity inequalities live
in LinearBandGapCapacity.
-/

namespace JSP000404Research

noncomputable def linearCyclicGapQuotients (t : ℝ) : List ℝ → List ℕ
  | [] => []
  | a :: xs =>
      (successiveDiffsFrom a xs).map Nat.floor ++
        [Nat.floor (a + t - xs.getLastD a)]

end JSP000404Research
