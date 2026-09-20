import Mathlib.Tactic

/-!
# Exact arithmetic hard stop for unconditional compensated deletion

A numerically realized four-point lower-branch configuration produced the
following quotient/exponent profile at one fixed exact-normalization parameter.

Original centres:

  [1,1,1], [2,0,0], [0,0,2], [0,0,2]

so their floor-excess exponents are

  0,1,1,1

and the total dyadic mass is 7.

After deleting any one centre and merging the corresponding projective gaps,
the three surviving quotient pairs have exponent 1 each.  Hence every
post-deletion dyadic mass is exactly 6.

The actual planar realization is a separate numerical-geometric certificate;
this file deliberately formalizes only the exact finite arithmetic profile.
It proves that this profile, once geometrically realized, contradicts the
over-strong conjecture that some deletion must always be compensated.
-/

namespace JSP000404Research

def listFloorExcess (qs : List ℕ) : ℕ :=
  (qs.map (fun q => q - 1)).sum

def dyadicWeightOfQ (qs : List ℕ) : ℕ :=
  2 ^ listFloorExcess qs

def compensatedHardStopOriginal : List (List ℕ) :=
  [[1,1,1], [2,0,0], [0,0,2], [0,0,2]]

def compensatedHardStopAfterDelete : Fin 4 → List (List ℕ)
  | 0 => [[2,1], [1,2], [1,2]]
  | 1 => [[1,2], [0,2], [0,2]]
  | 2 => [[2,1], [2,0], [0,2]]
  | 3 => [[1,2], [0,2], [0,2]]

def totalDyadicWeight (profiles : List (List ℕ)) : ℕ :=
  (profiles.map dyadicWeightOfQ).sum

theorem compensatedHardStop_original_exponents :
    compensatedHardStopOriginal.map listFloorExcess =
      [0,1,1,1] := by
  native_decide

theorem compensatedHardStop_original_weight :
    totalDyadicWeight compensatedHardStopOriginal = 7 := by
  native_decide

theorem compensatedHardStop_post_exponents
    (r : Fin 4) :
    (compensatedHardStopAfterDelete r).map listFloorExcess =
      [1,1,1] := by
  fin_cases r <;> native_decide

theorem compensatedHardStop_post_weight
    (r : Fin 4) :
    totalDyadicWeight (compensatedHardStopAfterDelete r) = 6 := by
  fin_cases r <;> native_decide

theorem compensatedHardStop_no_compensated_deletion :
    ¬ ∃ r : Fin 4,
      totalDyadicWeight compensatedHardStopOriginal ≤
        totalDyadicWeight (compensatedHardStopAfterDelete r) := by
  intro h
  obtain ⟨r, hr⟩ := h
  rw [compensatedHardStop_original_weight,
      compensatedHardStop_post_weight r] at hr
  omega

#print axioms compensatedHardStop_original_weight
#print axioms compensatedHardStop_post_weight
#print axioms compensatedHardStop_no_compensated_deletion

end JSP000404Research
