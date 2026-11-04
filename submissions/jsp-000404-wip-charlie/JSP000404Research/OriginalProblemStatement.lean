import JSP000404Research.SharpCentre
import Jsp000404.Statement

/-!
# The original Blumenthal problem, with both required quantifier directions

`Jsp404.alphaN` is the audited Sendov formula, not a definition of the
geometric extremum. It treats 3 separately, uses the unique dyadic strip
for N >= 4, and uses integer-exponent powers at the n = 1 boundary.

This module STATES the complete problem. It does not assert its proof.
The formula is reused from aznikline's pinned public package; that package's
all-N lower theorem requires `GeometricCertificates` and is not used here.
-/

namespace JSP000404Research

/-- Every injective ordinary N-point planar configuration forces the claimed
unoriented angle, at the middle member of a pairwise distinct triple. -/
def OriginalLowerBound (N : ℕ) : Prop :=
  ∀ p : Fin N → Plane, Function.Injective p →
    ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Jsp404.alphaN N ≤ EuclideanGeometry.angle (p a) (p b) (p c)

/-- Epsilon sharpness uses actual distinct ordinary points. No attainment,
general-position condition, convexity assumption, or generalized points. -/
def OriginalSharpness (N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ p : Fin N → Plane, Function.Injective p ∧
      ∀ a b c : Fin N, a ≠ b → a ≠ c → b ≠ c →
        EuclideanGeometry.angle (p a) (p b) (p c) < Jsp404.alphaN N + ε

/-- The full all-N original statement. There is currently no theorem of
this type in the research package. -/
def OriginalProblem : Prop :=
  ∀ N : ℕ, 3 ≤ N → OriginalLowerBound N ∧ OriginalSharpness N

end JSP000404Research
