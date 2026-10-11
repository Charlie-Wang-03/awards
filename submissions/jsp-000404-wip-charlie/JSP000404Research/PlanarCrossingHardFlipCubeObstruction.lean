import JSP000404Research.PlanarCrossingHardFlipDescent
import JSP000404Research.ResidualSafeFlipCubeObstruction
import Mathlib.Tactic

/-!
# The oriented safe flip is covered even in genuine planar configurations

This strengthens the already verified planar crossing hard-carrier local
trichotomy by certifying that its exact one-bit-flipped retained code is
ALWAYS covered by the upper vertex's retained completion cube.

The first local alternative ("no vertex has this canonical retained code")
is therefore NOT a Boolean hole. This negative conclusion applies to the
actual canonical projective-cycle exponents of AngleCap planar points,
not merely to arbitrary abstract direction data.

The statement does not produce a global overlap/defect payment.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_crossing_safe_flip_is_covered_or_resolves_or_descends
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (u a v b : ProjectionOrdered V)
    (hua :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      u < a)
    (hav :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < v)
    (hvb :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      v < b)
    (hHard :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let hpos : 0 < t := by
        rw [ht]
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      let hwidth : t < ((n + 1 : ℕ) : ℝ) := by
        rw [ht]
        push_cast
        linarith
      let D := genericDirectionData_sendov hp hcap hpos hlam
      let B := standardResidualColoring D n hwidth
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      (∃ wordUV wordAB : Fin n → Bool,
        (¬ ∃ c : Fin n, c ∉ residualForbidden B u v) ∧
        (¬ ∃ c : Fin n, c ∉ residualForbidden B a b) ∧
        wordUV ∈ retainedCompletionWords B u ∧
        wordUV ∈ retainedCompletionWords B v ∧
        wordAB ∈ retainedCompletionWords B a ∧
        wordAB ∈ retainedCompletionWords B b) ∧
      n ≤ k a + k v ∧
      SameRetained B a v ∧
      (¬ ∃ c : Fin n,
        c ∉ retainedActive B a ∧
        c ∉ retainedActive B v)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < ((n + 1 : ℕ) : ℝ) := by
      rw [ht]
      push_cast
      linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n hwidth
    ∃ c : Fin n,
      c ∉ residualForbidden B a v ∧
      c ∈ outgoingRetained B a ∧
      c ∉ retainedActive B v ∧
      flippedRetainedCode B a c ∈ coveredCompletionWords B ∧
      ((¬ ∃ w : ProjectionOrdered V,
          (fun d => retainedBit B w d) =
            flippedRetainedCode B a c) ∨
        (∃ w : ProjectionOrdered V,
          a < w ∧ w < v ∧
          IsResidual B w v ∧ RetainedSeparated B w v) ∨
        (∃ w : ProjectionOrdered V,
          v < w ∧
          (fun d => retainedBit B w d) =
            flippedRetainedCode B a c ∧
          (B.color v w).val < c.val)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < ((n + 1 : ℕ) : ℝ) := by
    rw [ht]
    push_cast
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  have hsame : SameRetained B a v := by
    exact hHard.2.2.1
  obtain ⟨c, hsafe, hout, hinactive, hcases⟩ :=
    planar_crossing_unsafe_high_mass_flip_hole_resolve_or_descend
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      cycles u a v b hua hav hvb hHard
  exact ⟨c, hsafe, hout, hinactive,
    sameRetained_flip_always_globally_covered B a v c hsame hinactive,
    hcases⟩

#print axioms planar_crossing_safe_flip_is_covered_or_resolves_or_descends

end ProjectionOrdered
end JSP000404Research
