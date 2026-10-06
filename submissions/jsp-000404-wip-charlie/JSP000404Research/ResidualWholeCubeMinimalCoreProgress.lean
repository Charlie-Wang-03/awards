import JSP000404Research.ResidualWholeCubeSecondCoordinateProfiledOutcome
import JSP000404Research.ResidualWholeCubePairExtraSharedWitness
import JSP000404Research.ResidualWholeCubeSecondCoordinateProfile
import Mathlib.Tactic

/-!
# Minimal-core whole-cube partner gives a closed outlet or profiled recursion outcome

At a projected-loss second-layer source v inside an inclusion-minimal deficient
core, a whole-cube Q/T partner forces an extra shared word, hence a third-source
witness.  The existing profile reduction classifies that third source into the
standard closed outlets or a second-layer second-coordinate witness.

Composing with the complete profiled second-coordinate outcome yields the
recursion-ready statement: every such whole-cube partner either exits through a
standard profile outlet or produces one of the five explicit profiled outcomes
(repeat / discovery / TQ half / TT quotient rematch / TT half).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimal_core_wholeCube_partner_profile_or_profiled_outcome
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    (hexpLt : ∀ q, exponent q < n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c)
    (coords : Finset (Fin n))
    (hcoords : coords ⊆ retainedActive C v) :
    (
      ∃ q : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) q
    )
    ∨
    (
      ∃ q : V,
        ExactProjectedBudget C exponent q
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q = n - 1
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q + 3 ≤ n
    )
    ∨
    WholeCubeSecondCoordinateProfiledOutcome
      C exponent T s v c coords := by
  have hthird :
      WholeCubeThirdSourceWitness C exponent T s v :=
    minimal_core_wholeCubeQTPair_has_third_source
      C exponent hn3 hdef hmin
      hvT hsv hsLoss hvLoss hvSecond hcV hwhole

  rcases wholeCubeThirdSource_profile_reduction
      C exponent hexpLt hexp honeLoss
      hvLoss hwhole hthird
    with hstrict | hexact | htop | hdeep | hsecond
  · exact Or.inl hstrict
  · exact Or.inr (Or.inl hexact)
  · exact Or.inr (Or.inr (Or.inl htop))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hdeep)))
  · right; right; right; right
    exact wholeCubeSecondCoordinate_profiled_outcome
      C exponent hn3 hexp honeLoss
      hvLoss hvSecond hsecond coords hcoords

/-- If all four standard profile outlets are excluded, the whole-cube partner
must enter the explicit profiled recursion state machine. -/
theorem minimal_core_wholeCube_partner_forces_profiled_outcome
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    (hexpLt : ∀ q, exponent q < n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c)
    (coords : Finset (Fin n))
    (hcoords : coords ⊆ retainedActive C v)
    (hnoStrict :
      ¬ ∃ q : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) q)
    (hnoExact :
      ¬ ∃ q : V,
        ExactProjectedBudget C exponent q)
    (hnoTop :
      ¬ ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q = n - 1)
    (hnoDeep :
      ¬ ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q + 3 ≤ n) :
    WholeCubeSecondCoordinateProfiledOutcome
      C exponent T s v c coords := by
  rcases minimal_core_wholeCube_partner_profile_or_profiled_outcome
      C exponent hn3 hexpLt hexp honeLoss
      hdef hmin
      hvT hsv hsLoss hvLoss hvSecond hcV hwhole
      coords hcoords
    with hstrict | hexact | htop | hdeep | houtcome
  · exact False.elim (hnoStrict hstrict)
  · exact False.elim (hnoExact hexact)
  · exact False.elim (hnoTop htop)
  · exact False.elim (hnoDeep hdeep)
  · exact houtcome

#print axioms minimal_core_wholeCube_partner_profile_or_profiled_outcome
#print axioms minimal_core_wholeCube_partner_forces_profiled_outcome

end OrderedEdgeColoring
end JSP000404Research
