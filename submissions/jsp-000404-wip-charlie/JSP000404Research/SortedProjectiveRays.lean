import JSP000404Research.FiniteProjectiveRays
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Sorting the canonical projective rays

Around a fixed centre, sort all other vertices by the lexicographic key

  (theta_j, j).

The vertex component is only a deterministic tie-breaker, so the resulting
list has nondecreasing projective angle even when several points share the
same projective direction.

The theorem below gives an exact finite list: no duplicates, every non-centre
vertex occurs, and the theta values are pairwise nondecreasing.
-/

namespace JSP000404Research

/-- Lexicographic key used only to sort canonical projective rays. -/
noncomputable def rayOrderKey
    {V : Type*} [LinearOrder V] {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    ℝ ×ₗ V :=
  toLex (rayThetaAt hp i j, j.1)

theorem rayOrderKey_injective
    {V : Type*} [LinearOrder V] {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) :
    Function.Injective (rayOrderKey hp i) := by
  intro a b hab
  apply Subtype.ext
  have hsecond :
      (ofLex (rayOrderKey hp i a)).2 =
        (ofLex (rayOrderKey hp i b)).2 :=
    congrArg (fun z : ℝ ×ₗ V => (ofLex z).2) hab
  simpa [rayOrderKey] using hsecond

/-- Temporary linear order on non-centre vertices induced by the lexicographic
ray key. -/
noncomputable def otherVertexRayOrder
    {V : Type*} [LinearOrder V] {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) :
    LinearOrder (OtherVertex i) :=
  LinearOrder.lift'
    (rayOrderKey hp i)
    (rayOrderKey_injective hp i)

/-- The lifted order is monotone in the actual projective angle. -/
theorem rayTheta_le_of_rayOrder_le
    {V : Type*} [LinearOrder V] {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    {a b : OtherVertex i}
    (hab :
      @LE.le (OtherVertex i)
        (otherVertexRayOrder hp i).toLE a b) :
    rayThetaAt hp i a ≤ rayThetaAt hp i b := by
  have hkey :
      rayOrderKey hp i a ≤ rayOrderKey hp i b := by
    exact hab
  have hfst := Prod.Lex.monotone_fst _ _ hkey
  simpa [rayOrderKey] using hfst

/-- All non-centre rays admit an exact theta-sorted list enumeration. -/
theorem exists_theta_sorted_other_vertices
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) :
    ∃ rays : List (OtherVertex i),
      rays.toFinset = Finset.univ ∧
      rays.Nodup ∧
      rays.Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
  classical
  letI : LinearOrder (OtherVertex i) :=
    otherVertexRayOrder hp i
  let rays : List (OtherVertex i) :=
    (Finset.univ : Finset (OtherVertex i)).sort
  refine ⟨rays, ?_, ?_, ?_⟩
  · dsimp [rays]
    simp
  · dsimp [rays]
    exact Finset.sort_nodup _ _
  · have hpair :
        rays.Pairwise (fun a b : OtherVertex i => a ≤ b) := by
      dsimp [rays]
      exact Finset.pairwise_sort _ _
    apply hpair.imp
    intro a b hab
    exact rayTheta_le_of_rayOrder_le hp i hab

/-- In particular the sorted ray list has exactly card(V)-1 entries. -/
theorem theta_sorted_other_vertices_length
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) :
    ∃ rays : List (OtherVertex i),
      rays.length = Fintype.card (OtherVertex i) ∧
      rays.toFinset = Finset.univ ∧
      rays.Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
  obtain ⟨rays, hall, hnodup, hsorted⟩ :=
    exists_theta_sorted_other_vertices hp i
  refine ⟨rays, ?_, hall, hsorted⟩
  rw [← List.toFinset_card_of_nodup hnodup, hall]
  simp

#print axioms rayOrderKey_injective
#print axioms rayTheta_le_of_rayOrder_le
#print axioms exists_theta_sorted_other_vertices
#print axioms theta_sorted_other_vertices_length

end JSP000404Research
