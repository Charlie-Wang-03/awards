import JSP000404Research.CentreProjectiveCycle
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Four-point centre cycles have three rays and three gaps

For V = Fin 4, every centre has exactly three other vertices.  Therefore every
concrete centre cycle consists of exactly three sorted rays and exactly three
normalized projective gaps.

This small structural fact lets the four-centre terminal use the explicit
three-gap merge and support-two lemmas without an additional abstract length
parameter.
-/

namespace JSP000404Research

theorem card_otherVertex_fin4 (i : Fin 4) :
    Fintype.card (OtherVertex i) = 3 := by
  change Fintype.card {j : Fin 4 // j ≠ i} = 3
  rw [Fintype.card_subtype_compl (fun j : Fin 4 => j = i)]
  simp

theorem centreProjectiveCycle_rays_length_fin4
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i) :
    C.rays.length = 3 := by
  classical
  have hcard :
      C.rays.toFinset.card = C.rays.length :=
    List.toFinset_card_of_nodup C.nodup
  have huniv :
      C.rays.toFinset.card =
        Fintype.card (OtherVertex i) := by
    rw [C.complete, Finset.card_univ]
  rw [← hcard, huniv, card_otherVertex_fin4 i]

theorem centreProjectiveCycle_gaps_length_fin4
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i) :
    C.gaps.length = 3 := by
  rw [C.gaps_length]
  exact centreProjectiveCycle_rays_length_fin4 i C

theorem centreProjectiveCycle_angles_length_fin4
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i) :
    C.angles.length = 3 := by
  rw [C.angles_length]
  exact centreProjectiveCycle_rays_length_fin4 i C

/-- Any length-three ray list can be exposed as an explicit triple. -/
theorem exists_three_rays_of_fin4_cycle
    {p : Fin 4 → Plane}
    {hp : Function.Injective p}
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i) :
    ∃ r0 r1 r2 : OtherVertex i,
      C.rays = [r0,r1,r2] := by
  have hlen := centreProjectiveCycle_rays_length_fin4 i C
  cases h : C.rays with
  | nil =>
      simp [h] at hlen
  | cons r0 rs =>
      cases hrs : rs with
      | nil =>
          simp [h, hrs] at hlen
      | cons r1 rs1 =>
          cases hrs1 : rs1 with
          | nil =>
              simp [h, hrs, hrs1] at hlen
          | cons r2 rs2 =>
              cases hrs2 : rs2 with
              | nil =>
                  exact ⟨r0, r1, r2, by simp [h, hrs, hrs1, hrs2]⟩
              | cons r3 rs3 =>
                  simp [h, hrs, hrs1, hrs2] at hlen

#print axioms card_otherVertex_fin4
#print axioms centreProjectiveCycle_rays_length_fin4
#print axioms centreProjectiveCycle_gaps_length_fin4
#print axioms exists_three_rays_of_fin4_cycle

end JSP000404Research
