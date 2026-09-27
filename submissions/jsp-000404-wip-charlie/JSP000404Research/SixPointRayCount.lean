import JSP000404Research.CutCentreRayCycle
import Mathlib.Tactic

/-!
# Ray-count identities in the six-point terminal

For a fixed centre i, OtherVertex i is the complement of the singleton {i}.
Hence

  card (OtherVertex i) = card V - 1.

Every CentreProjectiveCycle and CentreCutRayCycle enumerates OtherVertex i
exactly once, so under card V = 6 both ray lists have length exactly five.
-/

namespace JSP000404Research

noncomputable def otherVertexEquivErase
    {V : Type*} [Fintype V] [DecidableEq V]
    (i : V) :
    OtherVertex i ≃
      {j : V // j ∈ (Finset.univ.erase i : Finset V)} where
  toFun j := ⟨j.1, by simp [j.2]⟩
  invFun j := ⟨j.1, by simpa using j.2⟩
  left_inv j := by ext; rfl
  right_inv j := by ext; rfl

theorem card_otherVertex_eq_card_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (i : V) :
    Fintype.card (OtherVertex i) = Fintype.card V - 1 := by
  rw [Fintype.card_congr (otherVertexEquivErase i)]
  simp

theorem CentreProjectiveCycle.rays_length_eq_card_otherVertex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.rays.length = Fintype.card (OtherVertex i) := by
  classical
  calc
    C.rays.length = C.rays.toFinset.card := by
      simpa using (List.toFinset_card_of_nodup C.nodup).symm
    _ = Fintype.card (OtherVertex i) := by
      rw [C.complete]
      simp

theorem CentreCutRayCycle.rays_length_eq_card_otherVertex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c) :
    R.rays.length = Fintype.card (OtherVertex i) := by
  classical
  calc
    R.rays.length = R.rays.toFinset.card := by
      simpa using (List.toFinset_card_of_nodup R.nodup).symm
    _ = Fintype.card (OtherVertex i) := by
      rw [R.complete]
      simp

theorem CentreProjectiveCycle.rays_length_eq_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6) :
    C.rays.length = 5 := by
  rw [C.rays_length_eq_card_otherVertex,
      card_otherVertex_eq_card_sub_one i,
      hcard]
  norm_num

theorem CentreCutRayCycle.rays_length_eq_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (hcard : Fintype.card V = 6) :
    R.rays.length = 5 := by
  rw [R.rays_length_eq_card_otherVertex,
      card_otherVertex_eq_card_sub_one i,
      hcard]
  norm_num

#print axioms card_otherVertex_eq_card_sub_one
#print axioms CentreProjectiveCycle.rays_length_eq_five
#print axioms CentreCutRayCycle.rays_length_eq_five

end JSP000404Research
