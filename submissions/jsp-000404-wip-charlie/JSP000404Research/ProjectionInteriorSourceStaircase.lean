import JSP000404Research.FourCycleOwnerChoiceRigidity
import JSP000404Research.FourSupportTwoOrderedAdjacent
import JSP000404Research.ProjectionSameSideSmallAngleBandCloseness
import Mathlib.Tactic

/-!
# Interior-source colour rigidity in the ordered adjacent terminal

Work in the standard planar residual colouring on a<b<c<d.

If b is the whole-cube source, write x for the left partner owner and y,z for
the two right partner owners.  The source edges b-c and b-d have colours y,z,
while the two straddling partner edges a-c and a-d can a priori use either
endpoint owner.  The four small angles of the ordered-adjacent terminal force
the K2,2 retained colours to be one-step close around the cycle.  With x,y,z
pairwise distinct, the finite owner-choice core forces a-c=y and a-d=z.

The source-at-c statement is the order-dual: a-d=x and b-d=y.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

private theorem fin_val_ne_of_ne
    {n : ℕ} {x y : Fin n}
    (hxy : x ≠ y) :
    x.val ≠ y.val := by
  intro h
  apply hxy
  exact Fin.ext h

theorem orderedAdjacent_source_b_forces_two_colour_cross_staircase
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : ProjectionOrdered V}
    (hab :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      a < b)
    (hbc :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      b < c)
    (hcd :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      c < d)
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hretAC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color a c).val < n)
    (hretAD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color a d).val < n)
    (hretBC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color b c).val < n)
    (hretBD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color b d).val < n)
    (hBC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R b c hretBC = y)
    (hBD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R b d hretBD = z)
    (hAC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R a c hretAC = x ∨
        retainedColor R a c hretAC = y)
    (hAD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R a d hretAD = x ∨
        retainedColor R a d hretAD = z)
    (hpat :
      FourSupportTwoOrderedAdjacentPattern
        (reindexedPoint p) delta lam a b c d) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    let R := planarStandardResidualColoring
      hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
    retainedColor R a c hretAC = y ∧
      retainedColor R a d hretAD = z := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  let R := planarStandardResidualColoring
    hp hcap hn1 hdelta0 hdelta1 ht hlam
  have hac : a < c := hab.trans hbc
  have hbd : b < d := hbc.trans hcd

  unfold FourSupportTwoOrderedAdjacentPattern at hpat

  have hcloseA :=
    right_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hac hcd
      (by simpa [R] using hretAC)
      (by simpa [R] using hretAD)
      (by simpa [R] using hpat.1)
  have hcloseB :=
    right_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hbc hcd
      (by simpa [R] using hretBC)
      (by simpa [R] using hretBD)
      (by simpa [R] using hpat.2.1)
  have hcloseC :=
    left_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hab hbc
      (by simpa [R] using hretAC)
      (by simpa [R] using hretBC)
      (by simpa [R] using hpat.2.2.1)
  have hcloseD :=
    left_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hab hbd
      (by simpa [R] using hretAD)
      (by simpa [R] using hretBD)
      (by simpa [R] using hpat.2.2.2)

  let u := retainedColor R a c (by simpa [R] using hretAC)
  let v := retainedColor R a d (by simpa [R] using hretAD)
  have hu : u = x ∨ u = y := by
    simpa [R,u] using hAC
  have hv : v = x ∨ v = z := by
    simpa [R,v] using hAD
  have hUY : NatOneStepClose u.val y.val := by
    have h := hcloseC
    rw [show retainedColor R b c (by simpa [R] using hretBC) = y by
      simpa [R] using hBC] at h
    simpa [R,u,NatOneStepClose] using h
  have hVZ : NatOneStepClose v.val z.val := by
    have h := hcloseD
    rw [show retainedColor R b d (by simpa [R] using hretBD) = z by
      simpa [R] using hBD] at h
    simpa [R,v,NatOneStepClose] using h
  have hYZ : NatOneStepClose y.val z.val := by
    have h := hcloseB
    rw [show retainedColor R b c (by simpa [R] using hretBC) = y by
      simpa [R] using hBC,
      show retainedColor R b d (by simpa [R] using hretBD) = z by
      simpa [R] using hBD] at h
    simpa [NatOneStepClose] using h
  have hUV : NatOneStepClose u.val v.val := by
    simpa [R,u,v,NatOneStepClose] using hcloseA

  have hrig :=
    interior_source_owner_choices_force_two_colour_staircase
      x.val y.val z.val u.val v.val
      (fin_val_ne_of_ne hxy)
      (fin_val_ne_of_ne hxz)
      (fin_val_ne_of_ne hyz)
      (by
        rcases hu with hu | hu
        · exact Or.inl (congrArg Fin.val hu)
        · exact Or.inr (congrArg Fin.val hu))
      (by
        rcases hv with hv | hv
        · exact Or.inl (congrArg Fin.val hv)
        · exact Or.inr (congrArg Fin.val hv))
      hYZ hUY hVZ hUV

  constructor
  · apply Fin.ext
    exact hrig.1
  · apply Fin.ext
    exact hrig.2

theorem orderedAdjacent_source_c_forces_two_colour_cross_staircase
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : ProjectionOrdered V}
    (hab :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      a < b)
    (hbc :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      b < c)
    (hcd :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      c < d)
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hretAC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color a c).val < n)
    (hretAD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color a d).val < n)
    (hretBC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color b c).val < n)
    (hretBD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color b d).val < n)
    (hAC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R a c hretAC = x)
    (hBC :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R b c hretBC = y)
    (hAD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R a d hretAD = x ∨
        retainedColor R a d hretAD = z)
    (hBD :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      retainedColor R b d hretBD = y ∨
        retainedColor R b d hretBD = z)
    (hpat :
      FourSupportTwoOrderedAdjacentPattern
        (reindexedPoint p) delta lam a b c d) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    let R := planarStandardResidualColoring
      hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
    retainedColor R a d hretAD = x ∧
      retainedColor R b d hretBD = y := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  let R := planarStandardResidualColoring
    hp hcap hn1 hdelta0 hdelta1 ht hlam
  have hac : a < c := hab.trans hbc
  have hbd : b < d := hbc.trans hcd

  unfold FourSupportTwoOrderedAdjacentPattern at hpat

  have hcloseA :=
    right_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hac hcd
      (by simpa [R] using hretAC)
      (by simpa [R] using hretAD)
      (by simpa [R] using hpat.1)
  have hcloseB :=
    right_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hbc hcd
      (by simpa [R] using hretBC)
      (by simpa [R] using hretBD)
      (by simpa [R] using hpat.2.1)
  have hcloseC :=
    left_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hab hbc
      (by simpa [R] using hretAC)
      (by simpa [R] using hretBC)
      (by simpa [R] using hpat.2.2.1)
  have hcloseD :=
    left_same_side_small_angle_labels_one_step_close
      hp hcap hn1 hdelta0 hdeltaHalf ht hlam
      hab hbd
      (by simpa [R] using hretAD)
      (by simpa [R] using hretBD)
      (by simpa [R] using hpat.2.2.2)

  let u := retainedColor R a d (by simpa [R] using hretAD)
  let v := retainedColor R b d (by simpa [R] using hretBD)
  have hu : u = z ∨ u = x := by
    rcases hAD with h | h
    · exact Or.inr (by simpa [R,u] using h)
    · exact Or.inl (by simpa [R,u] using h)
  have hv : v = z ∨ v = y := by
    rcases hBD with h | h
    · exact Or.inr (by simpa [R,v] using h)
    · exact Or.inl (by simpa [R,v] using h)
  have hXY : NatOneStepClose x.val y.val := by
    have h := hcloseC
    rw [show retainedColor R a c (by simpa [R] using hretAC) = x by
      simpa [R] using hAC,
      show retainedColor R b c (by simpa [R] using hretBC) = y by
      simpa [R] using hBC] at h
    simpa [NatOneStepClose] using h
  have hUX : NatOneStepClose u.val x.val := by
    have h := hcloseA
    rw [show retainedColor R a c (by simpa [R] using hretAC) = x by
      simpa [R] using hAC] at h
    have h' : NatOneStepClose x.val u.val := by
      simpa [R,u,NatOneStepClose] using h
    exact natOneStepClose_symm h'
  have hVY : NatOneStepClose v.val y.val := by
    have h := hcloseB
    rw [show retainedColor R b c (by simpa [R] using hretBC) = y by
      simpa [R] using hBC] at h
    have h' : NatOneStepClose y.val v.val := by
      simpa [R,v,NatOneStepClose] using h
    exact natOneStepClose_symm h'
  have hUV : NatOneStepClose u.val v.val := by
    simpa [R,u,v,NatOneStepClose] using hcloseD

  have hrig :=
    interior_source_owner_choices_force_two_colour_staircase
      z.val x.val y.val u.val v.val
      (fin_val_ne_of_ne hxz).symm
      (fin_val_ne_of_ne hyz).symm
      (fin_val_ne_of_ne hxy)
      (by
        rcases hu with hu | hu
        · exact Or.inl (congrArg Fin.val hu)
        · exact Or.inr (congrArg Fin.val hu))
      (by
        rcases hv with hv | hv
        · exact Or.inl (congrArg Fin.val hv)
        · exact Or.inr (congrArg Fin.val hv))
      hXY hUX hVY hUV

  constructor
  · apply Fin.ext
    exact hrig.1
  · apply Fin.ext
    exact hrig.2

#print axioms orderedAdjacent_source_b_forces_two_colour_cross_staircase
#print axioms orderedAdjacent_source_c_forces_two_colour_cross_staircase

end ProjectionOrdered
end JSP000404Research
