import JSP000404Research.GenericProjectiveLine
import JSP000404Research.CentreCycleChoiceInvariant
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Negative/nonnegative blocks of generic projective line angles

Fix a projection-ordered centre i.  Every incident unoriented line has one
generic line angle in the common branch (base,base+pi), where base<0 and
base+pi>0.

Split the non-centre vertices into

  negative    : genericLineAngle < 0,
  nonnegative : 0 <= genericLineAngle,

and sort each block by genericLineAngle.

The generic projective cut sees the cyclic order

  negative ++ nonnegative.

The canonical [0,pi) projective cut sees

  nonnegative ++ negative,

where every angle in the negative block is shifted by +pi.

This file builds the two sorted blocks and proves that the latter vertex list
is a complete, duplicate-free canonical theta-sorted ray cycle.
-/

namespace JSP000404Research
namespace ProjectionOrdered

noncomputable def genericLineAngleAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) : ℝ :=
  genericLineAngle hp i (ofOriginal j.1)

noncomputable def genericLineOrderKey
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) :
    ℝ ×ₗ V :=
  toLex (genericLineAngleAt hp i j, j.1)

theorem genericLineOrderKey_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    Function.Injective (genericLineOrderKey hp i) := by
  intro a b hab
  apply Subtype.ext
  have hsecond :
      (ofLex (genericLineOrderKey hp i a)).2 =
        (ofLex (genericLineOrderKey hp i b)).2 :=
    congrArg (fun z : ℝ ×ₗ V => (ofLex z).2) hab
  simpa [genericLineOrderKey] using hsecond

noncomputable def otherVertexGenericLineOrder
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    LinearOrder (OtherVertex i.toOriginal) :=
  LinearOrder.lift'
    (genericLineOrderKey hp i)
    (genericLineOrderKey_injective hp i)

theorem genericLineAngleAt_le_of_order_le
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    {a b : OtherVertex i.toOriginal}
    (hab :
      @LE.le (OtherVertex i.toOriginal)
        (otherVertexGenericLineOrder hp i).toLE a b) :
    genericLineAngleAt hp i a ≤
      genericLineAngleAt hp i b := by
  have hkey :
      genericLineOrderKey hp i a ≤
        genericLineOrderKey hp i b := hab
  have hfst := Prod.Lex.monotone_fst _ _ hkey
  simpa [genericLineOrderKey] using hfst

noncomputable def genericNegativeSet
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    Finset (OtherVertex i.toOriginal) := by
  classical
  exact Finset.univ.filter fun j =>
    genericLineAngleAt hp i j < 0

noncomputable def genericNonnegativeSet
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    Finset (OtherVertex i.toOriginal) := by
  classical
  exact Finset.univ.filter fun j =>
    ¬ genericLineAngleAt hp i j < 0

noncomputable def genericNegativeRays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    List (OtherVertex i.toOriginal) := by
  letI : LinearOrder (OtherVertex i.toOriginal) :=
    otherVertexGenericLineOrder hp i
  exact (genericNegativeSet hp i).sort

noncomputable def genericNonnegativeRays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    List (OtherVertex i.toOriginal) := by
  letI : LinearOrder (OtherVertex i.toOriginal) :=
    otherVertexGenericLineOrder hp i
  exact (genericNonnegativeSet hp i).sort

@[simp] theorem genericNegativeRays_toFinset
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNegativeRays hp i).toFinset =
      genericNegativeSet hp i := by
  classical
  simp [genericNegativeRays]

@[simp] theorem genericNonnegativeRays_toFinset
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNonnegativeRays hp i).toFinset =
      genericNonnegativeSet hp i := by
  classical
  simp [genericNonnegativeRays]

theorem genericNegativeRays_nodup
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNegativeRays hp i).Nodup := by
  classical
  simp [genericNegativeRays]

theorem genericNonnegativeRays_nodup
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNonnegativeRays hp i).Nodup := by
  classical
  simp [genericNonnegativeRays]

theorem mem_genericNegativeRays_iff
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) :
    j ∈ genericNegativeRays hp i ↔
      genericLineAngleAt hp i j < 0 := by
  classical
  rw [← List.mem_toFinset,
      genericNegativeRays_toFinset]
  simp [genericNegativeSet]

theorem mem_genericNonnegativeRays_iff
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) :
    j ∈ genericNonnegativeRays hp i ↔
      0 ≤ genericLineAngleAt hp i j := by
  classical
  rw [← List.mem_toFinset,
      genericNonnegativeRays_toFinset]
  simp [genericNonnegativeSet, not_lt]

theorem genericNegativeRays_angle_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNegativeRays hp i).Pairwise
      (fun a b =>
        genericLineAngleAt hp i a ≤
          genericLineAngleAt hp i b) := by
  classical
  letI : LinearOrder (OtherVertex i.toOriginal) :=
    otherVertexGenericLineOrder hp i
  have hpair :
      (genericNegativeRays hp i).Pairwise
        (fun a b : OtherVertex i.toOriginal => a ≤ b) := by
    exact Finset.pairwise_sort
      (genericNegativeSet hp i) (· ≤ ·)
  exact hpair.imp fun a b hab =>
    genericLineAngleAt_le_of_order_le hp i hab

theorem genericNonnegativeRays_angle_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNonnegativeRays hp i).Pairwise
      (fun a b =>
        genericLineAngleAt hp i a ≤
          genericLineAngleAt hp i b) := by
  classical
  letI : LinearOrder (OtherVertex i.toOriginal) :=
    otherVertexGenericLineOrder hp i
  have hpair :
      (genericNonnegativeRays hp i).Pairwise
        (fun a b : OtherVertex i.toOriginal => a ≤ b) := by
    exact Finset.pairwise_sort
      (genericNonnegativeSet hp i) (· ≤ ·)
  exact hpair.imp fun a b hab =>
    genericLineAngleAt_le_of_order_le hp i hab

noncomputable def genericCanonicalRays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    List (OtherVertex i.toOriginal) :=
  genericNonnegativeRays hp i ++
    genericNegativeRays hp i

theorem genericCanonicalRays_complete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericCanonicalRays hp i).toFinset =
      Finset.univ := by
  classical
  ext j
  by_cases hneg :
      genericLineAngleAt hp i j < 0
  · simp [genericCanonicalRays,
      genericNegativeSet, genericNonnegativeSet,
      hneg]
  · simp [genericCanonicalRays,
      genericNegativeSet, genericNonnegativeSet,
      hneg]

theorem genericCanonicalRays_nodup
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericCanonicalRays hp i).Nodup := by
  classical
  apply (genericNonnegativeRays_nodup hp i).append
    (genericNegativeRays_nodup hp i)
  rw [List.disjoint_iff_ne]
  intro a ha b hb hab
  subst b
  have hnon :
      0 ≤ genericLineAngleAt hp i a :=
    (mem_genericNonnegativeRays_iff hp i a).1 ha
  have hneg :
      genericLineAngleAt hp i a < 0 :=
    (mem_genericNegativeRays_iff hp i a).1 hb
  linarith

theorem canonicalTheta_eq_generic_of_nonnegative_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    {j : OtherVertex i.toOriginal}
    (hj : j ∈ genericNonnegativeRays hp i) :
    rayThetaAt hp i.toOriginal j =
      genericLineAngleAt hp i j := by
  simpa [genericLineAngleAt] using
    (canonicalTheta_eq_genericLineAngle_of_nonneg
      hp i j
      ((mem_genericNonnegativeRays_iff hp i j).1 hj))

theorem canonicalTheta_eq_generic_add_pi_of_negative_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    {j : OtherVertex i.toOriginal}
    (hj : j ∈ genericNegativeRays hp i) :
    rayThetaAt hp i.toOriginal j =
      genericLineAngleAt hp i j + Real.pi := by
  simpa [genericLineAngleAt] using
    (canonicalTheta_eq_genericLineAngle_add_pi_of_neg
      hp i j
      ((mem_genericNegativeRays_iff hp i j).1 hj))

theorem genericNonnegativeRays_theta_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNonnegativeRays hp i).Pairwise
      (fun a b =>
        rayThetaAt hp i.toOriginal a ≤
          rayThetaAt hp i.toOriginal b) := by
  let rays := genericNonnegativeRays hp i
  have hgen :
      (rays.map (genericLineAngleAt hp i)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact genericNonnegativeRays_angle_pairwise hp i
  have hmap :
      rays.map (rayThetaAt hp i.toOriginal) =
        rays.map (genericLineAngleAt hp i) := by
    apply List.map_congr_left
    intro j hj
    exact canonicalTheta_eq_generic_of_nonnegative_mem
      hp i hj
  rw [← List.pairwise_map]
  rw [hmap]
  exact hgen

theorem genericNegativeRays_theta_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericNegativeRays hp i).Pairwise
      (fun a b =>
        rayThetaAt hp i.toOriginal a ≤
          rayThetaAt hp i.toOriginal b) := by
  let rays := genericNegativeRays hp i
  have hgen :
      (rays.map
        (fun j => genericLineAngleAt hp i j + Real.pi)).Pairwise
          (· ≤ ·) := by
    rw [List.pairwise_map]
    exact (genericNegativeRays_angle_pairwise hp i).imp
      fun _ _ h => by linarith
  have hmap :
      rays.map (rayThetaAt hp i.toOriginal) =
        rays.map
          (fun j => genericLineAngleAt hp i j + Real.pi) := by
    apply List.map_congr_left
    intro j hj
    exact canonicalTheta_eq_generic_add_pi_of_negative_mem
      hp i hj
  rw [← List.pairwise_map]
  rw [hmap]
  exact hgen

theorem genericCanonicalRays_theta_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericCanonicalRays hp i).Pairwise
      (fun a b =>
        rayThetaAt hp i.toOriginal a ≤
          rayThetaAt hp i.toOriginal b) := by
  classical
  rw [genericCanonicalRays, List.pairwise_append]
  refine ⟨genericNonnegativeRays_theta_pairwise hp i,
    genericNegativeRays_theta_pairwise hp i, ?_⟩
  intro a ha b hb
  have hAneq :
      i ≠ ofOriginal a.1 := by
    intro h
    apply a.2
    exact (congrArg toOriginal h).symm
  have hBneq :
      i ≠ ofOriginal b.1 := by
    intro h
    apply b.2
    exact (congrArg toOriginal h).symm
  have hA := genericLineAngle_mem hp hAneq
  have hB := genericLineAngle_mem hp hBneq
  rw [canonicalTheta_eq_generic_of_nonnegative_mem hp i ha,
      canonicalTheta_eq_generic_add_pi_of_negative_mem hp i hb]
  dsimp [genericLineAngleAt]
  have hAup := hA.2
  have hBlo := hB.1
  linarith

noncomputable def genericCanonicalCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (hother : Nonempty (OtherVertex i.toOriginal)) :
    CentreProjectiveCycle hp i.toOriginal where
  rays := genericCanonicalRays hp i
  complete := genericCanonicalRays_complete hp i
  nodup := genericCanonicalRays_nodup hp i
  nonempty := by
    obtain ⟨j⟩ := hother
    intro hnil
    have hj :
        j ∈ genericCanonicalRays hp i := by
      have hjFin :
          j ∈ (genericCanonicalRays hp i).toFinset := by
        rw [genericCanonicalRays_complete hp i]
        simp
      simpa using hjFin
    simpa [hnil] using hj
  theta_sorted := genericCanonicalRays_theta_pairwise hp i

#print axioms genericLineOrderKey_injective
#print axioms genericNegativeRays_angle_pairwise
#print axioms genericCanonicalRays_complete
#print axioms genericCanonicalRays_theta_pairwise
#print axioms genericCanonicalCycle

end ProjectionOrdered
end JSP000404Research
