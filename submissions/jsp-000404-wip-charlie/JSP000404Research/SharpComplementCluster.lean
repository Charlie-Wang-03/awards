import JSP000404Research.SharpOuterAngles
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Complement clusters around a distinguished sharp centre

Fix a distinguished centre s.  Say that another centre i has a
SharpComplementCluster if every angle at i formed by two vertices different
from both i and s is at most delta*lambda.

For a support-two deficit-two centre in the presence of a sharp centre, the
intended geometric bridge is that the two positive quotient gaps isolate the
ray to s, while all remaining zero-quotient gaps have total width at most
delta/t.  Hence all non-s rays form exactly such a narrow complement cluster.

This file isolates the global consequence of that bridge.

If two distinct centres i,j both have narrow complement clusters relative to
the same s and there is a fourth vertex k, then triangle i-j-k has angles at i
and j at most delta*lambda.  The global cap bounds the angle at k by
pi-lambda.  Since 2*delta<1, the three angles cannot sum to pi.

Thus, once the local support-two -> complement-cluster bridge is supplied,
there can be at most one support-two deficit-two centre around a sharp centre
in every configuration with at least four points.
-/

namespace JSP000404Research

open Real

def SharpComplementClusterAt
    {V : Type*} (p : V → Plane)
    (s i : V) (delta lam : ℝ) : Prop :=
  ∀ j k : V,
    j ≠ i →
    k ≠ i →
    j ≠ k →
    j ≠ s →
    k ≠ s →
    EuclideanGeometry.angle (p j) (p i) (p k) ≤
      delta * lam

theorem no_two_complement_clusters_with_fourth
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {s i j k : V}
    (hsi : s ≠ i)
    (hsj : s ≠ j)
    (hsk : s ≠ k)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hi : SharpComplementClusterAt p s i delta lam)
    (hj : SharpComplementClusterAt p s j delta lam) :
    False := by
  have hangleI :
      EuclideanGeometry.angle (p j) (p i) (p k) ≤
        delta * lam :=
    hi j k hij.symm hik hjk hsj.symm hsk.symm
  have hangleJ :
      EuclideanGeometry.angle (p i) (p j) (p k) ≤
        delta * lam :=
    hj i k hij hik hjk hsi.symm hsk.symm
  have hangleK :
      EuclideanGeometry.angle (p i) (p k) (p j) ≤
        Real.pi - lam :=
    hcap i k j hik hjk hij
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p i) (p₂ := p j) (p k)
      (hp.ne hij)
  have hcomm :
      EuclideanGeometry.angle (p k) (p i) (p j) =
        EuclideanGeometry.angle (p j) (p i) (p k) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm] at hsum
  nlinarith

/-- Finite-index consequence: relative to a fixed s, at most one vertex in a
family can carry a complement-cluster certificate once a fourth vertex exists
for every pair. -/
theorem complementCluster_filter_card_le_one_fin
    {m : ℕ}
    {p : Fin m → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hm : 4 ≤ m)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (s : Fin m)
    (Good : Fin m → Prop)
    (hgood :
      ∀ i, Good i →
        i ≠ s ∧
        SharpComplementClusterAt p s i delta lam) :
    ((Finset.univ : Finset (Fin m)).filter Good).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra hij
  have his := (hgood i hi).1
  have hjs := (hgood j hj).1
  obtain ⟨k, hki, hkj⟩ :=
    Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < m)
  by_cases hks : k = s
  · -- There is still a fourth vertex distinct from s,i,j.
    let S : Finset (Fin m) := {s, i, j}
    have hcardS : S.card = 3 := by
      simp [his.symm, hjs.symm, hij]
    have hcardUniv : (Finset.univ : Finset (Fin m)).card = m := by
      simp
    have hproper : S ≠ Finset.univ := by
      intro h
      have hc := congrArg Finset.card h
      rw [hcardS, hcardUniv] at hc
      omega
    obtain ⟨k', hk'not⟩ := Finset.exists_mem_not_mem_of_card_lt
      (s := S) (t := (Finset.univ : Finset (Fin m)))
      (by
        rw [hcardS, hcardUniv]
        omega)
    have hk'univ : k' ∈ (Finset.univ : Finset (Fin m)) := hk'not.1
    have hk'S : k' ∉ S := hk'not.2
    have hk's : k' ≠ s := by
      intro h
      subst k'
      exact hk'S (by simp [S])
    have hk'i : k' ≠ i := by
      intro h
      subst k'
      exact hk'S (by simp [S])
    have hk'j : k' ≠ j := by
      intro h
      subst k'
      exact hk'S (by simp [S])
    exact no_two_complement_clusters_with_fourth
      hp hcap hdelta hlampos
      his.symm hjs.symm hk's.symm hij
      hk'i.symm hk'j.symm
      (hgood i hi).2 (hgood j hj).2
  · exact no_two_complement_clusters_with_fourth
      hp hcap hdelta hlampos
      his.symm hjs.symm hks.symm hij
      hki.symm hkj.symm
      (hgood i hi).2 (hgood j hj).2

#print axioms no_two_complement_clusters_with_fourth

end JSP000404Research
