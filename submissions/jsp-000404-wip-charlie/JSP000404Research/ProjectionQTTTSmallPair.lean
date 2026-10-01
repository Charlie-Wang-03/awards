import JSP000404Research.SupportTwoThreeMarkedSmallPair
import JSP000404Research.ProjectionQTTTAllNSupport
import Mathlib.Tactic

/-!
# Q/T/T/T support-two centres carry small marked pairs

The analytic support-two geometry is packaged into a finite K4 terminal:
every support-two member of four distinct second-layer centres sees a
delta*lambda-small pair among the other three centres.
-/

namespace JSP000404Research

def SmallPairAmongOtherThree
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam
  ∨ EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam
  ∨ EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam

theorem secondLayer_supportTwo_first_has_small_pair_among_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Ca : CentreProjectiveCycle hp a)
    (haSecond : centreExponent Ca t = n - 2)
    (haSupport :
      positiveSupport (centreQuotient Ca t) = 2) :
    SmallPairAmongOtherThree p delta lam a b c d := by
  have h :=
    supportTwo_three_other_vertices_has_small_pair
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      Ca haSecond haSupport
  rcases h with hbcSmall | hcdSmall | hdbSmall
  · exact Or.inl hbcSmall
  · exact Or.inr (Or.inr hcdSmall)
  · exact Or.inr (Or.inl (by
      simpa [EuclideanGeometry.angle_comm] using hdbSmall))

/-- Symmetric finite K4 form: a designated support-two centre among four
distinct second-layer centres always carries one small opposite edge. -/
theorem secondLayer_supportTwo_member_has_small_pair
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {s x y z a : V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsSecond : centreExponent (C s) t = n - 2)
    (hxSecond : centreExponent (C x) t = n - 2)
    (hySecond : centreExponent (C y) t = n - 2)
    (hzSecond : centreExponent (C z) t = n - 2)
    (haMem : a ∈ ({s,x,y,z} : Finset V))
    (haSupport :
      positiveSupport (centreQuotient (C a) t) = 2) :
    ∃ b c d : V,
      b ∈ ({s,x,y,z} : Finset V) ∧
      c ∈ ({s,x,y,z} : Finset V) ∧
      d ∈ ({s,x,y,z} : Finset V) ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      SmallPairAmongOtherThree p delta lam a b c d := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at haMem
  rcases haMem with rfl | rfl | rfl | rfl
  · refine ⟨x,y,z,by simp,by simp,by simp,
      hsx,hsy,hsz,hxy,hxz,hyz,?_⟩
    exact secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hsx hsy hsz hxy hxz hyz
      (C s) hsSecond haSupport
  · refine ⟨s,y,z,by simp,by simp,by simp,
      hsx.symm,hxy,hxz,hsy,hsz,hyz,?_⟩
    exact secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hsx.symm hxy hxz hsy hsz hyz
      (C x) hxSecond haSupport
  · refine ⟨s,x,z,by simp,by simp,by simp,
      hsy.symm,hxy.symm,hyz,hsx,hsz,hxz,?_⟩
    exact secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hsy.symm hxy.symm hyz hsx hsz hxz
      (C y) hySecond haSupport
  · refine ⟨s,x,y,by simp,by simp,by simp,
      hsz.symm,hxz.symm,hyz.symm,hsx,hsy,hxy,?_⟩
    exact secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hsz.symm hxz.symm hyz.symm hsx hsy hxy
      (C z) hzSecond haSupport

#print axioms secondLayer_supportTwo_first_has_small_pair_among_three
#print axioms secondLayer_supportTwo_member_has_small_pair

end JSP000404Research
