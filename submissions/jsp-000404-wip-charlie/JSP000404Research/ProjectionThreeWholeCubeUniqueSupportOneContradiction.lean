import JSP000404Research.ThreeWholeCubePartnerExtremeProfileContradiction
import JSP000404Research.ThreeWholeCubeSourceExtremeProfileContradiction
import Mathlib.Tactic

/-!
# Unique-support-one whole-cube branch is impossible

Assume one vertex o of the three-whole-cube star is the unique support-one
global order extreme and the other three vertices are support-two.

No consecutive-palette or unit-transition information is needed:

* if o is the source, its retained profile is 000 or 111 and all three
  partners are support-two;
* if o is an owner partner, the source and the other two partners are
  support-two, so the partner-extreme 100/110 contradiction applies.

Thus the unique-support-one branch itself is impossible.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_uniqueSupportOne_impossible
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ o : ProjectionOrdered V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs23 : s₂ ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v c₃)
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
    (hoMem :
      o ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)))
    (hoExtreme :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      GlobalOrderExtreme o)
    (hothers :
      ∀ q : ProjectionOrdered V,
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        q ≠ o →
        positiveSupport (centreQuotient (Cfam q) t) = 2) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  have hactive' : retainedActive R v = {c₁,c₂,c₃} := by
    simpa [R] using hactive
  have hc1V : c₁ ∈ retainedActive R v := by rw [hactive']; simp
  have hc2V : c₂ ∈ retainedActive R v := by rw [hactive']; simp
  have hc3V : c₃ ∈ retainedActive R v := by rw [hactive']; simp

  simp only [Finset.mem_insert, Finset.mem_singleton] at hoMem
  rcases hoMem with rfl | rfl | rfl | rfl

  · have hs1Support :=
      hothers s₁ (by simp) hvs1.symm
    have hs2Support :=
      hothers s₂ (by simp) hvs2.symm
    have hs3Support :=
      hothers s₃ (by simp) hvs3.symm
    rcases hoExtreme with hmin | hmax
    · have hfalse : AllRetainedBitsFalse R v :=
        global_min_allRetainedBitsFalse R hmin
      exact source_000_profile_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc12 hc13 hc23
        hactive h₁ h₂ h₃
        hs1Second hs2Second hs3Second
        hs1Support hs2Support hs3Support
        (by simpa [R] using hfalse c₁ hc1V)
        (by simpa [R] using hfalse c₂ hc2V)
        (by simpa [R] using hfalse c₃ hc3V)
    · have htrue : AllRetainedBitsTrue R v :=
        global_max_allRetainedBitsTrue R hmax
      exact source_111_profile_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc12 hc13 hc23
        hactive h₁ h₂ h₃
        hs1Second hs2Second hs3Second
        hs1Support hs2Support hs3Support
        (by simpa [R] using htrue c₁ hc1V)
        (by simpa [R] using htrue c₂ hc2V)
        (by simpa [R] using htrue c₃ hc3V)

  · have hvSupport :=
      hothers v (by simp) hvs1
    have hs2Support :=
      hothers s₂ (by simp) hs12
    have hs3Support :=
      hothers s₃ (by simp) hs13
    rcases hoExtreme with hmin | hmax
    · exact owner_partner_globalMin_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc12 hc13 hc23
        hactive h₁ h₂ h₃
        hvSecond hs2Second hs3Second
        hvSupport hs2Support hs3Support hmin
    · exact owner_partner_globalMax_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc12 hc13 hc23
        hactive h₁ h₂ h₃
        hvSecond hs2Second hs3Second
        hvSupport hs2Support hs3Support hmax

  · have hvSupport :=
      hothers v (by simp) hvs2
    have hs1Support :=
      hothers s₁ (by simp) hs12.symm
    have hs3Support :=
      hothers s₃ (by simp) hs23
    have hactive₂ :
        let R' :=
          planarStandardResidualColoring
            hp hcap hn1 hdelta0 hdelta1 ht hlam
        retainedActive R' v = {c₂,c₁,c₃} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    rcases hoExtreme with hmin | hmax
    · exact owner_partner_globalMin_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc12.symm hc23 hc13
        (by simpa [R] using hactive₂)
        h₂ h₁ h₃
        hvSecond hs1Second hs3Second
        hvSupport hs1Support hs3Support hmin
    · exact owner_partner_globalMax_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc12.symm hc23 hc13
        (by simpa [R] using hactive₂)
        h₂ h₁ h₃
        hvSecond hs1Second hs3Second
        hvSupport hs1Support hs3Support hmax

  · have hvSupport :=
      hothers v (by simp) hvs3
    have hs1Support :=
      hothers s₁ (by simp) hs13.symm
    have hs2Support :=
      hothers s₂ (by simp) hs23.symm
    have hactive₃ :
        let R' :=
          planarStandardResidualColoring
            hp hcap hn1 hdelta0 hdelta1 ht hlam
        retainedActive R' v = {c₃,c₁,c₂} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    rcases hoExtreme with hmin | hmax
    · exact owner_partner_globalMin_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc13.symm hc23.symm hc12
        (by simpa [R] using hactive₃)
        h₃ h₁ h₂
        hvSecond hs1Second hs2Second
        hvSupport hs1Support hs2Support hmin
    · exact owner_partner_globalMax_supportTwo_impossible
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
        hc13.symm hc23.symm hc12
        (by simpa [R] using hactive₃)
        h₃ h₁ h₂
        hvSecond hs1Second hs2Second
        hvSupport hs1Support hs2Support hmax

#print axioms planar_threeWholeCube_uniqueSupportOne_impossible

end ProjectionOrdered
end JSP000404Research
