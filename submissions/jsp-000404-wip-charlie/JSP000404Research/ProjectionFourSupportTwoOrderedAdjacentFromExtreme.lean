import JSP000404Research.ProjectionOrderedSupportTwoAdjacent
import JSP000404Research.FourSupportTwoSecondLayerBridge
import Mathlib.Tactic

/-!
# Ordered adjacent terminal from an already known global extreme

This module isolates the geometry/combinatorics after the four-point
whole-cube core has supplied a global order extreme.

No WholeCubeQTPair or retained-code-star hypothesis appears here.  Thus the
checked chain is:

  global extreme
  + four projected-loss second-layer support-two centres
  -> sort the four vertices
  -> four-support-two three-pattern terminal
  -> projected-loss opposite-side obstruction
  -> unique ordered-adjacent pattern.

The heavier whole-cube retained-code argument is a separate bridge.
-/

namespace JSP000404Research

theorem three_distinct_strict_order_cases_light
    {V : Type*} [LinearOrder V]
    {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (x < y ∧ y < z) ∨
    (x < z ∧ z < y) ∨
    (y < x ∧ x < z) ∨
    (y < z ∧ z < x) ∨
    (z < x ∧ x < y) ∨
    (z < y ∧ y < x) := by
  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · rcases lt_or_gt_of_ne hyz with hyzlt | hzylt
    · exact Or.inl ⟨hxylt, hyzlt⟩
    · rcases lt_or_gt_of_ne hxz with hxzlt | hzxlt
      · exact Or.inr (Or.inl ⟨hxzlt, hzylt⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hzxlt, hxylt⟩))))
  · rcases lt_or_gt_of_ne hxz with hxzlt | hzxlt
    · exact Or.inr (Or.inr (Or.inl ⟨hyxlt, hxzlt⟩))
    · rcases lt_or_gt_of_ne hyz with hyzlt | hzylt
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hyzlt, hzxlt⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hzylt, hyxlt⟩))))

theorem four_with_global_min_has_sorted_permutation_light
    {V : Type*} [LinearOrder V]
    {o x y z : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hoz : o ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmin : ∀ w : V, w ≠ o → o < w) :
    ∃ a b c d : V,
      ({a,b,c,d} : Finset V) = {o,x,y,z} ∧
      a < b ∧ b < c ∧ c < d := by
  have hoxlt := hmin x hox.symm
  have hoylt := hmin y hoy.symm
  have hozlt := hmin z hoz.symm
  rcases three_distinct_strict_order_cases_light hxy hxz hyz with
    hxyz | hxzy | hyxz | hyzx | hzxy | hzyx
  · exact ⟨o,x,y,z,rfl,hoxlt,hxyz.1,hxyz.2⟩
  · refine ⟨o,x,z,y,?_,hoxlt,hxzy.1,hxzy.2⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨o,y,x,z,?_,hoylt,hyxz.1,hyxz.2⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨o,y,z,x,?_,hoylt,hyzx.1,hyzx.2⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨o,z,x,y,?_,hozlt,hzxy.1,hzxy.2⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨o,z,y,x,?_,hozlt,hzyx.1,hzyx.2⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]

theorem four_with_global_max_has_sorted_permutation_light
    {V : Type*} [LinearOrder V]
    {o x y z : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hoz : o ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmax : ∀ w : V, w ≠ o → w < o) :
    ∃ a b c d : V,
      ({a,b,c,d} : Finset V) = {o,x,y,z} ∧
      a < b ∧ b < c ∧ c < d := by
  have hxolt := hmax x hox.symm
  have hyolt := hmax y hoy.symm
  have hzolt := hmax z hoz.symm
  rcases three_distinct_strict_order_cases_light hxy hxz hyz with
    hxyz | hxzy | hyxz | hyzx | hzxy | hzyx
  · refine ⟨x,y,z,o,?_,hxyz.1,hxyz.2,hzolt⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨x,z,y,o,?_,hxzy.1,hxzy.2,hyolt⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨y,x,z,o,?_,hyxz.1,hyxz.2,hzolt⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨y,z,x,o,?_,hyzx.1,hyzx.2,hxolt⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨z,x,y,o,?_,hzxy.1,hzxy.2,hyolt⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]
  · refine ⟨z,y,x,o,?_,hzyx.1,hzyx.2,hxolt⟩
    ext q; simp [or_assoc, or_left_comm, or_comm]

namespace ProjectionOrdered

open OrderedEdgeColoring

def FourPointGlobalExtreme
    {V : Type*} [LinearOrder V]
    (v s₁ s₂ s₃ : V) : Prop :=
  ((∀ w : V, w ≠ v → v < w) ∨ (∀ w : V, w ≠ v → w < v))
  ∨
  ((∀ w : V, w ≠ s₁ → s₁ < w) ∨ (∀ w : V, w ≠ s₁ → w < s₁))
  ∨
  ((∀ w : V, w ≠ s₂ → s₂ < w) ∨ (∀ w : V, w ≠ s₂ → w < s₂))
  ∨
  ((∀ w : V, w ≠ s₃ → s₃ < w) ∨ (∀ w : V, w ≠ s₃ → w < s₃))

theorem planar_fourSupportTwo_of_globalExtreme_ordered_adjacent_terminal
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
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁) (hvs2 : v ≠ s₂) (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hvLoss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hs1Loss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hs2Loss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hs3Loss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      s₃ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
    (hvSupport : positiveSupport (centreQuotient (Cfam v) t) = 2)
    (hs1Support : positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support : positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support : positiveSupport (centreQuotient (Cfam s₃) t) = 2)
    (hextreme :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      FourPointGlobalExtreme v s₁ s₂ s₃) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    ∃ a b c d : ProjectionOrdered V,
      ({a,b,c,d} : Finset (ProjectionOrdered V)) = {v,s₁,s₂,s₃} ∧
      a < b ∧ b < c ∧ c < d ∧
      FourSupportTwoOrderedAdjacentPattern
        (reindexedPoint p) delta lam a b c d := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R := planarStandardResidualColoring
    hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent (t := t) hp Cfam
  let S : Finset (ProjectionOrdered V) := {v,s₁,s₂,s₃}

  have loss_of_mem :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        q ∈ projectedLossVertices R exponent := by
    intro q hq
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa [R, exponent] using hvLoss
    · simpa [R, exponent] using hs1Loss
    · simpa [R, exponent] using hs2Loss
    · simpa [R, exponent] using hs3Loss

  have second_of_mem :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        centreExponent (Cfam q) t = n - 2 := by
    intro q hq
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvSecond
    · exact hs1Second
    · exact hs2Second
    · exact hs3Second

  have support_of_mem :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        positiveSupport (centreQuotient (Cfam q) t) = 2 := by
    intro q hq
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvSupport
    · exact hs1Support
    · exact hs2Support
    · exact hs3Support

  have sorted_of_extreme :
      ∃ a b c d : ProjectionOrdered V,
        ({a,b,c,d} : Finset (ProjectionOrdered V)) = S ∧
        a < b ∧ b < c ∧ c < d := by
    rcases hextreme with hv | hs1 | hs2 | hs3
    · rcases hv with hmin | hmax
      · simpa [S] using
          (four_with_global_min_has_sorted_permutation_light
            hvs1 hvs2 hvs3 hs12 hs13 hs23 hmin)
      · simpa [S] using
          (four_with_global_max_has_sorted_permutation_light
            hvs1 hvs2 hvs3 hs12 hs13 hs23 hmax)
    · rcases hs1 with hmin | hmax
      · simpa [S] using
          (four_with_global_min_has_sorted_permutation_light
            hvs1.symm hs12 hs13 hvs2 hs23 hvs3 hmin)
      · simpa [S] using
          (four_with_global_max_has_sorted_permutation_light
            hvs1.symm hs12 hs13 hvs2 hs23 hvs3 hmax)
    · rcases hs2 with hmin | hmax
      · simpa [S] using
          (four_with_global_min_has_sorted_permutation_light
            hvs2.symm hs12.symm hs23 hvs1 hs13 hvs3 hmin)
      · simpa [S] using
          (four_with_global_max_has_sorted_permutation_light
            hvs2.symm hs12.symm hs23 hvs1 hs13 hvs3 hmax)
    · rcases hs3 with hmin | hmax
      · simpa [S] using
          (four_with_global_min_has_sorted_permutation_light
            hvs3.symm hs13.symm hs23.symm hvs1 hvs2 hs12 hmin)
      · simpa [S] using
          (four_with_global_max_has_sorted_permutation_light
            hvs3.symm hs13.symm hs23.symm hvs1 hvs2 hs12 hmax)

  obtain ⟨a,b,c,d,hset,hab,hbc,hcd⟩ := sorted_of_extreme
  have haS : a ∈ S := by rw [← hset]; simp
  have hbS : b ∈ S := by rw [← hset]; simp
  have hcS : c ∈ S := by rw [← hset]; simp
  have hdS : d ∈ S := by rw [← hset]; simp

  have hac : a ≠ c := ne_of_lt (hab.trans hbc)
  have had : a ≠ d := ne_of_lt (hab.trans (hbc.trans hcd))
  have hbd : b ≠ d := ne_of_lt (hbc.trans hcd)

  have hpat3 :=
    four_supportTwo_secondLayer_reduce_to_derangement_three
      (reindexedPoint_injective hp)
      (angleCap_reindexed hcap)
      (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      (ne_of_lt hab) hac had
      (ne_of_lt hbc) hbd (ne_of_lt hcd)
      (second_of_mem haS)
      (second_of_mem hbS)
      (second_of_mem hcS)
      (second_of_mem hdS)
      (support_of_mem haS)
      (support_of_mem hbS)
      (support_of_mem hcS)
      (support_of_mem hdS)

  have hadj :=
    projectedLoss_ordered_pattern3_reduce_to_adjacent
      hp hcap hn1 hdelta0 hdelta1 ht hlam Cfam
      hab hbc hcd
      (by simpa [R, exponent] using loss_of_mem hbS)
      hpat3

  exact ⟨a,b,c,d,by simpa [S] using hset,hab,hbc,hcd,hadj⟩

#print axioms planar_fourSupportTwo_of_globalExtreme_ordered_adjacent_terminal

end ProjectionOrdered
end JSP000404Research
