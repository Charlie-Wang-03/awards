import JSP000404Research.ThreeWholeCubeInternalEdgeMatrix
import JSP000404Research.ThreeWholeCubeGlobalExtreme
import JSP000404Research.ProjectionSameBandSameSideAngle
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Same-band angle rigidity in a three-whole-cube source-extreme star

Assume the source v itself is the global order minimum of a saturated
three-whole-cube star and its partners satisfy s1 < s2 < s3.

The source retained bits at c1,c2,c3 are all false.  Hence the internal edge
matrix gives

  color(v,sj)=cj,
  color(s1,s2)=c2,
  color(s1,s3)=c3,
  color(s2,s3)=c3.

Therefore all three edges ending at s3 have one colour, and the two edges
v-s2 and s1-s2 have one colour.  The generic-projection same-band bridge then
gives all three star angles at s3 < lambda and angle(v,s2,s1)<lambda.

The global-maximum case is the exact dual.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem retainedCompletionWords_nonempty
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (retainedCompletionWords C v).Nonempty := by
  apply Finset.card_pos.mp
  rw [retainedCompletionWords_card]
  positivity

theorem threeWholeCube_source_globalMin_sameBand_angles
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁) (hvs2 : v ≠ s₂) (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂) (hc13 : c₁ ≠ c₃) (hc23 : c₂ ≠ c₃)
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hc1V :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      c₁ ∈ retainedActive R v)
    (hc2V :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      c₂ ∈ retainedActive R v)
    (hc3V :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      c₃ ∈ retainedActive R v)
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      WholeCubeQTPair R s₃ v c₃)
    (hmin : ∀ w : ProjectionOrdered V, w ≠ v → v < w)
    (hs12lt : s₁ < s₂)
    (hs23lt : s₂ < s₃) :
    EuclideanGeometry.angle
        (reindexedPoint p v) (reindexedPoint p s₃) (reindexedPoint p s₁) < lam ∧
    EuclideanGeometry.angle
        (reindexedPoint p v) (reindexedPoint p s₃) (reindexedPoint p s₂) < lam ∧
    EuclideanGeometry.angle
        (reindexedPoint p s₁) (reindexedPoint p s₃) (reindexedPoint p s₂) < lam ∧
    EuclideanGeometry.angle
        (reindexedPoint p v) (reindexedPoint p s₂) (reindexedPoint p s₁) < lam := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let R := planarStandardResidualColoring hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    have hprof :=
      genericProjection_lowerBranch_profile_hypotheses
        hp hcap hn hdelta0 hdelta1 ht hlam Cfam
    exact Nat.le_of_lt (by simpa [exponent] using hprof.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    have hprof :=
      genericProjection_lowerBranch_profile_hypotheses
        hp hcap hn hdelta0 hdelta1 ht hlam Cfam
    simpa [R, exponent] using hprof.2 q

  have hfalse : AllRetainedBitsFalse R v :=
    projectedLoss_global_min_allFalse
      R exponent (by simpa [R, exponent] using hvLoss) hmin
  have hb1 : retainedBit R v c₁ = false := hfalse c₁ (by simpa [R] using hc1V)
  have hb2 : retainedBit R v c₂ = false := hfalse c₂ (by simpa [R] using hc2V)
  have hb3 : retainedBit R v c₃ = false := hfalse c₃ (by simpa [R] using hc3V)

  have hv1 : v < s₁ := hmin s₁ hvs1
  have hv2 : v < s₂ := hmin s₂ hvs2
  have hv3 : v < s₃ := hmin s₃ hvs3
  have hs13lt : s₁ < s₃ := hs12lt.trans hs23lt

  obtain ⟨w1, hw1⟩ := retainedCompletionWords_nonempty R s₁
  obtain ⟨w2, hw2⟩ := retainedCompletionWords_nonempty R s₂
  obtain ⟨w3, hw3⟩ := retainedCompletionWords_nonempty R s₃

  have hsource1 :=
    wholeCube_source_partner_edge_owner_colour_of_completion
      R exponent hexp hone hvs1.symm
      (by simpa [R, exponent] using hvLoss)
      (by simpa [R] using hc1V) hw1 (by simpa [R] using h₁)
  have hsource2 :=
    wholeCube_source_partner_edge_owner_colour_of_completion
      R exponent hexp hone hvs2.symm
      (by simpa [R, exponent] using hvLoss)
      (by simpa [R] using hc2V) hw2 (by simpa [R] using h₂)
  have hsource3 :=
    wholeCube_source_partner_edge_owner_colour_of_completion
      R exponent hexp hone hvs3.symm
      (by simpa [R, exponent] using hvLoss)
      (by simpa [R] using hc3V) hw3 (by simpa [R] using h₃)

  obtain ⟨hretV2,hcolV2⟩ : ∃ hret : (R.color v s₂).val < n,
      retainedColor R v s₂ hret = c₂ := by
    rcases hsource2 with hbad | hgood
    · obtain ⟨hsv,_,_⟩ := hbad
      exact False.elim (lt_asymm hsv hv2)
    · exact hgood.2
  obtain ⟨hretV3,hcolV3⟩ : ∃ hret : (R.color v s₃).val < n,
      retainedColor R v s₃ hret = c₃ := by
    rcases hsource3 with hbad | hgood
    · obtain ⟨hsv,_,_⟩ := hbad
      exact False.elim (lt_asymm hsv hv3)
    · exact hgood.2

  have hret12 :
      (R.color s₁ s₂).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone
      (by
        have hs1Loss : s₁ ∈ projectedLossVertices R exponent := by
          have hact := h₁.1
          rw [hact]
          simpa [R, exponent] using hvLoss
        exact hs1Loss)
      hs12lt
  have hret13 :
      (R.color s₁ s₃).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone
      (by
        have hs1Loss : s₁ ∈ projectedLossVertices R exponent := by
          have hact := h₁.1
          rw [hact]
          simpa [R, exponent] using hvLoss
        exact hs1Loss)
      hs13lt
  have hret23 :
      (R.color s₂ s₃).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone
      (by
        have hs2Loss : s₂ ∈ projectedLossVertices R exponent := by
          have hact := h₂.1
          rw [hact]
          simpa [R, exponent] using hvLoss
        exact hs2Loss)
      hs23lt

  have hcol12 :=
    wholeCube_partner_edge_eq_upper_owner_of_false_false
      R hc12
      (by simpa [R] using hc1V) (by simpa [R] using hc2V)
      (by simpa [R] using h₁) (by simpa [R] using h₂)
      hs12lt hret12 hb1 hb2
  have hcol13 :=
    wholeCube_partner_edge_eq_upper_owner_of_false_false
      R hc13
      (by simpa [R] using hc1V) (by simpa [R] using hc3V)
      (by simpa [R] using h₁) (by simpa [R] using h₃)
      hs13lt hret13 hb1 hb3
  have hcol23 :=
    wholeCube_partner_edge_eq_upper_owner_of_false_false
      R hc23
      (by simpa [R] using hc2V) (by simpa [R] using hc3V)
      (by simpa [R] using h₂) (by simpa [R] using h₃)
      hs23lt hret23 hb2 hb3

  have fullEqV3_13 : R.color v s₃ = R.color s₁ s₃ := by
    apply Fin.ext
    have h1 := congrArg Fin.val hcolV3
    have h2 := congrArg Fin.val hcol13
    simpa [retainedColor] using h1.trans h2.symm
  have fullEqV3_23 : R.color v s₃ = R.color s₂ s₃ := by
    apply Fin.ext
    have h1 := congrArg Fin.val hcolV3
    have h2 := congrArg Fin.val hcol23
    simpa [retainedColor] using h1.trans h2.symm
  have fullEq13_23 : R.color s₁ s₃ = R.color s₂ s₃ := fullEqV3_13.symm.trans fullEqV3_23

  have fullEqV2_12 : R.color v s₂ = R.color s₁ s₂ := by
    apply Fin.ext
    have h1 := congrArg Fin.val hcolV2
    have h2 := congrArg Fin.val hcol12
    simpa [retainedColor] using h1.trans h2.symm

  refine ⟨?_,?_,?_,?_⟩
  · exact same_standardBand_common_last_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hv3 hs13lt (by exact hvs1)
      (by simpa [R] using fullEqV3_13)
  · exact same_standardBand_common_last_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hv3 hs23lt (by exact hvs2)
      (by simpa [R] using fullEqV3_23)
  · exact same_standardBand_common_last_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hs13lt hs23lt hs12
      (by simpa [R] using fullEq13_23)
  · exact same_standardBand_common_last_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hv2 hs12lt hvs1
      (by simpa [R] using fullEqV2_12)

#print axioms threeWholeCube_source_globalMin_sameBand_angles


/-- Dual source-global-maximum geometry.  If s1<s2<s3<v, then all three
star edges leaving s1 have colour c1, while s2-s3 and s2-v both have colour
c2.  Hence all three star angles at s1 are below lambda and
angle(s3,s2,v)<lambda. -/
theorem threeWholeCube_source_globalMax_sameBand_angles
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁) (hvs2 : v ≠ s₂) (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂) (hc13 : c₁ ≠ c₃) (hc23 : c₂ ≠ c₃)
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hc1V :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      c₁ ∈ retainedActive R v)
    (hc2V :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      c₂ ∈ retainedActive R v)
    (hc3V :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      c₃ ∈ retainedActive R v)
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
      WholeCubeQTPair R s₃ v c₃)
    (hmax : ∀ w : ProjectionOrdered V, w ≠ v → w < v)
    (hs12lt : s₁ < s₂)
    (hs23lt : s₂ < s₃) :
    EuclideanGeometry.angle
        (reindexedPoint p v) (reindexedPoint p s₁) (reindexedPoint p s₂) < lam ∧
    EuclideanGeometry.angle
        (reindexedPoint p v) (reindexedPoint p s₁) (reindexedPoint p s₃) < lam ∧
    EuclideanGeometry.angle
        (reindexedPoint p s₂) (reindexedPoint p s₁) (reindexedPoint p s₃) < lam ∧
    EuclideanGeometry.angle
        (reindexedPoint p s₃) (reindexedPoint p s₂) (reindexedPoint p v) < lam := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let R := planarStandardResidualColoring hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hprof :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt (by simpa [exponent] using hprof.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R, exponent] using hprof.2 q

  have htrue : AllRetainedBitsTrue R v :=
    projectedLoss_global_max_allTrue
      R exponent (by simpa [R, exponent] using hvLoss) hmax
  have hb1 : retainedBit R v c₁ = true := htrue c₁ (by simpa [R] using hc1V)
  have hb2 : retainedBit R v c₂ = true := htrue c₂ (by simpa [R] using hc2V)
  have hb3 : retainedBit R v c₃ = true := htrue c₃ (by simpa [R] using hc3V)

  have h1v : s₁ < v := hmax s₁ hvs1.symm
  have h2v : s₂ < v := hmax s₂ hvs2.symm
  have h3v : s₃ < v := hmax s₃ hvs3.symm
  have hs13lt : s₁ < s₃ := hs12lt.trans hs23lt

  obtain ⟨w1, hw1⟩ := retainedCompletionWords_nonempty R s₁
  obtain ⟨w2, hw2⟩ := retainedCompletionWords_nonempty R s₂

  have hsource1 :=
    wholeCube_source_partner_edge_owner_colour_of_completion
      R exponent hexp hone hvs1.symm
      (by simpa [R, exponent] using hvLoss)
      (by simpa [R] using hc1V) hw1 (by simpa [R] using h₁)
  have hsource2 :=
    wholeCube_source_partner_edge_owner_colour_of_completion
      R exponent hexp hone hvs2.symm
      (by simpa [R, exponent] using hvLoss)
      (by simpa [R] using hc2V) hw2 (by simpa [R] using h₂)

  obtain ⟨hret1V,hcol1V⟩ : ∃ hret : (R.color s₁ v).val < n,
      retainedColor R s₁ v hret = c₁ := by
    rcases hsource1 with hgood | hbad
    · exact hgood.2
    · obtain ⟨hvs,_,_⟩ := hbad
      exact False.elim (lt_asymm hvs h1v)
  obtain ⟨hret2V,hcol2V⟩ : ∃ hret : (R.color s₂ v).val < n,
      retainedColor R s₂ v hret = c₂ := by
    rcases hsource2 with hgood | hbad
    · exact hgood.2
    · obtain ⟨hvs,_,_⟩ := hbad
      exact False.elim (lt_asymm hvs h2v)

  have lossS1 : s₁ ∈ projectedLossVertices R exponent := by
    have hact := h₁.1
    rw [hact]
    simpa [R, exponent] using hvLoss
  have lossS2 : s₂ ∈ projectedLossVertices R exponent := by
    have hact := h₂.1
    rw [hact]
    simpa [R, exponent] using hvLoss

  have hret12 : (R.color s₁ s₂).val < n :=
    projectedLoss_edge_right_retained R exponent hexp hone lossS1 hs12lt
  have hret13 : (R.color s₁ s₃).val < n :=
    projectedLoss_edge_right_retained R exponent hexp hone lossS1 hs13lt
  have hret23 : (R.color s₂ s₃).val < n :=
    projectedLoss_edge_right_retained R exponent hexp hone lossS2 hs23lt

  have hcol12 :=
    wholeCube_partner_edge_eq_lower_owner_of_true_true
      R hc12
      (by simpa [R] using hc1V) (by simpa [R] using hc2V)
      (by simpa [R] using h₁) (by simpa [R] using h₂)
      hs12lt hret12 hb1 hb2
  have hcol13 :=
    wholeCube_partner_edge_eq_lower_owner_of_true_true
      R hc13
      (by simpa [R] using hc1V) (by simpa [R] using hc3V)
      (by simpa [R] using h₁) (by simpa [R] using h₃)
      hs13lt hret13 hb1 hb3
  have hcol23 :=
    wholeCube_partner_edge_eq_lower_owner_of_true_true
      R hc23
      (by simpa [R] using hc2V) (by simpa [R] using hc3V)
      (by simpa [R] using h₂) (by simpa [R] using h₃)
      hs23lt hret23 hb2 hb3

  have fullEq1V_12 : R.color s₁ v = R.color s₁ s₂ := by
    apply Fin.ext
    have h1 := congrArg Fin.val hcol1V
    have h2 := congrArg Fin.val hcol12
    simpa [retainedColor] using h1.trans h2.symm
  have fullEq1V_13 : R.color s₁ v = R.color s₁ s₃ := by
    apply Fin.ext
    have h1 := congrArg Fin.val hcol1V
    have h2 := congrArg Fin.val hcol13
    simpa [retainedColor] using h1.trans h2.symm
  have fullEq12_13 : R.color s₁ s₂ = R.color s₁ s₃ :=
    fullEq1V_12.symm.trans fullEq1V_13
  have fullEq2V_23 : R.color s₂ v = R.color s₂ s₃ := by
    apply Fin.ext
    have h1 := congrArg Fin.val hcol2V
    have h2 := congrArg Fin.val hcol23
    simpa [retainedColor] using h1.trans h2.symm

  refine ⟨?_,?_,?_,?_⟩
  · exact same_standardBand_common_first_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hs12lt h1v hvs2
      (by simpa [R] using fullEq1V_12.symm)
  · exact same_standardBand_common_first_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hs13lt h1v hvs3
      (by simpa [R] using fullEq1V_13.symm)
  · exact same_standardBand_common_first_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hs12lt hs13lt hs23
      (by simpa [R] using fullEq12_13)
  · exact same_standardBand_common_first_angle_lt_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      hs23lt h2v hvs3
      (by simpa [R] using fullEq2V_23.symm)

#print axioms threeWholeCube_source_globalMax_sameBand_angles

end ProjectionOrdered
end JSP000404Research
