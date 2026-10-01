import JSP000404Research.ResidualEnlargedCandidateHall
import JSP000404Research.ResidualEnlargedLossDegree
import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import JSP000404Research.ResidualEnlargedTriangleOutlet
import JSP000404Research.ResidualTripleFibreOutlet
import JSP000404Research.ResidualLossThreeExitRecursiveOutlet
import JSP000404Research.ResidualExactSharedRecursiveOutlet
import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.GenericTopExponentMultiplicity
import JSP000404Research.PlanarResidualHardRemainder
import JSP000404Research.ProjectionStandardBandBudget
import Mathlib.Tactic

/-!
# Planar lower branch via enlarged all-active loss candidate blocks

Instantiate the enlarged residual candidate family in the genuine planar
standard residual colouring.

For a planar lower-branch centre i:

* if i is not projected-loss, use the retained completion cube Q_i;
* if i is projected-loss, use Q_i together with every active one-coordinate
  translate.

The planar exponent satisfies exponent(i)<n and the one-layer active-colour
bound, so every enlarged block contains at least 2^exponent(i) Boolean words.

Weighted subset expansion of this explicit family therefore implies the sharp
all-N lower-branch dyadic capacity.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

noncomputable def planarEnlargedCandidateBlock
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V) :
    Finset (Fin n → Bool) := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  exact enlargedProjectedCandidateBlock R exponent i

theorem planarEnlargedCandidateBlock_local_capacity
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V) :
    2 ^ centreExponent (C i) t ≤
      (planarEnlargedCandidateBlock
        hp hcap hn hdelta0 hdeltaHalf ht hlam C i).card := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ j : ProjectionOrdered V, exponent j < n := by
    intro j
    simpa [exponent, planarCentreExponent] using
      (centreExponent_lt_n
        (C j) n delta t hn hdelta0 hdelta1 ht)
  have hexp :
      ∀ j : ProjectionOrdered V, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt (hexpLt j)
  have hone :
      ∀ j, (active R j).card ≤ n - exponent j + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      R exponent hexpLt hexp hone i
  simpa [planarEnlargedCandidateBlock,R,exponent,
    planarCentreExponent] using hlocal

theorem planar_lowerBranch_capacity_of_enlargedBlock_expansion
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hExpansion :
      ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t) ≤
          (S.biUnion
            (planarEnlargedCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  exact dyadic_capacity_of_vertex_block_expansion
    (fun i : ProjectionOrdered V =>
      centreExponent (C i) t)
    (planarEnlargedCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C)
    hExpansion

theorem planar_enlarged_expansion_failure_minimal_core
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hfail :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t) ≤
          (S.biUnion
            (planarEnlargedCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C)).card) :
    ∃ T : Finset (ProjectionOrdered V),
      T.Nonempty ∧
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C)
        T ∧
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap hn hdelta0 hdeltaHalf ht hlam C)
          U := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hfail' :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ exponent i) ≤
          (S.biUnion
            (enlargedProjectedCandidateBlock R exponent)).card := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hfail
  obtain ⟨T,hT,hdef,hmin⟩ :=
    exists_minimal_enlargedCandidate_deficient_core
      R exponent hfail'
  refine ⟨T,hT,?_,?_⟩
  · simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hdef
  · intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hmin U hUT


theorem planar_minimal_enlarged_maxLoss_degree_one_is_sharp
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U)
    {i : ProjectionOrdered V}
    (hiT : i ∈ T)
    (hiLoss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (hmaxLoss :
      ∀ z : ProjectionOrdered V,
        z ∈ T →
        z ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam)
          (planarCentreExponent hp C) →
        (retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam) z).card
          ≤
        (retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam) i).card)
    (hdegree :
      (enlargedCollisionNeighbours
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C) T i).card = 1) :
    SharpAt (reindexedPoint p) delta lam i := by
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n := by
    intro x
    simpa [exponent, planarCentreExponent] using
      (centreExponent_lt_n
        (C x) n delta t (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht)
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht hlam C
  have hiExp :
      exponent i = n - 1 := by
    apply minimal_enlargedCandidate_maxLoss_degree_one_exponent_eq_n_sub_one
      R exponent hexpLt hexp hone
      (T := T)
    · simpa [planarEnlargedCandidateBlock,R,exponent,
        planarCentreExponent] using hdef
    · intro U hUT
      simpa [planarEnlargedCandidateBlock,R,exponent,
        planarCentreExponent] using hmin U hUT
    · exact hiT
    · simpa [R,exponent] using hiLoss
    · intro z hzT hzLoss
      simpa [R,exponent] using
        hmaxLoss z hzT (by simpa [R,exponent] using hzLoss)
    · simpa [R,exponent] using hdegree
  have hcapRe :
      AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  exact concrete_unit_deficit_is_sharp
    (reindexedPoint_injective hp)
    hcapRe hn hdelta0 hdelta1 ht hlam
    i (C i)
    (by simpa [exponent, planarCentreExponent] using hiExp)


theorem planar_minimal_enlarged_no_two_maxLoss_degree_one
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U)
    {a b : ProjectionOrdered V}
    (haT : a ∈ T)
    (hbT : b ∈ T)
    (haLoss :
      a ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C))
    (haMax :
      ∀ z : ProjectionOrdered V,
        z ∈ T →
        z ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam)
          (planarCentreExponent hp C) →
        (retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam) z).card
          ≤
        (retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam) a).card)
    (hbMax :
      ∀ z : ProjectionOrdered V,
        z ∈ T →
        z ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam)
          (planarCentreExponent hp C) →
        (retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam) z).card
          ≤
        (retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith) ht hlam) b).card)
    (haDegree :
      (enlargedCollisionNeighbours
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C) T a).card = 1)
    (hbDegree :
      (enlargedCollisionNeighbours
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith) ht hlam)
        (planarCentreExponent hp C) T b).card = 1) :
    a = b := by
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith) ht hlam
  let exponent := planarCentreExponent hp C
  have hdelta1 : delta < 1 := by linarith
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n := by
    intro x
    simpa [exponent, planarCentreExponent] using
      (centreExponent_lt_n
        (C x) n delta t (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht)
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht hlam C
  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hdef
  have hminR :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock R exponent)
          U := by
    intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent] using hmin U hUT
  have haExp :
      exponent a = n - 1 :=
    minimal_enlargedCandidate_maxLoss_degree_one_exponent_eq_n_sub_one
      R exponent hexpLt hexp hone
      hdefR hminR haT
      (by simpa [R,exponent] using haLoss)
      (by
        intro z hzT hzLoss
        simpa [R,exponent] using
          haMax z hzT (by simpa [R,exponent] using hzLoss))
      (by simpa [R,exponent] using haDegree)
  have hbExp :
      exponent b = n - 1 :=
    minimal_enlargedCandidate_maxLoss_degree_one_exponent_eq_n_sub_one
      R exponent hexpLt hexp hone
      hdefR hminR hbT
      (by simpa [R,exponent] using hbLoss)
      (by
        intro z hzT hzLoss
        simpa [R,exponent] using
          hbMax z hzT (by simpa [R,exponent] using hzLoss))
      (by simpa [R,exponent] using hbDegree)
  have htop :=
    projectionOrdered_topExponent_filter_card_le_one
      hp hcap hcard hn hdelta0 hdeltaHalf ht hlam C
  apply Finset.card_le_one.mp htop
  · simp [exponent, planarCentreExponent, haExp]
  · simp [exponent, planarCentreExponent, hbExp]


theorem planar_minimal_enlarged_leaf_or_triangle_or_exact_or_topLoss
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ u v wu wv : ProjectionOrdered V,
        u ∈ T ∧
        v ∈ T ∧
        u ≠ v ∧
        wu ∈ T ∧
        wv ∈ T ∧
        wu ≠ u ∧
        wv ≠ v ∧
        EnlargedLeafOutlet R exponent T u wu ∧
        EnlargedLeafOutlet R exponent T v wv
    )
    ∨
    (
      ∃ u v w :
          {x : ProjectionOrdered V // x ∈ T},
        (enlargedCollisionGraph R exponent T).Adj u v ∧
        (enlargedCollisionGraph R exponent T).Adj u w ∧
        (enlargedCollisionGraph R exponent T).Adj v w
    )
    ∨
    (
      ∃ v ∈ T,
        ExactProjectedBudget R exponent v
    )
    ∨
    (
      ∃ top ∈ T,
        top ∈ projectedLossVertices R exponent ∧
        exponent top = n - 1 ∧
        2 *
          blockDeficiencyAmount
            (fun x => 2 ^ exponent x)
            (enlargedProjectedCandidateBlock R exponent)
            T
          ≤
        (retainedCompletionWords R top).card
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤
        n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C

  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef
  have hminR :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock R exponent)
          U := by
    intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hmin U hUT

  rcases
    minimal_enlargedCollisionGraph_leaf_outlets_or_triangle_or_long_cycle
      R exponent hexpLt hexp hone hdefR hminR
    with hleaf | htri | hlong
  · exact Or.inl hleaf
  · exact Or.inr (Or.inl htri)
  · rcases
      longCycle_exact_or_singleTopLoss_lowDefect
        R exponent hexpLt hexp hone
        hdefR hminR hlong
      with hexact | htop
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr htop))

theorem planar_enlarged_expansion_failure_root_reduction
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hfail :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t) ≤
          (S.biUnion
            (planarEnlargedCandidateBlock
              hp hcap (by omega : 1 ≤ n)
              hdelta0 hdeltaHalf ht hlam C)).card) :
    ∃ T : Finset (ProjectionOrdered V),
      T.Nonempty ∧
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      (
        (
          ∃ u v wu wv : ProjectionOrdered V,
            u ∈ T ∧
            v ∈ T ∧
            u ≠ v ∧
            wu ∈ T ∧
            wv ∈ T ∧
            wu ≠ u ∧
            wv ≠ v ∧
            EnlargedLeafOutlet R exponent T u wu ∧
            EnlargedLeafOutlet R exponent T v wv
        )
        ∨
        (
          ∃ u v w :
              {x : ProjectionOrdered V // x ∈ T},
            EnlargedTriangleOutlet R exponent T u v w
        )
        ∨
        (
          ∃ v ∈ T,
            ExactProjectedBudget R exponent v
        )
        ∨
        (
          ∃ top ∈ T,
            top ∈ projectedLossVertices R exponent ∧
            exponent top = n - 1 ∧
            2 *
              blockDeficiencyAmount
                (fun x => 2 ^ exponent x)
                (enlargedProjectedCandidateBlock R exponent)
                T
              ≤
            (retainedCompletionWords R top).card
        )
      ) := by
  obtain ⟨T,hT,hdef,hmin⟩ :=
    planar_enlarged_expansion_failure_minimal_core
      hp hcap (by omega : 1 ≤ n) hdelta0
      hdeltaHalf ht hlam C hfail
  refine ⟨T,hT,?_⟩
  exact planar_minimal_enlarged_leaf_or_triangle_or_exact_or_topLoss
    hp hcap hn hdelta0 hdeltaHalf ht hlam C
    hdef hmin


theorem planar_secondLayerLoss_word_closed_outlet
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (s : ProjectionOrdered V)
    (hS : centreExponent (C s) t = n - 1)
    {v : ProjectionOrdered V}
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hvSecond : centreExponent (C v) t = n - 2)
    {word : Fin n → Bool}
    (hword :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) v) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ e : Fin n,
        e ∈ retainedActive R v ∧
        flipBoolWordAt word e ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        ExactProjectedBudget R exponent w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices R exponent ∧
        exponent w + 1 ≤ n - 2
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤
        n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C

  have htop :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => exponent z = n - 1)).card ≤ 1 := by
    simpa [exponent,planarCentreExponent] using
      (projectionOrdered_topExponent_filter_card_le_one
        hp hcap hcard (by omega : 2 ≤ n)
        hdelta0 hdeltaHalf ht hlam C)

  have hcapRe :
      AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  have hsecondComp :=
    secondLayer_companion_card_le_two
      (reindexedPoint_injective hp)
      hcapRe hn3 hdelta0 hdeltaHalf ht hlam
      C s hS

  have hsecondEq :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => exponent z = n - 2))
        =
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => z ≠ s ∧
          centreExponent (C z) t = n - 2)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      have hz' :
          centreExponent (C z) t = n - 2 := by
        simpa [exponent,planarCentreExponent] using hz
      refine ⟨?_,hz'⟩
      intro hzs
      subst z
      omega
    · rintro ⟨_hzs,hz⟩
      simpa [exponent,planarCentreExponent] using hz

  have hsecond :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => exponent z = n - 2)).card ≤ 2 := by
    rw [hsecondEq]
    exact hsecondComp

  have hvSecondR :
      exponent v = n - 2 := by
    simpa [exponent,planarCentreExponent] using hvSecond

  simpa [R,exponent,hn1,hdelta1] using
    (secondLayerLoss_word_closed_outlet_of_multiplicity
      R exponent hexpLt hexp hone
      htop hsecond
      (by simpa [R,exponent,hn1,hdelta1] using hvLoss)
      hvSecondR
      (by simpa [R,hn1,hdelta1] using hword))


theorem planar_topLoss_word_closed_outlet
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {v : ProjectionOrdered V}
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hvTop : centreExponent (C v) t = n - 1)
    {word : Fin n → Bool}
    (hword :
      word ∈ retainedCompletionWords
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam) v) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        ExactProjectedBudget R exponent w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices R exponent ∧
        exponent w + 3 ≤ n
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤
        n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hvTopR :
      exponent v = n - 1 := by
    simpa [exponent,planarCentreExponent] using hvTop
  have hvLossR :
      v ∈ projectedLossVertices R exponent := by
    simpa [R,exponent,hn1,hdelta1] using hvLoss

  rcases
    topLoss_word_five_exit_outlet_with_lower_witness
      R exponent hexpLt hexp hone
      hvLossR hvTopR
      (by simpa [R,hn1,hdelta1] using hword)
    with hhole | hpaid | hexact | hlower | htwoTop
  · obtain ⟨e,_heActive,heHole⟩ := hhole
    exact Or.inl ⟨flipBoolWordAt word e,heHole⟩
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · obtain ⟨w,hwLoss,hwLower,e,heActive,hwWord⟩ := hlower
    rcases lowerLoss_secondLayer_or_deep
        R exponent hwLoss (hexpLt w) hwLower
      with hwSecond | hwDeep
    · have hwSecondGeom :
          centreExponent (C w) t = n - 2 := by
        simpa [exponent,planarCentreExponent] using hwSecond
      rcases
        planar_secondLayerLoss_word_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C v hvTop
          (v := w)
          (by simpa [R,exponent,hn1,hdelta1] using hwLoss)
          hwSecondGeom
          (word := flipBoolWordAt word e)
          (by simpa [R,hn1,hdelta1] using hwWord)
        with hhole2 | hpaid2 | hexact2 | hdeep2
      · obtain ⟨e2,_he2Active,he2Hole⟩ := hhole2
        exact Or.inl
          ⟨flipBoolWordAt (flipBoolWordAt word e) e2,
            he2Hole⟩
      · exact Or.inr (Or.inl hpaid2)
      · exact Or.inr (Or.inr (Or.inl hexact2))
      · obtain ⟨z,hzLoss,hzDeep⟩ := hdeep2
        exact Or.inr (Or.inr (Or.inr
          ⟨z,hzLoss,by omega⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨w,hwLoss,hwDeep⟩))
  · obtain ⟨w,z,hwz,hwLoss,hzLoss,hwTop,hzTop⟩ := htwoTop
    have htop :=
      projectionOrdered_topExponent_filter_card_le_one
        hp hcap hcard (by omega : 2 ≤ n)
        hdelta0 hdeltaHalf ht hlam C
    have hwMem :
        w ∈ (Finset.univ : Finset (ProjectionOrdered V)).filter
          (fun x => centreExponent (C x) t = n - 1) := by
      simp [exponent,planarCentreExponent] at hwTop
      simp [hwTop]
    have hzMem :
        z ∈ (Finset.univ : Finset (ProjectionOrdered V)).filter
          (fun x => centreExponent (C x) t = n - 1) := by
      simp [exponent,planarCentreExponent] at hzTop
      simp [hzTop]
    have hwEqz := Finset.card_le_one.mp htop hwMem hzMem
    exact False.elim (hwz hwEqz)

#print axioms planar_secondLayerLoss_word_closed_outlet
#print axioms planar_topLoss_word_closed_outlet


/-- A planar top projected-loss vertex is already closed without specifying a
completion word: its retained completion cube is nonempty, so choose any word
and apply the word-level top-loss outlet. -/
theorem planar_topLoss_closed_outlet
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {v : ProjectionOrdered V}
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hvTop : centreExponent (C v) t = n - 1) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        ExactProjectedBudget R exponent w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices R exponent ∧
        exponent w + 3 ≤ n
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hnonempty :
      (retainedCompletionWords R v).Nonempty := by
    apply Finset.card_pos.mp
    rw [retainedCompletionWords_card]
    positivity
  obtain ⟨word,hword⟩ := hnonempty
  simpa [R,exponent,hn1,hdelta1,planarCentreExponent] using
    (planar_topLoss_word_closed_outlet
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C hvLoss hvTop hword)

#print axioms planar_topLoss_closed_outlet


/-- Girth-free planar deficient-core root.  The previous
leaf/triangle/long-cycle graph split is replaced by fibre multiplicity.
All bounded-multiplicity overloads are recursively discharged; a top shared
completion word is fed through the planar top-loss closed outlet.  The only
remaining structural branch is a high-layer two-loss pair. -/
theorem planar_deficientCore_girthFree_recursive_root
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) z
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        ExactProjectedBudget R exponent z
    )
    ∨
    (
      ∃ source : ProjectionOrdered V,
        ExactRecursiveOutlet R exponent source
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        z ∈ projectedLossVertices R exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ a b : {x : ProjectionOrdered V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices R exponent ∧
        b.1 ∈ projectedLossVertices R exponent ∧
        (
          (exponent a.1 = n - 1 ∧ exponent b.1 = n - 2)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 1)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 2)
        )
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have htop :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => exponent z = n - 1)).card ≤ 1 := by
    simpa [exponent,planarCentreExponent] using
      (projectionOrdered_topExponent_filter_card_le_one
        hp hcap hcard (by omega : 2 ≤ n)
        hdelta0 hdeltaHalf ht hlam C)
  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef

  rcases
    deficientCore_deep_or_highLossPair_or_paid_or_exactRecursive_or_topShared
      R exponent hexpLt hexp hone htop hdefR
    with hdeep | hpair | hpaid | hrec | htopShared
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpair))))
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
  · obtain ⟨top,htopT,htopLoss,htopExp,hshared⟩ := htopShared
    obtain ⟨word,hword⟩ := hshared
    have hparts := Finset.mem_inter.mp hword
    have htopLossGeom :
        top ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith : delta < 1) ht hlam)
          (planarCentreExponent hp C) := by
      simpa [R,exponent,hn1,hdelta1] using htopLoss
    have htopExpGeom :
        centreExponent (C top) t = n - 1 := by
      simpa [exponent,planarCentreExponent] using htopExp
    have hwordGeom :
        word ∈ retainedCompletionWords
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith : delta < 1) ht hlam) top := by
      simpa [R,hn1,hdelta1] using hparts.2
    rcases
      planar_topLoss_word_closed_outlet
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        hcard C htopLossGeom htopExpGeom hwordGeom
      with hhole | hpaid2 | hexact2 | hdeep2
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid2)
    · exact Or.inr (Or.inr (Or.inl hexact2))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))

#print axioms planar_deficientCore_girthFree_recursive_root


/-- Stronger planar root: top--second and second--top loss pairs are not
structural remainders, because the top loss itself is already closed by
planar_topLoss_closed_outlet.  Hence the only remaining high-layer pair is
second--second. -/
theorem planar_deficientCore_girthFree_secondPair_root
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) z
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        ExactProjectedBudget R exponent z
    )
    ∨
    (
      ∃ source : ProjectionOrdered V,
        ExactRecursiveOutlet R exponent source
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        z ∈ projectedLossVertices R exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ a b : {x : ProjectionOrdered V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices R exponent ∧
        b.1 ∈ projectedLossVertices R exponent ∧
        exponent a.1 = n - 2 ∧
        exponent b.1 = n - 2
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  rcases
    planar_deficientCore_girthFree_recursive_root
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C hdef
    with hhole | hpaid | hexact | hrec | hdeep | hpair
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
  · obtain ⟨a,b,hab,haLoss,hbLoss,hlevels⟩ := hpair
    rcases hlevels with haTopSecond | haSecondTop | hbothSecond
    · have haLossGeom :
          a.1 ∈ projectedLossVertices
            (planarStandardResidualColoring
              hp hcap (by omega : 1 ≤ n)
              hdelta0 (by linarith : delta < 1) ht hlam)
            (planarCentreExponent hp C) := by
        simpa [R,exponent,hn1,hdelta1] using haLoss
      have haTopGeom :
          centreExponent (C a.1) t = n - 1 := by
        simpa [exponent,planarCentreExponent] using haTopSecond.1
      rcases
        planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C haLossGeom haTopGeom
        with hhole2 | hpaid2 | hexact2 | hdeep2
      · exact Or.inl hhole2
      · exact Or.inr (Or.inl hpaid2)
      · exact Or.inr (Or.inr (Or.inl hexact2))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
    · have hbLossGeom :
          b.1 ∈ projectedLossVertices
            (planarStandardResidualColoring
              hp hcap (by omega : 1 ≤ n)
              hdelta0 (by linarith : delta < 1) ht hlam)
            (planarCentreExponent hp C) := by
        simpa [R,exponent,hn1,hdelta1] using hbLoss
      have hbTopGeom :
          centreExponent (C b.1) t = n - 1 := by
        simpa [exponent,planarCentreExponent] using haSecondTop.2
      rcases
        planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C hbLossGeom hbTopGeom
        with hhole2 | hpaid2 | hexact2 | hdeep2
      · exact Or.inl hhole2
      · exact Or.inr (Or.inl hpaid2)
      · exact Or.inr (Or.inr (Or.inl hexact2))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨a,b,hab,haLoss,hbLoss,hbothSecond.1,hbothSecond.2⟩))))

#print axioms planar_deficientCore_girthFree_secondPair_root


/-- Witness-preserving planar root.  The sole structural remainder is a
triple-covered word carried by a collision triangle in which at least one
triangle edge joins two second-layer loss vertices. -/
theorem planar_deficientCore_girthFree_secondTriple_root
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) z
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        ExactProjectedBudget R exponent z
    )
    ∨
    (
      ∃ source : ProjectionOrdered V,
        ExactRecursiveOutlet R exponent source
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        z ∈ projectedLossVertices R exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ word : Fin n → Bool,
      ∃ u v w : {x : ProjectionOrdered V // x ∈ T},
        u ≠ v ∧
        u ≠ w ∧
        v ≠ w ∧
        word ∈ enlargedProjectedCandidateBlock R exponent u.1 ∧
        word ∈ enlargedProjectedCandidateBlock R exponent v.1 ∧
        word ∈ enlargedProjectedCandidateBlock R exponent w.1 ∧
        (enlargedCollisionGraph R exponent T).Adj u v ∧
        (enlargedCollisionGraph R exponent T).Adj u w ∧
        (enlargedCollisionGraph R exponent T).Adj v w ∧
        (
          (u.1 ∈ projectedLossVertices R exponent ∧
            v.1 ∈ projectedLossVertices R exponent ∧
            exponent u.1 = n - 2 ∧
            exponent v.1 = n - 2)
          ∨
          (u.1 ∈ projectedLossVertices R exponent ∧
            w.1 ∈ projectedLossVertices R exponent ∧
            exponent u.1 = n - 2 ∧
            exponent w.1 = n - 2)
          ∨
          (v.1 ∈ projectedLossVertices R exponent ∧
            w.1 ∈ projectedLossVertices R exponent ∧
            exponent v.1 = n - 2 ∧
            exponent w.1 = n - 2)
        )
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef

  rcases
    deficientCore_tripleFibre_or_recursiveOverload
      R exponent hexpLt hexp hone hdefR
    with htriple | hexactOutlet | htopShared
  · obtain ⟨word,hthree⟩ := htriple
    obtain ⟨u,v,w,huv,huw,hvw,
      huWord,hvWord,hwWord,hUV,hUW,hVW⟩ :=
      tripleFibre_has_common_word_collision_triangle
        R exponent hthree
    rcases
      enlargedCollisionGraph_triangle_loss_shape
        R exponent T hUV hUW hVW
      with hU | hV | hW | hUVLoss | hUWLoss | hVWLoss
    · rcases
        enlargedTriangle_nonloss_edge_paid_or_exactRecursive
          R exponent hexp hone T
          hVW hU.hvNonloss hU.hwNonloss
        with hpaid | hrec
      · exact Or.inr (Or.inl hpaid)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
    · rcases
        enlargedTriangle_nonloss_edge_paid_or_exactRecursive
          R exponent hexp hone T
          hUW hV.huNonloss hV.hwNonloss
        with hpaid | hrec
      · exact Or.inr (Or.inl hpaid)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
    · rcases
        enlargedTriangle_nonloss_edge_paid_or_exactRecursive
          R exponent hexp hone T
          hUV hW.huNonloss hW.hvNonloss
        with hpaid | hrec
      · exact Or.inr (Or.inl hpaid)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
    · rcases
        two_projectedLoss_highLayer_classification
          R exponent hexpLt
          (by
            simpa [exponent,planarCentreExponent] using
              (projectionOrdered_topExponent_filter_card_le_one
                hp hcap hcard (by omega : 2 ≤ n)
                hdelta0 hdeltaHalf ht hlam C))
          (by
            intro h
            apply huv
            apply Subtype.ext
            exact h)
          hUVLoss.huLoss hUVLoss.hvLoss
      with huDeep | hvDeep | huTopSecond | huSecondTop | hBothSecond
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨u.1,hUVLoss.huLoss,huDeep⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨v.1,hUVLoss.hvLoss,hvDeep⟩))))
      · have huLossGeom :
            u.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hUVLoss.huLoss
        have huTopGeom :
            centreExponent (C u.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using huTopSecond.1
        rcases planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C huLossGeom huTopGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
      · have hvLossGeom :
            v.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hUVLoss.hvLoss
        have hvTopGeom :
            centreExponent (C v.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using huSecondTop.2
        rcases planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C hvLossGeom hvTopGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨word,u,v,w,huv,huw,hvw,
            huWord,hvWord,hwWord,hUV,hUW,hVW,
            Or.inl ⟨hUVLoss.huLoss,hUVLoss.hvLoss,
              hBothSecond.1,hBothSecond.2⟩⟩))))
    · rcases
        two_projectedLoss_highLayer_classification
          R exponent hexpLt
          (by
            simpa [exponent,planarCentreExponent] using
              (projectionOrdered_topExponent_filter_card_le_one
                hp hcap hcard (by omega : 2 ≤ n)
                hdelta0 hdeltaHalf ht hlam C))
          (by
            intro h
            apply huw
            apply Subtype.ext
            exact h)
          hUWLoss.huLoss hUWLoss.hwLoss
      with huDeep | hwDeep | huTopSecond | huSecondTop | hBothSecond
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨u.1,hUWLoss.huLoss,huDeep⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨w.1,hUWLoss.hwLoss,hwDeep⟩))))
      · have huLossGeom :
            u.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hUWLoss.huLoss
        have huTopGeom :
            centreExponent (C u.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using huTopSecond.1
        rcases planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C huLossGeom huTopGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
      · have hwLossGeom :
            w.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hUWLoss.hwLoss
        have hwTopGeom :
            centreExponent (C w.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using huSecondTop.2
        rcases planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C hwLossGeom hwTopGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨word,u,v,w,huv,huw,hvw,
            huWord,hvWord,hwWord,hUV,hUW,hVW,
            Or.inr (Or.inl
              ⟨hUWLoss.huLoss,hUWLoss.hwLoss,
                hBothSecond.1,hBothSecond.2⟩)⟩))))
    · rcases
        two_projectedLoss_highLayer_classification
          R exponent hexpLt
          (by
            simpa [exponent,planarCentreExponent] using
              (projectionOrdered_topExponent_filter_card_le_one
                hp hcap hcard (by omega : 2 ≤ n)
                hdelta0 hdeltaHalf ht hlam C))
          (by
            intro h
            apply hvw
            apply Subtype.ext
            exact h)
          hVWLoss.hvLoss hVWLoss.hwLoss
      with hvDeep | hwDeep | hvTopSecond | hvSecondTop | hBothSecond
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨v.1,hVWLoss.hvLoss,hvDeep⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨w.1,hVWLoss.hwLoss,hwDeep⟩))))
      · have hvLossGeom :
            v.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hVWLoss.hvLoss
        have hvTopGeom :
            centreExponent (C v.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using hvTopSecond.1
        rcases planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C hvLossGeom hvTopGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
      · have hwLossGeom :
            w.1 ∈ projectedLossVertices
              (planarStandardResidualColoring
                hp hcap (by omega : 1 ≤ n)
                hdelta0 (by linarith : delta < 1) ht hlam)
              (planarCentreExponent hp C) := by
          simpa [R,exponent,hn1,hdelta1] using hVWLoss.hwLoss
        have hwTopGeom :
            centreExponent (C w.1) t = n - 1 := by
          simpa [exponent,planarCentreExponent] using hvSecondTop.2
        rcases planar_topLoss_closed_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          hcard C hwLossGeom hwTopGeom
          with hhole | hpaid | hexact | hdeep
        · exact Or.inl hhole
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inr (Or.inr (Or.inl hexact))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨word,u,v,w,huv,huw,hvw,
            huWord,hvWord,hwWord,hUV,hUW,hVW,
            Or.inr (Or.inr
              ⟨hVWLoss.hvLoss,hVWLoss.hwLoss,
                hBothSecond.1,hBothSecond.2⟩)⟩))))
  · obtain ⟨v,hvT,hvExact,hout⟩ := hexactOutlet
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨v,exactSharedOutlet_to_recursive
        R exponent hvExact hout⟩)))
  · obtain ⟨top,htopT,htopLoss,htopExp,_hshared⟩ := htopShared
    have htopLossGeom :
        top ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith : delta < 1) ht hlam)
          (planarCentreExponent hp C) := by
      simpa [R,exponent,hn1,hdelta1] using htopLoss
    have htopExpGeom :
        centreExponent (C top) t = n - 1 := by
      simpa [exponent,planarCentreExponent] using htopExp
    rcases planar_topLoss_closed_outlet
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C htopLossGeom htopExpGeom
      with hhole | hpaid | hexact | hdeep
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))

#print axioms planar_deficientCore_girthFree_secondTriple_root


/-- Final multiplicity-first planar root at the current frontier.  If the
closed hole/surplus/exact/recursive/deep outlets all fail, the deficient core
contains one Boolean word carried by three distinct second-layer projected-loss
vertices. -/
theorem planar_deficientCore_girthFree_threeSecond_root
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) z
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        ExactProjectedBudget R exponent z
    )
    ∨
    (
      ∃ source : ProjectionOrdered V,
        ExactRecursiveOutlet R exponent source
    )
    ∨
    (
      ∃ z : ProjectionOrdered V,
        z ∈ projectedLossVertices R exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ word : Fin n → Bool,
      ∃ u v w : {x : ProjectionOrdered V // x ∈ T},
        u ≠ v ∧
        u ≠ w ∧
        v ≠ w ∧
        word ∈ enlargedProjectedCandidateBlock R exponent u.1 ∧
        word ∈ enlargedProjectedCandidateBlock R exponent v.1 ∧
        word ∈ enlargedProjectedCandidateBlock R exponent w.1 ∧
        (enlargedCollisionGraph R exponent T).Adj u v ∧
        (enlargedCollisionGraph R exponent T).Adj u w ∧
        (enlargedCollisionGraph R exponent T).Adj v w ∧
        u.1 ∈ projectedLossVertices R exponent ∧
        v.1 ∈ projectedLossVertices R exponent ∧
        w.1 ∈ projectedLossVertices R exponent ∧
        exponent u.1 = n - 2 ∧
        exponent v.1 = n - 2 ∧
        exponent w.1 = n - 2
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C

  rcases
    planar_deficientCore_girthFree_secondTriple_root
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C hdef
    with hhole | hpaid | hexact | hrec | hdeep | htriple
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
  · obtain ⟨word,u,v,w,huv,huw,hvw,
      huWord,hvWord,hwWord,hUV,hUW,hVW,hpair⟩ := htriple
    rcases hpair with hUVSecond | hUWSecond | hVWSecond
    · obtain ⟨huLoss,hvLoss,huSecond,hvSecond⟩ := hUVSecond
      rcases projectedProfile_strict_exact_or_loss
          R exponent hexp hone w.1
        with hwStrict | hwExact | hwLoss
      · exact Or.inr (Or.inl
          ⟨w.1,
            projected_strict_surplus_at_least_one
              exponent (projectedFree R) hwStrict⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨w.1,hwExact⟩))
      · rcases exponent_top_second_or_deep
          exponent (hexpLt w.1)
        with hwTop | hwSecond | hwDeep
        · have hwLossGeom :
              w.1 ∈ projectedLossVertices
                (planarStandardResidualColoring
                  hp hcap (by omega : 1 ≤ n)
                  hdelta0 (by linarith : delta < 1) ht hlam)
                (planarCentreExponent hp C) := by
            simpa [R,exponent,hn1,hdelta1] using hwLoss
          have hwTopGeom :
              centreExponent (C w.1) t = n - 1 := by
            simpa [exponent,planarCentreExponent] using hwTop
          rcases planar_topLoss_closed_outlet
            hp hcap hn3 hdelta0 hdeltaHalf ht hlam
            hcard C hwLossGeom hwTopGeom
            with hhole2 | hpaid2 | hexact2 | hdeep2
          · exact Or.inl hhole2
          · exact Or.inr (Or.inl hpaid2)
          · exact Or.inr (Or.inr (Or.inl hexact2))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨word,u,v,w,huv,huw,hvw,
              huWord,hvWord,hwWord,hUV,hUW,hVW,
              huLoss,hvLoss,hwLoss,
              huSecond,hvSecond,hwSecond⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨w.1,hwLoss,hwDeep⟩))))
    · obtain ⟨huLoss,hwLoss,huSecond,hwSecond⟩ := hUWSecond
      rcases projectedProfile_strict_exact_or_loss
          R exponent hexp hone v.1
        with hvStrict | hvExact | hvLoss
      · exact Or.inr (Or.inl
          ⟨v.1,
            projected_strict_surplus_at_least_one
              exponent (projectedFree R) hvStrict⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨v.1,hvExact⟩))
      · rcases exponent_top_second_or_deep
          exponent (hexpLt v.1)
        with hvTop | hvSecond | hvDeep
        · have hvLossGeom :
              v.1 ∈ projectedLossVertices
                (planarStandardResidualColoring
                  hp hcap (by omega : 1 ≤ n)
                  hdelta0 (by linarith : delta < 1) ht hlam)
                (planarCentreExponent hp C) := by
            simpa [R,exponent,hn1,hdelta1] using hvLoss
          have hvTopGeom :
              centreExponent (C v.1) t = n - 1 := by
            simpa [exponent,planarCentreExponent] using hvTop
          rcases planar_topLoss_closed_outlet
            hp hcap hn3 hdelta0 hdeltaHalf ht hlam
            hcard C hvLossGeom hvTopGeom
            with hhole2 | hpaid2 | hexact2 | hdeep2
          · exact Or.inl hhole2
          · exact Or.inr (Or.inl hpaid2)
          · exact Or.inr (Or.inr (Or.inl hexact2))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨word,u,v,w,huv,huw,hvw,
              huWord,hvWord,hwWord,hUV,hUW,hVW,
              huLoss,hvLoss,hwLoss,
              huSecond,hvSecond,hwSecond⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨v.1,hvLoss,hvDeep⟩))))
    · obtain ⟨hvLoss,hwLoss,hvSecond,hwSecond⟩ := hVWSecond
      rcases projectedProfile_strict_exact_or_loss
          R exponent hexp hone u.1
        with huStrict | huExact | huLoss
      · exact Or.inr (Or.inl
          ⟨u.1,
            projected_strict_surplus_at_least_one
              exponent (projectedFree R) huStrict⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨u.1,huExact⟩))
      · rcases exponent_top_second_or_deep
          exponent (hexpLt u.1)
        with huTop | huSecond | huDeep
        · have huLossGeom :
              u.1 ∈ projectedLossVertices
                (planarStandardResidualColoring
                  hp hcap (by omega : 1 ≤ n)
                  hdelta0 (by linarith : delta < 1) ht hlam)
                (planarCentreExponent hp C) := by
            simpa [R,exponent,hn1,hdelta1] using huLoss
          have huTopGeom :
              centreExponent (C u.1) t = n - 1 := by
            simpa [exponent,planarCentreExponent] using huTop
          rcases planar_topLoss_closed_outlet
            hp hcap hn3 hdelta0 hdeltaHalf ht hlam
            hcard C huLossGeom huTopGeom
            with hhole2 | hpaid2 | hexact2 | hdeep2
          · exact Or.inl hhole2
          · exact Or.inr (Or.inl hpaid2)
          · exact Or.inr (Or.inr (Or.inl hexact2))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨word,u,v,w,huv,huw,hvw,
              huWord,hvWord,hwWord,hUV,hUW,hVW,
              huLoss,hvLoss,hwLoss,
              huSecond,hvSecond,hwSecond⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨u.1,huLoss,huDeep⟩))))

#print axioms planar_deficientCore_girthFree_threeSecond_root


theorem planar_longCycle_overload_recursive_outlet
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent hp C
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T)
    (hgirth :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent hp C
      3 < (enlargedCollisionGraph R exponent T).girth) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ v ∈ T,
        ExactRecursiveOutlet R exponent v
    )
    ∨
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords R
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree R) w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        ExactProjectedBudget R exponent w
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices R exponent ∧
        exponent w + 3 ≤ n
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤
        n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [R,exponent,hn1,hdelta1] using hdef
  have hgirthR :
      3 < (enlargedCollisionGraph R exponent T).girth := by
    simpa [R,exponent,hn1,hdelta1] using hgirth

  rcases
    longCycle_overload_recursive_outlet
      R exponent hexpLt hexp hone
      hdefR hgirthR
    with hexactOutlet | htop
  · obtain ⟨v,hvT,hvExact,hout⟩ := hexactOutlet
    exact Or.inl
      ⟨v,hvT,
        exactSharedOutlet_to_recursive
          R exponent hvExact hout⟩
  · obtain ⟨v,hvT,hvLoss,hvTop,hsharedQ⟩ := htop
    obtain ⟨word,hwordSharedQ⟩ := hsharedQ
    have hword :
        word ∈ retainedCompletionWords R v :=
      (Finset.mem_inter.mp hwordSharedQ).2
    have hvTopGeom :
        centreExponent (C v) t = n - 1 := by
      simpa [exponent,planarCentreExponent] using hvTop
    rcases
      planar_topLoss_word_closed_outlet
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        hcard C
        (v := v)
        (by simpa [R,exponent,hn1,hdelta1] using hvLoss)
        hvTopGeom
        (word := word)
        (by simpa [R,hn1,hdelta1] using hword)
      with hhole | hpaid | hexact | hdeep
    · exact Or.inr (Or.inl hhole)
    · exact Or.inr (Or.inr (Or.inl hpaid))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hexact)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hdeep)))

#print axioms planar_longCycle_overload_recursive_outlet


theorem planar_minimal_enlarged_leaf_or_triangle_or_recursive
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      (
        ∃ u v wu wv : ProjectionOrdered V,
          u ∈ T ∧
          v ∈ T ∧
          u ≠ v ∧
          wu ∈ T ∧
          wv ∈ T ∧
          wu ≠ u ∧
          wv ≠ v ∧
          EnlargedLeafOutlet R exponent T u wu ∧
          EnlargedLeafOutlet R exponent T v wv
      )
      ∨
      (
        ∃ u v w :
            {x : ProjectionOrdered V // x ∈ T},
          EnlargedTriangleOutlet R exponent T u v w
      )
      ∨
      (
        ∃ v ∈ T,
          ExactRecursiveOutlet R exponent v
      )
      ∨
      (
        ∃ hole : Fin n → Bool,
          hole ∉ coveredCompletionWords R
      )
      ∨
      (
        ∃ w : ProjectionOrdered V,
          1 ≤ dyadicProfileSurplus
            exponent (projectedFree R) w
      )
      ∨
      (
        ∃ w : ProjectionOrdered V,
          ExactProjectedBudget R exponent w
      )
      ∨
      (
        ∃ w : ProjectionOrdered V,
          w ∈ projectedLossVertices R exponent ∧
          exponent w + 3 ≤ n
      )
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤
        n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef
  have hminR :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock R exponent)
          U := by
    intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hmin U hUT

  rcases
    minimal_enlargedCollisionGraph_leaf_outlets_or_triangle_or_long_cycle
      R exponent hexpLt hexp hone hdefR hminR
    with hleaf | htri | hlong
  · exact Or.inl hleaf
  · obtain ⟨u,v,w,huv,huw,hvw⟩ := htri
    exact Or.inr (Or.inl
      ⟨u,v,w,
        enlargedCollisionGraph_triangle_outlet
          R exponent hexp hone T huv huw hvw⟩)
  · rcases
      planar_longCycle_overload_recursive_outlet
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        hcard C
        (T := T)
        (by simpa [R,exponent,hn1,hdelta1] using hdefR)
        (by simpa [R,exponent,hn1,hdelta1] using hlong)
      with hexactRec | hhole | hpaid | hexact | hdeep
    · exact Or.inr (Or.inr (Or.inl hexactRec))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hhole)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpaid))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hdeep))))

theorem planar_enlarged_expansion_failure_recursive_root
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hfail :
      ¬ ∀ S : Finset (ProjectionOrdered V),
        (∑ i ∈ S, 2 ^ centreExponent (C i) t) ≤
          (S.biUnion
            (planarEnlargedCandidateBlock
              hp hcap (by omega : 1 ≤ n)
              hdelta0 hdeltaHalf ht hlam C)).card) :
    ∃ T : Finset (ProjectionOrdered V),
      T.Nonempty ∧
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent hp C
      (
        (
          ∃ u v wu wv : ProjectionOrdered V,
            u ∈ T ∧
            v ∈ T ∧
            u ≠ v ∧
            wu ∈ T ∧
            wv ∈ T ∧
            wu ≠ u ∧
            wv ≠ v ∧
            EnlargedLeafOutlet R exponent T u wu ∧
            EnlargedLeafOutlet R exponent T v wv
        )
        ∨
        (
          ∃ u v w :
              {x : ProjectionOrdered V // x ∈ T},
            EnlargedTriangleOutlet R exponent T u v w
        )
        ∨
        (
          ∃ v ∈ T,
            ExactRecursiveOutlet R exponent v
        )
        ∨
        (
          ∃ hole : Fin n → Bool,
            hole ∉ coveredCompletionWords R
        )
        ∨
        (
          ∃ w : ProjectionOrdered V,
            1 ≤ dyadicProfileSurplus
              exponent (projectedFree R) w
        )
        ∨
        (
          ∃ w : ProjectionOrdered V,
            ExactProjectedBudget R exponent w
        )
        ∨
        (
          ∃ w : ProjectionOrdered V,
            w ∈ projectedLossVertices R exponent ∧
            exponent w + 3 ≤ n
        )
      ) := by
  obtain ⟨T,hT,hdef,hmin⟩ :=
    planar_enlarged_expansion_failure_minimal_core
      hp hcap (by omega : 1 ≤ n) hdelta0
      hdeltaHalf ht hlam C hfail
  refine ⟨T,hT,?_⟩
  exact
    planar_minimal_enlarged_leaf_or_triangle_or_recursive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C hdef hmin

#print axioms planar_minimal_enlarged_leaf_or_triangle_or_recursive
#print axioms planar_enlarged_expansion_failure_recursive_root

#print axioms planarEnlargedCandidateBlock_local_capacity
#print axioms planar_lowerBranch_capacity_of_enlargedBlock_expansion
#print axioms planar_enlarged_expansion_failure_minimal_core
#print axioms planar_minimal_enlarged_maxLoss_degree_one_is_sharp
#print axioms planar_minimal_enlarged_no_two_maxLoss_degree_one
#print axioms planar_minimal_enlarged_leaf_or_triangle_or_exact_or_topLoss
#print axioms planar_enlarged_expansion_failure_root_reduction

end
end ProjectionOrdered
end JSP000404Research
