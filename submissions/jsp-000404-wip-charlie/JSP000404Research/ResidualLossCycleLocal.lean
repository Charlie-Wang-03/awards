import JSP000404Research.ResidualLossAllActivePairOverlap
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Two-sided colour separation at a projected-loss cycle vertex

If u < v < w and v is projected-loss, both incident edges uv and vw are
retained. Their retained colours are distinct by the defining no-monochromatic
increasing-two-path condition of OrderedEdgeColoring.

Hence the two corresponding translated slices at v are disjoint. This is the
local cycle geometry needed to prevent two-sided collision mass from using one
translated channel at a non-extremal loss vertex.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_two_sided_retained_colours_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u < v)
    (hvw : v < w) :
    retainedColor C u v
        (projectedLoss_edge_left_retained
          C exponent hexp honeLoss hvLoss huv)
      ≠
    retainedColor C v w
        (projectedLoss_edge_right_retained
          C exponent hexp honeLoss hvLoss hvw) := by
  let hleft :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hvLoss huv
  let hright :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hvLoss hvw
  intro hEq
  apply C.noMonoTwoPath huv hvw
  apply Fin.ext
  have hval := congrArg Fin.val hEq
  simpa [retainedColor,hleft,hright] using hval

theorem projectedLoss_two_sided_edge_slices_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u < v)
    (hvw : v < w) :
    let hleft :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hvLoss huv
    let hright :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hvLoss hvw
    Disjoint
      (translatedCompletionWords C v
        (retainedColor C u v hleft))
      (translatedCompletionWords C v
        (retainedColor C v w hright)) := by
  dsimp
  let hleft :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hvLoss huv
  let hright :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hvLoss hvw
  have hcLeft :
      retainedColor C u v hleft ∈ retainedActive C v :=
    retainedColor_mem_retainedActive_right C huv hleft
  have hcRight :
      retainedColor C v w hright ∈ retainedActive C v :=
    retainedColor_mem_retainedActive_left C hvw hright
  exact
    translatedCompletionWords_disjoint_same_owner_distinct_active
      C hcLeft
      (projectedLoss_two_sided_retained_colours_ne
        C exponent hexp honeLoss hvLoss huv hvw)

#print axioms projectedLoss_two_sided_retained_colours_ne
#print axioms projectedLoss_two_sided_edge_slices_disjoint

end OrderedEdgeColoring
end JSP000404Research
