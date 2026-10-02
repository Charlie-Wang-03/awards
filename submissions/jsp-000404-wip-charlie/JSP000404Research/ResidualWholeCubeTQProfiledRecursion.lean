import JSP000404Research.ResidualWholeCubeTQRecursionStep
import Mathlib.Tactic

/-!
# Profile-preserving T/Q rematch

The existing T/Q recursion theorem intentionally compresses a lossless rematch
to a bare WholeCubeQTPair.  For finite-state termination we also need the
profile information already present in the T/Q witness: the new completion
owner w is a second-layer projected-loss core vertex.

This wrapper retains that information without changing the existing recursion
API.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def WholeCubeSecondCoordinateTQWholeRematch
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n) : Prop :=
  ∃ w : V, ∃ d : Fin n,
    w ∈ T ∧
    w ≠ v ∧
    w ≠ s ∧
    w ∈ projectedLossVertices C exponent ∧
    exponent w = n - 2 ∧
    d ∈ retainedActive C v ∧
    d ≠ c ∧
    WholeCubeQTPair C w v d

theorem wholeCubeSecondCoordinateTQ_rematch_or_halfCapture_profiled
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwit : WholeCubeSecondCoordinateTQ C exponent T s v c) :
    WholeCubeSecondCoordinateTQWholeRematch
      C exponent T s v c
    ∨
    (
      ∃ w : V, ∃ d : Fin n,
        w ∈ T ∧
        w ≠ v ∧
        w ≠ s ∧
        w ∈ projectedLossVertices C exponent ∧
        exponent w = n - 2 ∧
        d ∈ retainedActive C v ∧
        d ≠ c ∧
        WholeCubeSecondCoordinateTQHalfCapture C v w d
    ) := by
  obtain ⟨word,w,d,
      hdV,hdc,hvT,hwQ,
      hwT,hwNeV,hwNeS,
      hwLoss,hwSecond,hedge⟩ := hwit

  have hdW : d ∈ retainedActive C w := by
    rcases hedge with hedge | hedge
    · obtain ⟨hvw,hret,hcol⟩ := hedge
      have hm :=
        retainedColor_mem_retainedActive_right C hvw hret
      simpa [hcol] using hm
    · obtain ⟨hwv,hret,hcol⟩ := hedge
      have hm :=
        retainedColor_mem_retainedActive_left C hwv hret
      simpa [hcol] using hm

  have hinter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty :=
    ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩

  rcases secondLayer_TQ_wholeCube_or_half_source_cube
      C exponent hn3
      hvLoss hwLoss hvSecond hwSecond
      hdV hdW hinter
    with hwhole | hhalf
  · exact Or.inl
      ⟨w,d,
        hwT,hwNeV,hwNeS,
        hwLoss,hwSecond,
        hdV,hdc,hwhole⟩
  · right
    have hpos :
        0 < (translatedBaseCapture C v w d).card := by
      apply Finset.card_pos.mpr
      exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩
    exact ⟨w,d,
      hwT,hwNeV,hwNeS,
      hwLoss,hwSecond,
      hdV,hdc,
      hpos,hhalf⟩

#print axioms wholeCubeSecondCoordinateTQ_rematch_or_halfCapture_profiled

end OrderedEdgeColoring
end JSP000404Research
