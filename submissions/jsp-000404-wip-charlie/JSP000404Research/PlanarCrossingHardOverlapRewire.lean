import JSP000404Research.PlanarCrossingHardFlipCubeObstruction
import JSP000404Research.ResidualCompletionOverlapRewire
import JSP000404Research.StandardResidualSafeHardDescent
import Mathlib.Tactic

/-!
# Planar safe-flip overlap rewiring to a singleton or resolved interior pair

For actual planar AngleCap crossing hard carriers, the previously obtained
oriented safe flip has a more precise CUBE-overlap interpretation.

The original canonical retained base is doubly covered. The flipped
Boolean word is necessarily covered; either it is singly covered, or its
second covering vertex w lies strictly between a and v, with a-w
coloured by the flipped retained colour and w-v a residual edge
already RETAINED-SEPARATED by the genuine standard residual geometry.

This does not establish a globally injective allocation of excess
completion mass and therefore does not discharge the one remaining
global lower-branch payment sorry.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_crossing_hard_overlap_singleton_or_resolved_interior
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (u a v b : ProjectionOrdered V)
    (hua :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      u < a)
    (hav :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < v)
    (hvb :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      v < b)
    (hHard :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let hpos : 0 < t := by
        rw [ht]
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      let hwidth : t < ((n + 1 : ℕ) : ℝ) := by
        rw [ht]
        push_cast
        linarith
      let D := genericDirectionData_sendov hp hcap hpos hlam
      let B := standardResidualColoring D n hwidth
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      (∃ wordUV wordAB : Fin n → Bool,
        (¬ ∃ c : Fin n, c ∉ residualForbidden B u v) ∧
        (¬ ∃ c : Fin n, c ∉ residualForbidden B a b) ∧
        wordUV ∈ retainedCompletionWords B u ∧
        wordUV ∈ retainedCompletionWords B v ∧
        wordAB ∈ retainedCompletionWords B a ∧
        wordAB ∈ retainedCompletionWords B b) ∧
      n ≤ k a + k v ∧
      SameRetained B a v ∧
      (¬ ∃ c : Fin n,
        c ∉ retainedActive B a ∧
        c ∉ retainedActive B v)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < ((n + 1 : ℕ) : ℝ) := by
      rw [ht]
      push_cast
      linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n hwidth
    ∃ c : Fin n,
      c ∉ residualForbidden B a v ∧
      c ∈ outgoingRetained B a ∧
      c ∉ retainedActive B v ∧
      (fun d => retainedBit B a d) ∈ overlapCompletionWords B ∧
      flippedRetainedCode B a c ∈ coveredCompletionWords B ∧
      ((completionFibre B (flippedRetainedCode B a c)).card = 1 ∨
        ∃ w : ProjectionOrdered V,
          a < w ∧ w < v ∧
          IsResidual B w v ∧
          RetainedSeparated B w v ∧
          B.color a w = c.castSucc ∧
          Disjoint (retainedCompletionWords B a)
            (retainedCompletionWords B w)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < ((n + 1 : ℕ) : ℝ) := by
    rw [ht]
    push_cast
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  have hsame : SameRetained B a v := hHard.2.2.1
  have hav' : a < v := hav
  have hresAV : IsResidual B a v :=
    isResidual_of_sameRetained_lt B hav' hsame
  obtain ⟨c, hsafe, hout, hinactive, hcovered, _hprevious⟩ :=
    planar_crossing_safe_flip_is_covered_or_resolves_or_descends
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      cycles u a v b hua hav hvb hHard
  obtain ⟨hbase, hroute⟩ :=
    oriented_safe_flip_overlap_singleton_or_interior_rewire
      B c hav' hsame hout hinactive
  refine ⟨c, hsafe, hout, hinactive, hbase, hcovered, ?_⟩
  rcases hroute with hsingle | hnew
  · exact Or.inl hsingle
  · right
    obtain ⟨w, haw, hwv, hresWV, hcol, hdisjoint⟩ := hnew
    have hresolve :=
      safe_hard_interior_witness_resolves
        D n (by omega : 0 < n) hwidth haw hwv
        hresAV hsame hcol
    exact ⟨w, haw, hwv, hresWV, hresolve.2, hcol, hdisjoint⟩

#print axioms planar_crossing_hard_overlap_singleton_or_resolved_interior

end ProjectionOrdered
end JSP000404Research
