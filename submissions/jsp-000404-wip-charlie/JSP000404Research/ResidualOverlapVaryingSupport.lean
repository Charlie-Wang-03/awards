import JSP000404Research.OverlapVaryingCoordinatesCore
import JSP000404Research.ResidualOverlapCube
import Mathlib.Tactic

/-!
# Varying coordinates of a retained-completion overlap cube

A nonempty intersection of two retained completion cubes fixes exactly the
coordinates active at at least one endpoint.  Its genuinely varying
coordinates are therefore exactly the coordinates inactive at both endpoints.

This gives a set-valued invariant stronger than overlap cardinality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem overlapVaryingCoordinates_eq_commonRetainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    overlapVaryingCoordinates
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v)
      =
    commonRetainedInactive C u v := by
  classical
  ext c
  rw [mem_overlapVaryingCoordinates,
      mem_commonRetainedInactive]
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    have hxParts := Finset.mem_inter.mp hx
    have hyParts := Finset.mem_inter.mp hy
    constructor
    · intro hcu
      have hxFix :=
        (mem_retainedCompletionWords C u x).1
          hxParts.1 c hcu
      have hyFix :=
        (mem_retainedCompletionWords C u y).1
          hyParts.1 c hcu
      exact hxy (hxFix.trans hyFix.symm)
    · intro hcv
      have hxFix :=
        (mem_retainedCompletionWords C v x).1
          hxParts.2 c hcv
      have hyFix :=
        (mem_retainedCompletionWords C v y).1
          hyParts.2 c hcv
      exact hxy (hxFix.trans hyFix.symm)
  · rintro ⟨hcu,hcv⟩
    let y := flipBoolWordAt base c
    have hyU :
        y ∈ retainedCompletionWords C u := by
      dsimp [y]
      exact
        (mem_retainedCompletionWords_flip_iff_of_inactive
          C hcu).2 hbaseU
    have hyV :
        y ∈ retainedCompletionWords C v := by
      dsimp [y]
      exact
        (mem_retainedCompletionWords_flip_iff_of_inactive
          C hcv).2 hbaseV
    refine ⟨base,
      Finset.mem_inter.mpr ⟨hbaseU,hbaseV⟩,
      y,
      Finset.mem_inter.mpr ⟨hyU,hyV⟩,
      ?_⟩
    dsimp [y]
    cases hb : base c <;>
      simp [flipBoolWordAt, hb]

#print axioms overlapVaryingCoordinates_eq_commonRetainedInactive

end OrderedEdgeColoring
end JSP000404Research
