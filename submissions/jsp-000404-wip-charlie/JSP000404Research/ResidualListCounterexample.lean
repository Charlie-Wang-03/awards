import JSP000404Research.ResidualListCapacity
import Mathlib.Tactic

/-!
# Exact hard stop for naive residual safe-list elimination

The local condition used by `ResidualListCapacity` is sufficient, but it is
not a consequence of the abstract ordered-edge-colouring axioms.

On five ordered vertices, colour every increasing edge `i<j` by its lower
endpoint `i`, using four colours.  Consecutive increasing edges then always
have different colours.  If colour 3 is treated as residual, the edge
`3<4` is residual while the three retained colours 0,1,2 all occur on
incoming edges at vertex 3.  Hence its residual forbidden list is the whole
of `Fin 3`.

This exact finite example prevents the sufficient safe-list condition from
being silently promoted to an abstract theorem.  Any use in JSP-000404 must
exploit additional geometry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Four-colour lower-endpoint colouring on five ordered vertices. -/
def lowerEndpointColor5 (u _v : Fin 5) : Fin 4 :=
  if h : u.val < 4 then ⟨u.val, h⟩ else ⟨0, by omega⟩

def lowerEndpointColoring5 : OrderedEdgeColoring (Fin 5) 4 where
  color := lowerEndpointColor5
  noMonoTwoPath := by
    intro a v w hav hvw
    have ha4 : a.val < 4 := by
      have hav' : a.val < v.val := hav
      have hvw' : v.val < w.val := hvw
      have hw5 := w.isLt
      omega
    have hv4 : v.val < 4 := by
      have hvw' : v.val < w.val := hvw
      have hw5 := w.isLt
      omega
    intro heq
    have hval := congrArg Fin.val heq
    simp [lowerEndpointColor5, ha4, hv4] at hval
    have hav' : a.val < v.val := hav
    omega

/-- The last increasing edge has the residual colour 3. -/
theorem lowerEndpointColoring5_last_isResidual :
    IsResidual lowerEndpointColoring5 (3 : Fin 5) (4 : Fin 5) := by
  unfold IsResidual lowerEndpointColoring5 lowerEndpointColor5
  norm_num

/-- Every retained colour occurs on an incoming edge at vertex 3. -/
theorem lowerEndpointColoring5_all_retained_incoming
    (c : Fin 3) :
    c ∈ incomingRetained lowerEndpointColoring5 (3 : Fin 5) := by
  apply (mem_incomingRetained_iff
    lowerEndpointColoring5 (3 : Fin 5) c).2
  let a : Fin 5 := ⟨c.val, by omega⟩
  refine ⟨a, ?_, ?_⟩
  · change c.val < 3
    exact c.isLt
  · apply Fin.ext
    simp [lowerEndpointColoring5, lowerEndpointColor5, a]
    omega

/-- Therefore the forbidden list of the residual edge 3--4 is all three
retained colours. -/
theorem lowerEndpointColoring5_residualForbidden_eq_univ :
    residualForbidden lowerEndpointColoring5 (3 : Fin 5) (4 : Fin 5) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro c
  apply Finset.mem_union_left
  exact lowerEndpointColoring5_all_retained_incoming c

theorem lowerEndpointColoring5_residualForbidden_card :
    (residualForbidden
      lowerEndpointColoring5 (3 : Fin 5) (4 : Fin 5)).card = 3 := by
  rw [lowerEndpointColoring5_residualForbidden_eq_univ]
  simp

#print axioms lowerEndpointColoring5
#print axioms lowerEndpointColoring5_last_isResidual
#print axioms lowerEndpointColoring5_residualForbidden_eq_univ
#print axioms lowerEndpointColoring5_residualForbidden_card

end OrderedEdgeColoring
end JSP000404Research
