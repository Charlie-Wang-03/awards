import JSP000404Research.ResidualHardOverlapCubeSoftRouting
import Mathlib.Tactic

/-!
# Pairwise disjoint completion cubes of residual-edge upper endpoints

If a<v and b<z are two residual edges and v≠z, then
their upper-endpoint retained completion cubes Q_v and Q_z
are disjoint.

Indeed, an intersection of completion cubes at v,z forces
an edge of residual colour between v and z. If v<z,
the residual two-path a<v<z is forbidden; if z<v,
the residual two-path b<z<v is forbidden.

This is a GLOBAL structural property of all residual edges,
independent of the same-retained condition or any planar hypothesis.
In particular, it prevents two distinct hard-pair upper cubes
from colliding under any later full-face transport.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Different upper endpoints of (possibly unrelated) residual
edges have DISJOINT retained Boolean completion cubes. -/
theorem residual_upper_completion_cubes_disjoint
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v b z : V}
    (hav : a < v)
    (hbz : b < z)
    (hresAV : IsResidual C a v)
    (hresBZ : IsResidual C b z)
    (hvz : v ≠ z) :
    Disjoint (retainedCompletionWords C v)
      (retainedCompletionWords C z) := by
  classical
  rw [Finset.disjoint_left]
  intro word hvword hzword
  rcases retainedCompletion_overlap_forces_residual
      C hvz hvword hzword with hforward | hbackward
  · exact no_two_residual_on_path
      C hav hforward.1 hresAV hforward.2
  · exact no_two_residual_on_path
      C hbz hbackward.1 hresBZ hbackward.2

/-- A shared Boolean word determines the upper endpoint of a
residual carrier uniquely, even across distinct residual edges. -/
theorem residual_upper_completion_word_unique
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v b z : V} {word : Fin n → Bool}
    (hav : a < v)
    (hbz : b < z)
    (hresAV : IsResidual C a v)
    (hresBZ : IsResidual C b z)
    (hvword : word ∈ retainedCompletionWords C v)
    (hzword : word ∈ retainedCompletionWords C z) :
    v = z := by
  by_contra hvz
  exact (Finset.disjoint_left.mp
    (residual_upper_completion_cubes_disjoint
      C hav hbz hresAV hresBZ hvz))
    hvword hzword

#print axioms residual_upper_completion_cubes_disjoint
#print axioms residual_upper_completion_word_unique

end OrderedEdgeColoring
end JSP000404Research
