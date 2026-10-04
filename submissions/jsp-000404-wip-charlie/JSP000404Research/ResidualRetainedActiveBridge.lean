import JSP000404Research.ResidualSafeTarget
import Mathlib.Tactic

/-!
# Lightweight retained-active / active bridge

Basic set-theoretic relation between a retained colour and the old active
palette.  Kept separate from the Boolean hole-injection machinery so local
projection-loss arguments do not inherit global repair dependencies.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem castSucc_mem_active_iff_mem_retainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    c.castSucc ∈ active C v ↔ c ∈ retainedActive C v := by
  classical
  simp [active, retainedActive]

end OrderedEdgeColoring
end JSP000404Research
