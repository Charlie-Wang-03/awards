import JSP000404Research.ResidualBlocker
import JSP000404Research.ResidualHoleInjection
import Mathlib.Tactic

/-!
# Boolean-code spelling of retained-neighbour blockers

Keep the local blocker geometry independent of the global hole-injection
construction.  This bridge is the only place that identifies the blocker
predicate with equality to the one-coordinate flipped retained code.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedCode_eq_flipped_iff_blocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u w : V) (c : Fin n) :
    (fun d => retainedBit C w d) =
        flippedRetainedCode C u c
      ↔
    RetainedNeighbourBlocker C u c w := by
  constructor
  · intro h
    constructor
    · have hc := congrFun h c
      intro heq
      apply flippedRetainedCode_at_ne C u c
      rw [← hc, heq]
    · intro d hdc
      have hd := congrFun h d
      rw [flippedRetainedCode_off C u c d hdc] at hd
      exact hd.symm
  · intro h
    funext d
    by_cases hdc : d = c
    · subst d
      have hne := h.1
      cases hu : retainedBit C u c <;>
        cases hw : retainedBit C w c <;>
        simp_all [flippedRetainedCode]
    · rw [flippedRetainedCode_off C u c d hdc]
      exact (h.2 d hdc).symm

#print axioms retainedCode_eq_flipped_iff_blocker

end OrderedEdgeColoring
end JSP000404Research
