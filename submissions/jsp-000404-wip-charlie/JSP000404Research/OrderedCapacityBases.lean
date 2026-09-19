import JSP000404Research.OrderedDirections
import Mathlib.Tactic

/-!
# Sharp finite base capacities for ordered directions

These are the two base cases required by the prospective doubling recurrence:

* five ordered vertices force width at least `5/2`;
* six ordered vertices force width at least `3`.

The proofs use only the abstract `DirectionData` axioms and finite linear
orientation elimination.  They do not use Sendov's disputed optimizer claim.
-/

namespace JSP000404Research
namespace DirectionData

set_option maxHeartbeats 2500000 in
/-- Five strictly ordered vertices force direction width at least `5/2`. -/
theorem fivePoint_width
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {v0 v1 v2 v3 v4 : V}
    (h01 : v0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) :
    (5 : ℝ) / 2 ≤ width := by
  have h02 : v0 < v2 := h01.trans h12
  have h03 : v0 < v3 := h02.trans h23
  have h04 : v0 < v4 := h03.trans h34
  have h13 : v1 < v3 := h12.trans h23
  have h14 : v1 < v4 := h13.trans h34
  have h24 : v2 < v4 := h23.trans h34
  have t012 := triple_constraints D h01 h12
  have t013 := triple_constraints D h01 h13
  have t014 := triple_constraints D h01 h14
  have t023 := triple_constraints D h02 h23
  have t024 := triple_constraints D h02 h24
  have t034 := triple_constraints D h03 h34
  have t123 := triple_constraints D h12 h23
  have t124 := triple_constraints D h12 h24
  have t134 := triple_constraints D h13 h34
  have t234 := triple_constraints D h23 h34
  rcases t012 with t012 | t012 <;>
    rcases t013 with t013 | t013 <;>
    rcases t014 with t014 | t014 <;>
    rcases t023 with t023 | t023 <;>
    rcases t024 with t024 | t024 <;>
    rcases t034 with t034 | t034 <;>
    rcases t123 with t123 | t123 <;>
    rcases t124 with t124 | t124 <;>
    rcases t134 with t134 | t134 <;>
    rcases t234 with t234 | t234 <;> linarith

set_option maxHeartbeats 4500000 in
/-- Six strictly ordered vertices force direction width at least `3`.

The branch search is pruned by linear arithmetic after every orientation split;
the already-proved five-point bound supplies the sharp lower starting range.
-/
theorem sixPoint_width
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {v0 v1 v2 v3 v4 v5 : V}
    (h01 : v0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) :
    (3 : ℝ) ≤ width := by
  by_contra hnot
  have hfive : (5 : ℝ) / 2 ≤ width := fivePoint_width D h01 h12 h23 h34
  have hlt : width < 3 := lt_of_not_ge hnot
  have h02 := h01.trans h12
  have h03 := h02.trans h23
  have h04 := h03.trans h34
  have h05 := h04.trans h45
  have h13 := h12.trans h23
  have h14 := h13.trans h34
  have h15 := h14.trans h45
  have h24 := h23.trans h34
  have h25 := h24.trans h45
  have h35 := h34.trans h45

  have t012 := triple_constraints D h01 h12
  have t123 := triple_constraints D h12 h23
  have t234 := triple_constraints D h23 h34
  have t345 := triple_constraints D h34 h45
  have t023 := triple_constraints D h02 h23
  have t124 := triple_constraints D h12 h24
  have t235 := triple_constraints D h23 h35
  have t034 := triple_constraints D h03 h34
  have t125 := triple_constraints D h12 h25
  have t014 := triple_constraints D h01 h14
  have t145 := triple_constraints D h14 h45
  have t025 := triple_constraints D h02 h25
  have t035 := triple_constraints D h03 h35
  have t015 := triple_constraints D h01 h15
  have t045 := triple_constraints D h04 h45
  have t013 := triple_constraints D h01 h13
  have t024 := triple_constraints D h02 h24
  have t134 := triple_constraints D h13 h34
  have t135 := triple_constraints D h13 h35
  have t245 := triple_constraints D h24 h45

  all_goals rcases t012 with t012 | t012 <;> try linarith
  all_goals rcases t123 with t123 | t123 <;> try linarith
  all_goals rcases t234 with t234 | t234 <;> try linarith
  all_goals rcases t345 with t345 | t345 <;> try linarith
  all_goals rcases t023 with t023 | t023 <;> try linarith
  all_goals rcases t124 with t124 | t124 <;> try linarith
  all_goals rcases t235 with t235 | t235 <;> try linarith
  all_goals rcases t034 with t034 | t034 <;> try linarith
  all_goals rcases t125 with t125 | t125 <;> try linarith
  all_goals rcases t014 with t014 | t014 <;> try linarith
  all_goals rcases t145 with t145 | t145 <;> try linarith
  all_goals rcases t025 with t025 | t025 <;> try linarith
  all_goals rcases t035 with t035 | t035 <;> try linarith
  all_goals rcases t015 with t015 | t015 <;> try linarith
  all_goals rcases t045 with t045 | t045 <;> try linarith
  all_goals rcases t013 with t013 | t013 <;> try linarith
  all_goals rcases t024 with t024 | t024 <;> try linarith
  all_goals rcases t134 with t134 | t134 <;> try linarith
  all_goals rcases t135 with t135 | t135 <;> try linarith
  all_goals rcases t245 with t245 | t245 <;> linarith

#print axioms fivePoint_width
#print axioms sixPoint_width

end DirectionData
end JSP000404Research
