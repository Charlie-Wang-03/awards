import JSP000404Research.ThreeWholeCubePartnerEdgeBitMatrix
import JSP000404Research.ThreeWholeCubeExtremeUniqueness
import Mathlib.Tactic

/-!
# Interior-source staircase versus the wrong global extreme

For a three-whole-cube star the source retained code and the three partner
codes differ by one owner bit.

Two finite contradictions are useful after the ordered-adjacent staircase has
been established.

* Source at the second ordered vertex b:
  if the rightmost owner-z partner d is the global maximum, then d is all-true.
  The source bits at x and y are therefore both true.  Hence the partner edge
  a-c between owners x and y must have the lower owner colour x.  A two-colour
  staircase forces that same edge to have colour y, contradiction.

* Source at the third ordered vertex c:
  if the leftmost owner-x partner a is the global minimum, then a is all-false.
  The source bits at y and z are therefore both false.  Hence the partner edge
  b-d between owners y and z must have the upper owner colour z.  The dual
  staircase forces it to have colour y, contradiction.

This is a pure retained-code/edge-colour core; projection geometry enters only
later when the staircase hypotheses are supplied.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem source_second_staircase_impossible_of_max_right_partner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {a b c d : V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxB : x ∈ retainedActive C b)
    (hyB : y ∈ retainedActive C b)
    (hzB : z ∈ retainedActive C b)
    (ha : WholeCubeQTPair C a b x)
    (hc : WholeCubeQTPair C c b y)
    (hd : WholeCubeQTPair C d b z)
    (hdLoss : d ∈ projectedLossVertices C exponent)
    (hmax : ∀ w : V, w ≠ d → w < d)
    (hac : a < c)
    (hretAC : (C.color a c).val < n)
    (hstairAC : retainedColor C a c hretAC = y) :
    False := by
  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hxB hyB hzB ha hc hd

  have hxD : x ∈ retainedActive C d := by
    rw [hstar.2.2.1]
    exact hxB
  have hyD : y ∈ retainedActive C d := by
    rw [hstar.2.2.1]
    exact hyB

  have hdTrue :
      AllRetainedBitsTrue C d :=
    projectedLoss_global_max_allTrue
      C exponent hdLoss hmax
  have hxDTrue : retainedBit C d x = true :=
    hdTrue x hxD
  have hyDTrue : retainedBit C d y = true :=
    hdTrue y hyD

  have hxEq :
      retainedBit C d x = retainedBit C b x :=
    hstar.2.2.2.2 x hxB hxz
  have hyEq :
      retainedBit C d y = retainedBit C b y :=
    hstar.2.2.2.2 y hyB hyz

  have hxBTrue : retainedBit C b x = true :=
    hxEq.symm.trans hxDTrue
  have hyBTrue : retainedBit C b y = true :=
    hyEq.symm.trans hyDTrue

  have howner :=
    wholeCube_partner_edge_eq_lower_owner_of_true_true
      C hxy hxB hyB ha hc hac hretAC hxBTrue hyBTrue
  apply hxy
  exact howner.symm.trans hstairAC

theorem source_third_staircase_impossible_of_min_left_partner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {a b c d : V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxC : x ∈ retainedActive C c)
    (hyC : y ∈ retainedActive C c)
    (hzC : z ∈ retainedActive C c)
    (ha : WholeCubeQTPair C a c x)
    (hb : WholeCubeQTPair C b c y)
    (hd : WholeCubeQTPair C d c z)
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hmin : ∀ w : V, w ≠ a → a < w)
    (hbd : b < d)
    (hretBD : (C.color b d).val < n)
    (hstairBD : retainedColor C b d hretBD = y) :
    False := by
  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hxC hyC hzC ha hb hd

  have hyA : y ∈ retainedActive C a := by
    rw [hstar.1.1]
    exact hyC
  have hzA : z ∈ retainedActive C a := by
    rw [hstar.1.1]
    exact hzC

  have haFalse :
      AllRetainedBitsFalse C a :=
    projectedLoss_global_min_allFalse
      C exponent haLoss hmin
  have hyAFalse : retainedBit C a y = false :=
    haFalse y hyA
  have hzAFalse : retainedBit C a z = false :=
    haFalse z hzA

  have hyEq :
      retainedBit C a y = retainedBit C c y :=
    hstar.1.2.2 y hyC hxy.symm
  have hzEq :
      retainedBit C a z = retainedBit C c z :=
    hstar.1.2.2 z hzC hxz.symm

  have hyCFalse : retainedBit C c y = false :=
    hyEq.symm.trans hyAFalse
  have hzCFalse : retainedBit C c z = false :=
    hzEq.symm.trans hzAFalse

  have howner :=
    wholeCube_partner_edge_eq_upper_owner_of_false_false
      C hyz hyC hzC hb hd hbd hretBD hyCFalse hzCFalse
  apply hyz
  exact hstairBD.symm.trans howner

#print axioms source_second_staircase_impossible_of_max_right_partner
#print axioms source_third_staircase_impossible_of_min_left_partner

end OrderedEdgeColoring
end JSP000404Research
