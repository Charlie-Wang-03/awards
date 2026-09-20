import JSP000404Research.ResidualFreeNeighbour
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Monotone blockers of one-coordinate Boolean repairs

Let u<v be a hard residual vertical pair: u and v have the same retained
Boolean code.  Fix a retained coordinate c which is inactive at the lower
endpoint u.  Flip c in the common retained code.

If that neighbouring retained code is occupied by a third vertex w, then the
occupant is strongly constrained:

* its residual bit cannot equal the residual bit of u, because then the only
  possible separating colour between u and w would be c, contradicting
  inactivity of c at u;
* hence its residual bit equals the residual bit of v;
* the edge joining v and w can only have retained colour c;
* since c is inactive at u, the common c-bit of u and v is false, whereas the
  blocker c-bit is true.  Canonical edge-bit orientation therefore forces
  v < w.

Thus every blocked lower-end repair moves strictly to the right of the hard
pair.  This is the acyclicity mechanism needed by a future augmenting-chain /
Hall argument.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A vertex occupying the retained-code neighbour obtained by flipping one
coordinate of u. -/
def RetainedNeighbourBlocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) (c : Fin n) (w : V) : Prop :=
  retainedBit C w c ≠ retainedBit C u c ∧
  ∀ d : Fin n, d ≠ c →
    retainedBit C u d = retainedBit C w d

theorem blocker_ne_base
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    {u w : V} {c : Fin n}
    (hblock : RetainedNeighbourBlocker C u c w) :
    w ≠ u := by
  intro hwu
  subst w
  exact hblock.1 rfl

/-- If c is inactive at u, a blocker cannot have the same residual bit as u. -/
theorem blocker_residualBit_ne_base_of_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} {c : Fin n}
    (hcu : c.castSucc ∉ active C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    bit C w (residualCoord n) ≠
      bit C u (residualCoord n) := by
  intro hres
  have hwu : u ≠ w := (blocker_ne_base hblock).symm
  have hsep :=
    separator_eq_castSucc_of_only_retained_difference
      C hwu c hblock.2 hres.symm
  exact hcu hsep.1

/-- For a vertical pair u,v, a blocker of an inactive coordinate at u has the
same residual bit as the opposite endpoint v. -/
theorem blocker_residualBit_eq_other_of_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (huv : u ≠ v)
    (hret : ∀ d : Fin n,
      retainedBit C u d = retainedBit C v d)
    (hcu : c.castSucc ∉ active C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    bit C w (residualCoord n) =
      bit C v (residualCoord n) := by
  have huvRes :=
    residualBit_ne_of_same_retained C huv hret
  have hwuRes :=
    blocker_residualBit_ne_base_of_inactive
      C hcu hblock
  cases hu : bit C u (residualCoord n) <;>
    cases hv : bit C v (residualCoord n) <;>
    cases hw : bit C w (residualCoord n) <;>
    simp_all

/-- If two vertices have equal residual bits and all retained bits agree away
from c, then their increasing edge has retained colour c. -/
theorem edgeColor_eq_castSucc_of_only_retained_difference
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {x y : V} (hxy : x < y) (c : Fin n)
    (hsame : ∀ d : Fin n, d ≠ c →
      retainedBit C x d = retainedBit C y d)
    (hres :
      bit C x (residualCoord n) =
        bit C y (residualCoord n)) :
    C.color x y = c.castSucc := by
  by_cases hret : (C.color x y).val < n
  · let d : Fin n := retainedColor C x y hret
    have hne :
        retainedBit C x d ≠ retainedBit C y d :=
      retainedBit_ne_of_retained_edge C hxy hret
    have hdc : d = c := by
      by_contra h
      exact hne (hsame d h)
    apply Fin.ext
    have hval := congrArg Fin.val hdc
    simpa [d, retainedColor] using hval
  · have hval : (C.color x y).val = n := by
      have hlt := (C.color x y).isLt
      omega
    have hcol : C.color x y = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using hval
    have hne := edgeColor_bit_ne C hxy
    rw [hcol] at hne
    exact False.elim (hne hres)

/-- Inactivity of a retained coordinate makes its canonical retained bit false. -/
theorem retainedBit_eq_false_of_not_mem_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) (c : Fin n)
    (hcu : c.castSucc ∉ active C u) :
    retainedBit C u c = false := by
  unfold retainedBit
  exact bit_eq_false_of_not_mem_active C u c.castSucc hcu

/-- Main monotonicity theorem: a blocker of a lower-end inactive coordinate
lies strictly beyond the upper endpoint of the hard vertical pair. -/
theorem blocker_after_other_of_lower_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (huv : u < v)
    (hret : ∀ d : Fin n,
      retainedBit C u d = retainedBit C v d)
    (hcu : c.castSucc ∉ active C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    v < w := by
  have huvNe : u ≠ v := ne_of_lt huv
  have hresWV :
      bit C w (residualCoord n) =
        bit C v (residualCoord n) :=
    blocker_residualBit_eq_other_of_inactive
      C huvNe hret hcu hblock
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact hblock.1 (hret c).symm
  have hvfalse : retainedBit C v c = false := by
    have hufalse :=
      retainedBit_eq_false_of_not_mem_active C u c hcu
    exact (hret c).symm.trans hufalse
  rcases lt_or_gt_of_ne hwv with hwvlt | hvw
  · have hsameWV :
        ∀ d : Fin n, d ≠ c →
          retainedBit C w d = retainedBit C v d := by
      intro d hdc
      exact (hblock.2 d hdc).symm.trans (hret d)
    have hcol :
        C.color w v = c.castSucc :=
      edgeColor_eq_castSucc_of_only_retained_difference
        C hwvlt c hsameWV hresWV
    have hvtrueRaw :=
      edgeColor_bit_upper_eq_true C hwvlt
    rw [hcol] at hvtrueRaw
    have hvtrue : retainedBit C v c = true := by
      simpa [retainedBit] using hvtrueRaw
    rw [hvfalse] at hvtrue
    contradiction
  · exact hvw

#print axioms blocker_ne_base
#print axioms blocker_residualBit_ne_base_of_inactive
#print axioms blocker_residualBit_eq_other_of_inactive
#print axioms edgeColor_eq_castSucc_of_only_retained_difference
#print axioms retainedBit_eq_false_of_not_mem_active
#print axioms blocker_after_other_of_lower_inactive

end OrderedEdgeColoring
end JSP000404Research
