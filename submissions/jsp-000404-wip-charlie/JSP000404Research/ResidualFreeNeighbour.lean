import JSP000404Research.ResidualVerticalPairs
import Mathlib.Tactic

/-!
# A common inactive retained coordinate gives a free neighbour code

Let u,v be a vertical pair: they agree on every retained bit and are distinct,
so their residual bits are opposite.

Suppose a retained colour c is inactive at both u and v.  Consider the Boolean
n-code obtained from their common retained code by flipping coordinate c.

No third original vertex can have that retained code.

Indeed, if a candidate w has the same residual bit as u, then u and w differ
only at retained coordinate c; the separation theorem would force colour c to
be active at u, contradiction.  If w has the opposite residual bit, it equals
the residual bit of v, and the same argument with v gives the contradiction.

This is a local repair certificate for hard residual vertical pairs.  Global
repair still requires choosing distinct free neighbour codes for distinct
vertical pairs.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Distinct vertices with equal retained code have opposite residual bits. -/
theorem residualBit_ne_of_same_retained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u ≠ v)
    (hret : ∀ d : Fin n, retainedBit C u d = retainedBit C v d) :
    bit C u (residualCoord n) ≠ bit C v (residualCoord n) := by
  intro hres
  exact huv (eq_of_retainedBits_eq_of_residualBit_eq C hret hres)

/-- If two vertices have equal residual bits and agree on every retained bit
except possibly c, then any separating old colour must be c. -/
theorem separator_eq_castSucc_of_only_retained_difference
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} (huw : u ≠ w) (c : Fin n)
    (hsame :
      ∀ d : Fin n, d ≠ c →
        retainedBit C u d = retainedBit C w d)
    (hres :
      bit C u (residualCoord n) =
        bit C w (residualCoord n)) :
    ∃ hcu : c.castSucc ∈ active C u,
      c.castSucc ∈ active C w := by
  obtain ⟨d, hdu, hdw, hbit⟩ := separates C u w huw
  have hd : d = c.castSucc := by
    by_cases hlt : d.val < n
    · let e : Fin n := ⟨d.val, hlt⟩
      have hecast : e.castSucc = d := by
        apply Fin.ext
        rfl
      by_cases hec : e = c
      · subst e
        exact hecast.symm
      · have heq := hsame e hec
        have : bit C u d = bit C w d := by
          simpa [retainedBit, hecast] using heq
        exact False.elim (hbit this)
    · have hdval : d.val = n := by
        have hdlt := d.isLt
        omega
      have hdres : d = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using hdval
      have : bit C u d = bit C w d := by
        simpa [hdres] using hres
      exact False.elim (hbit this)
  subst d
  exact ⟨hdu, hdw⟩

/-- A common inactive coordinate of a vertical pair cannot be occupied by a
third vertex after flipping that coordinate in the retained code. -/
theorem flipped_common_inactive_code_is_free
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} (c : Fin n)
    (huv : u ≠ v)
    (hret : ∀ d : Fin n, retainedBit C u d = retainedBit C v d)
    (hcu : c.castSucc ∉ active C u)
    (hcv : c.castSucc ∉ active C v)
    (hflip :
      retainedBit C w c ≠ retainedBit C u c)
    (hsame :
      ∀ d : Fin n, d ≠ c →
        retainedBit C w d = retainedBit C u d) :
    w = u ∨ w = v := by
  by_cases hwu : w = u
  · exact Or.inl hwu
  by_cases hwv : w = v
  · exact Or.inr hwv
  have huvRes :=
    residualBit_ne_of_same_retained C huv hret
  by_cases hreswu :
      bit C w (residualCoord n) = bit C u (residualCoord n)
  · have hsep :=
      separator_eq_castSucc_of_only_retained_difference
        C hwu c
        (fun d hdc => (hsame d hdc).symm)
        hreswu.symm
    exact False.elim (hcu hsep.1)
  · have hreswv :
        bit C w (residualCoord n) =
          bit C v (residualCoord n) := by
      cases hu : bit C u (residualCoord n) <;>
        cases hv : bit C v (residualCoord n) <;>
        cases hw : bit C w (residualCoord n) <;>
        simp_all
    have hsameVW :
        ∀ d : Fin n, d ≠ c →
          retainedBit C v d = retainedBit C w d := by
      intro d hdc
      exact (hret d).symm.trans (hsame d hdc).symm
    have hsep :=
      separator_eq_castSucc_of_only_retained_difference
        C hwv.symm c hsameVW hreswv.symm
    exact False.elim (hcv hsep.1)

/-- The target flipped code is genuinely different from both members of the
vertical pair, so the previous theorem says it is absent from the original
vertex set. -/
theorem no_vertex_realizes_flipped_common_inactive_code
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} (c : Fin n)
    (huv : u ≠ v)
    (hret : ∀ d : Fin n, retainedBit C u d = retainedBit C v d)
    (hcu : c.castSucc ∉ active C u)
    (hcv : c.castSucc ∉ active C v) :
    ¬ ∃ w : V,
      retainedBit C w c ≠ retainedBit C u c ∧
      (∀ d : Fin n, d ≠ c →
        retainedBit C w d = retainedBit C u d) := by
  rintro ⟨w, hflip, hsame⟩
  have hw :=
    flipped_common_inactive_code_is_free
      C c huv hret hcu hcv hflip hsame
  rcases hw with rfl | rfl
  · exact hflip rfl
  · have hcEq : retainedBit C v c = retainedBit C u c :=
      (hret c).symm
    exact hflip hcEq

#print axioms residualBit_ne_of_same_retained
#print axioms separator_eq_castSucc_of_only_retained_difference
#print axioms flipped_common_inactive_code_is_free
#print axioms no_vertex_realizes_flipped_common_inactive_code

end OrderedEdgeColoring
end JSP000404Research
