import JSP000404Research.ResidualBlocker
import JSP000404Research.StandardResidualSafeHardDescent
import Mathlib.Tactic

/-!
# Blockers of safe-oriented flips

Let u<v be a same-retained hard pair.  Let c be a retained colour which is
outgoing at u and inactive at v.  This is exactly the oriented safe branch
which remains when the pair has no common inactive coordinate.

Flip coordinate c in the common retained code.  If a vertex w realizes that
flipped code, then:

* w cannot have the residual bit of v, because v and w would differ only at c
  and equal residual bits would force c active at v;
* therefore w has the residual bit of u;
* the edge joining u and w has retained colour c;
* because c is outgoing at u, the canonical c-bit of u is false, so w cannot
  lie before u.  Hence u<w.

For the standard residual geometry, compare w with v.  If u<w<v, the hard
outer-pair XOR makes w--v residual while the retained code already separates
w from v.  Otherwise v<w.  Thus an occupied safe-coordinate flip either
resolves the hard collision inside the interval or moves strictly to the
right.

This is the monotone augmenting mechanism needed for a Boolean-hole proof.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An oriented safe coordinate is false in the lower canonical retained
code, because it is outgoing and incoming/outgoing sets are disjoint. -/
theorem retainedBit_false_of_outgoing
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u : V} {c : Fin n}
    (hcOut : c ∈ outgoingRetained C u) :
    retainedBit C u c = false := by
  unfold retainedBit
  apply bit_eq_false_iff.mpr
  intro hex
  have hcIn :
      c ∈ incomingRetained C u :=
    (mem_incomingRetained_iff C u c).2 hex
  exact Finset.disjoint_left.mp
    (incomingRetained_disjoint_outgoingRetained C u)
    hcIn hcOut

/-- A blocker of the oriented safe flip cannot carry the upper endpoint's
residual bit. -/
theorem safeFlip_blocker_residualBit_ne_upper
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hsame : SameRetained C u v)
    (hcInactiveV : c ∉ retainedActive C v)
    (hblock : RetainedNeighbourBlocker C u c w) :
    bit C w (residualCoord n) ≠
      bit C v (residualCoord n) := by
  intro hresWV
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact hblock.1 (hsame c)
  have hsameVW :
      ∀ d : Fin n, d ≠ c →
        retainedBit C v d = retainedBit C w d := by
    intro d hdc
    exact (hsame d).symm.trans (hblock.2 d hdc)
  have hsep :=
    separator_eq_castSucc_of_only_retained_difference
      C hwv c hsameVW hresWV.symm
  exact hcInactiveV
    ((castSucc_mem_active_iff_mem_retainedActive C v c).1
      hsep.1)

/-- Since the hard pair has opposite residual bits, the blocker has exactly
the lower endpoint's residual bit. -/
theorem safeFlip_blocker_residualBit_eq_lower
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (huv : u ≠ v)
    (hsame : SameRetained C u v)
    (hcInactiveV : c ∉ retainedActive C v)
    (hblock : RetainedNeighbourBlocker C u c w) :
    bit C w (residualCoord n) =
      bit C u (residualCoord n) := by
  have huvRes :=
    residualBit_ne_of_same_retained C huv hsame
  have hwvRes :=
    safeFlip_blocker_residualBit_ne_upper
      C hsame hcInactiveV hblock
  cases hu : bit C u (residualCoord n) <;>
    cases hv : bit C v (residualCoord n) <;>
    cases hw : bit C w (residualCoord n) <;>
    simp_all

/-- The blocker lies after the lower endpoint. -/
theorem safeFlip_blocker_after_lower
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hcOutU : c ∈ outgoingRetained C u)
    (hcInactiveV : c ∉ retainedActive C v)
    (hblock : RetainedNeighbourBlocker C u c w) :
    u < w := by
  have hwu : w ≠ u :=
    blocker_ne_base hblock
  have hresWU :
      bit C w (residualCoord n) =
        bit C u (residualCoord n) :=
    safeFlip_blocker_residualBit_eq_lower
      C (ne_of_lt huv) hsame hcInactiveV hblock
  have huFalse :
      retainedBit C u c = false :=
    retainedBit_false_of_outgoing C hcOutU
  rcases lt_or_gt_of_ne hwu with hwuLt | huw
  · have hsameWU :
        ∀ d : Fin n, d ≠ c →
          retainedBit C w d = retainedBit C u d := by
      intro d hdc
      exact (hblock.2 d hdc).symm
    have hcol :
        C.color w u = c.castSucc :=
      edgeColor_eq_castSucc_of_only_retained_difference
        C hwuLt c hsameWU hresWU
    have huTrueRaw :=
      edgeColor_bit_upper_eq_true C hwuLt
    rw [hcol] at huTrueRaw
    have huTrue :
        retainedBit C u c = true := by
      simpa [retainedBit] using huTrueRaw
    rw [huFalse] at huTrue
    contradiction
  · exact huw

/-- The edge from the lower endpoint to its blocker has precisely the flipped
retained colour. -/
theorem safeFlip_blocker_edgeColor_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hcOutU : c ∈ outgoingRetained C u)
    (hcInactiveV : c ∉ retainedActive C v)
    (hblock : RetainedNeighbourBlocker C u c w) :
    C.color u w = c.castSucc := by
  have huw :=
    safeFlip_blocker_after_lower
      C huv hsame hcOutU hcInactiveV hblock
  have hresWU :
      bit C w (residualCoord n) =
        bit C u (residualCoord n) :=
    safeFlip_blocker_residualBit_eq_lower
      C (ne_of_lt huv) hsame hcInactiveV hblock
  exact edgeColor_eq_castSucc_of_only_retained_difference
    C huw c hblock.2 hresWU.symm

/-- Function-valued occupation of the flipped retained code is exactly the
blocker predicate. -/
theorem safeFlip_occupied_iff_blocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u w : V) (c : Fin n) :
    (fun d => retainedBit C w d) =
        flippedRetainedCode C u c
      ↔
    RetainedNeighbourBlocker C u c w :=
  retainedCode_eq_flipped_iff_blocker C u w c

#print axioms retainedBit_false_of_outgoing
#print axioms safeFlip_blocker_residualBit_ne_upper
#print axioms safeFlip_blocker_residualBit_eq_lower
#print axioms safeFlip_blocker_after_lower
#print axioms safeFlip_blocker_edgeColor_eq

end OrderedEdgeColoring

namespace DirectionData

open OrderedEdgeColoring

/-- In standard residual geometry, an occupied safe-oriented flip either
produces an interior residual edge which is already retained-separated, or
its blocker lies strictly to the right of the hard pair. -/
theorem safeFlip_blocker_resolves_or_after_upper
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v w : V} {c : Fin n}
    (huv : u < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v)
    (hcOutU :
      c ∈ outgoingRetained
        (standardResidualColoring D n hwidth) u)
    (hcInactiveV :
      c ∉ retainedActive
        (standardResidualColoring D n hwidth) v)
    (hblock :
      RetainedNeighbourBlocker
        (standardResidualColoring D n hwidth) u c w) :
    (u < w ∧ w < v ∧
      IsResidual
        (standardResidualColoring D n hwidth) w v ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) w v)
    ∨
    v < w := by
  let C := standardResidualColoring D n hwidth
  have huw :
      u < w :=
    safeFlip_blocker_after_lower
      C huv hsame hcOutU hcInactiveV hblock
  have hcol :
      C.color u w = c.castSucc :=
    safeFlip_blocker_edgeColor_eq
      C huv hsame hcOutU hcInactiveV hblock
  rcases lt_trichotomy w v with hwv | hwEq | hvw
  · left
    have hresolved :=
      safe_hard_interior_witness_resolves
        D n hn hwidth huw hwv hres hsame hcol
    exact ⟨huw, hwv, hresolved.1, hresolved.2⟩
  · subst w
    exact False.elim
      (hblock.1 (hsame c))
  · exact Or.inr hvw

/-- Every safe-oriented coordinate has one of three outcomes: its one-bit
neighbour is a genuine Boolean hole, it is occupied by an interior blocker
which resolves the hard residual edge, or it is occupied strictly to the
right of the upper endpoint. -/
theorem safeFlip_hole_or_resolves_or_after_upper
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V} {c : Fin n}
    (huv : u < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v)
    (hcOutU :
      c ∈ outgoingRetained
        (standardResidualColoring D n hwidth) u)
    (hcInactiveV :
      c ∉ retainedActive
        (standardResidualColoring D n hwidth) v) :
    (¬ ∃ w : V,
      (fun d => retainedBit
        (standardResidualColoring D n hwidth) w d) =
        flippedRetainedCode
          (standardResidualColoring D n hwidth) u c)
    ∨
    (∃ w : V,
      u < w ∧ w < v ∧
      IsResidual
        (standardResidualColoring D n hwidth) w v ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) w v)
    ∨
    (∃ w : V,
      v < w ∧
      (fun d => retainedBit
        (standardResidualColoring D n hwidth) w d) =
        flippedRetainedCode
          (standardResidualColoring D n hwidth) u c) := by
  let C := standardResidualColoring D n hwidth
  by_cases hocc :
      ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c
  · obtain ⟨w, hw⟩ := hocc
    have hblock :
        RetainedNeighbourBlocker C u c w :=
      (safeFlip_occupied_iff_blocker C u w c).1 hw
    rcases safeFlip_blocker_resolves_or_after_upper
        D n hn hwidth huv hres hsame
        hcOutU hcInactiveV hblock with hinside | hright
    · exact Or.inr (Or.inl ⟨w, hinside.1, hinside.2.1,
        hinside.2.2.1, hinside.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨w, hright, hw⟩)
  · exact Or.inl hocc

#print axioms safeFlip_blocker_resolves_or_after_upper
#print axioms safeFlip_hole_or_resolves_or_after_upper

end DirectionData
end JSP000404Research
