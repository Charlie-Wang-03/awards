
import JSP000404Research.StandardResidualHardPairSplit
import JSP000404Research.ResidualSameCodeUnsafeZero
import Mathlib.Tactic

/-!
# Safe hard residual pairs: interior resolution or strict band descent

Let C be the standard (n+1)-band colouring of DirectionData and let u<v be a
residual same-retained pair.

Assume there is no retained coordinate inactive at both endpoints.  Then every
safe target colour is exactly an outgoing colour of u which is inactive at v.

Choose a witness edge u--w in that safe retained colour c.

There are only two cases.

* u<w<v.  Since u--v is residual while u--w is retained, the exact residual
  XOR for an interior vertex forces w--v to be residual.  The hard outer pair
  theorem simultaneously says w and v are retained-separated.  Thus the new
  residual edge is no longer hard.

* v<w.  Betweenness places value(v,w) below value(u,w)<c+1.  Since c is
  inactive at v, the edge v--w cannot itself have colour c.  Therefore its
  standard retained band index is strictly smaller than c.

So a safe hard pair either resolves to a non-hard residual child inside the
interval, or creates a strict natural-number descent in the retained band
index beyond the upper endpoint.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem safe_hard_colour_outgoing_lower_inactive_upper
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v)
    (hnoCommon :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive
          (standardResidualColoring D n hwidth) u ∧
        c ∉ retainedActive
          (standardResidualColoring D n hwidth) v)
    {c : Fin n}
    (hsafe :
      c ∉ residualForbidden
        (standardResidualColoring D n hwidth) u v) :
    c ∈ outgoingRetained
        (standardResidualColoring D n hwidth) u ∧
      c ∉ retainedActive
        (standardResidualColoring D n hwidth) v := by
  let C := standardResidualColoring D n hwidth
  have hcSet :
      c ∈ (Finset.univ \ residualForbidden C u v) := by
    simp [hsafe]
  have hset :=
    safeTargetSet_eq_outgoingLower_sdiff_outgoingUpper
      C hsame hnoCommon
  rw [hset] at hcSet
  have hcData := Finset.mem_sdiff.mp hcSet
  refine ⟨hcData.1, ?_⟩
  rw [retainedActive_eq_incoming_union_outgoing C v]
  intro hactive
  rw [Finset.mem_union] at hactive
  rcases hactive with hIn | hOut
  · have hInU :
        c ∈ incomingRetained C u := by
      rw [incomingRetained_eq_of_sameRetained C hsame]
      exact hIn
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C u)
      hInU hcData.1
  · exact hcData.2 hOut

/-- A safe colour witness lying inside the hard residual interval produces a
residual child which is already retained-separated. -/
theorem safe_hard_interior_witness_resolves
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u w v : V}
    (huw : u < w) (hwv : w < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v)
    {c : Fin n}
    (hcol :
      (standardResidualColoring D n hwidth).color u w =
        c.castSucc) :
    IsResidual
        (standardResidualColoring D n hwidth) w v ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) w v := by
  let C := standardResidualColoring D n hwidth
  have hretUW :
      (C.color u w).val < n := by
    rw [hcol]
    simp
  have hnotResUW : ¬ IsResidual C u w := hretUW
  have hxor :=
    standardResidual_inner_xor
      D n hwidth huw hwv hres
  have hresWV : IsResidual C w v := by
    rcases hxor with hleft | hright
    · exact False.elim (hnotResUW hleft.1)
    · exact hright.2
  have hsep :=
    standardResidual_hardPair_interior_separated_both
      D n hn hwidth huw hwv hres hsame
  exact ⟨hresWV, hsep.2⟩

/-- If the safe-colour witness lies beyond the upper endpoint, the next edge
drops to a strictly smaller retained band. -/
theorem safe_hard_outer_witness_strict_band_descent
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u v w : V}
    (huv : u < v) (hvw : v < w)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    {c : Fin n}
    (hcolUW :
      (standardResidualColoring D n hwidth).color u w =
        c.castSucc)
    (hcInactiveV :
      c ∉ retainedActive
        (standardResidualColoring D n hwidth) v) :
    ((standardResidualColoring D n hwidth).color v w).val < c.val := by
  let C := standardResidualColoring D n hwidth
  have huw : u < w := huv.trans hvw
  have hbandUW :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      hwidth huw c.castSucc).1 hcolUW
  have hresLower :
      (n : ℝ) ≤ D.value u v :=
    standardResidual_value_ge_n
      D n hwidth huv hres
  have hcN :
      (c : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast c.isLt
  have huvStrict :
      D.value u w < D.value u v := by
    linarith
  have hbetween :
      D.value v w ≤ D.value u w ∧
        D.value u w ≤ D.value u v := by
    rcases D.between huv hvw with hforward | hreverse
    · exfalso
      linarith
    · exact hreverse
  have hvwUpper :
      D.value v w < (c : ℝ) + 1 := by
    exact hbetween.1.trans_lt hbandUW.2
  have hvwBelowN :
      D.value v w < (n : ℝ) := by
    exact hvwUpper.trans_le hcN
  have hretVW :
      (C.color v w).val < n := by
    by_contra hnot
    have hhigh :
        (n : ℝ) ≤ D.value v w :=
      (standardResidual_iff_high
        D n hwidth hvw).1 hnot
    linarith
  let d : Fin n := retainedColor C v w hretVW
  have hbandVW :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      hwidth hvw d.castSucc).1 (by
        apply Fin.ext
        simp [d, retainedColor])
  have hdle : d.val ≤ c.val := by
    by_contra hnot
    have hge : c.val + 1 ≤ d.val := by omega
    have hgeR : (c : ℝ) + 1 ≤ (d : ℝ) := by
      exact_mod_cast hge
    linarith
  have hdne : d ≠ c := by
    intro hdc
    subst d
    have hcOut :
        c ∈ outgoingRetained C v := by
      apply (mem_outgoingRetained_iff C v c).2
      refine ⟨w, hvw, ?_⟩
      apply Fin.ext
      simpa [retainedColor] using hretVW
    apply hcInactiveV
    rw [retainedActive_eq_incoming_union_outgoing C v]
    exact Finset.mem_union_right _ hcOut
  have hdlt : d.val < c.val := by
    omega
  have hvalEq :
      (C.color v w).val = d.val := by
    simp [d, retainedColor]
  rw [hvalEq]
  exact hdlt

/-- Main safe-hard witness dichotomy. -/
theorem safe_hard_pair_resolves_or_descends
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v)
    (hnoCommon :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive
          (standardResidualColoring D n hwidth) u ∧
        c ∉ retainedActive
          (standardResidualColoring D n hwidth) v)
    {c : Fin n}
    (hsafe :
      c ∉ residualForbidden
        (standardResidualColoring D n hwidth) u v) :
    (∃ w : V,
      u < w ∧ w < v ∧
      IsResidual
        (standardResidualColoring D n hwidth) w v ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) w v)
    ∨
    (∃ w : V,
      v < w ∧
      ((standardResidualColoring D n hwidth).color v w).val < c.val) := by
  let C := standardResidualColoring D n hwidth
  have hcData :=
    safe_hard_colour_outgoing_lower_inactive_upper
      D n hwidth hsame hnoCommon hsafe
  obtain ⟨w, huw, hcolUW⟩ :=
    (mem_outgoingRetained_iff C u c).1 hcData.1
  rcases lt_trichotomy w v with hwv | hwEq | hvw
  · left
    have hresolved :=
      safe_hard_interior_witness_resolves
        D n hn hwidth huw hwv hres hsame hcolUW
    exact ⟨w, huw, hwv, hresolved.1, hresolved.2⟩
  · subst w
    have hret :
        (C.color u v).val < n := by
      rw [hcolUW]
      simp
    exact False.elim (hres hret)
  · right
    refine ⟨w, hvw, ?_⟩
    exact safe_hard_outer_witness_strict_band_descent
      D n hwidth huv hvw hres hcolUW hcData.2

#print axioms safe_hard_colour_outgoing_lower_inactive_upper
#print axioms safe_hard_interior_witness_resolves
#print axioms safe_hard_outer_witness_strict_band_descent
#print axioms safe_hard_pair_resolves_or_descends

end DirectionData
end JSP000404Research
