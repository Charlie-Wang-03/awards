
import JSP000404Research.StandardResidualSafeHardDescent
import JSP000404Research.ResidualBlockerDensity
import Mathlib.Tactic

/-!
# Exact hard same-code pair: interior resolution or right-side density

Let u<v be a standard residual same-retained pair with no common inactive
coordinate.  Assume the upper endpoint v is exact in the projected budget,

  exponent(v) = projectedFree(v).

The safe-target set is exactly retainedInactive(v).  Every safe target is an
outgoing retained colour of u, so choose one witness edge u--w_c.

If any chosen witness lies inside (u,v), the hard-pair split turns w_c--v into
a residual edge whose endpoints are already retained-separated.

Otherwise every chosen witness lies strictly to the right of v.  Different
safe colours give different witness vertices, because the edge u--w has only
one colour.

Hence either the hard collision resolves internally, or

  exponent(v)
    = card(retainedInactive(v))
    <= #{w | v<w}.

This is the safe-target analogue of the blocker-density theorem.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem exact_safe_hard_resolves_or_upper_exponent_le_right_count
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    (exponent : V → ℕ)
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
    (hvExact :
      ExactProjectedBudget
        (standardResidualColoring D n hwidth)
        exponent v) :
    (∃ w : V,
      u < w ∧ w < v ∧
      IsResidual
        (standardResidualColoring D n hwidth) w v ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) w v)
    ∨
    exponent v ≤ (strictRightVertices v).card := by
  classical
  let C := standardResidualColoring D n hwidth
  by_cases hresolve :
      ∃ w : V,
        u < w ∧ w < v ∧
        IsResidual C w v ∧
        RetainedSeparated C w v
  · exact Or.inl hresolve
  · right
    have hset :
        (Finset.univ \ residualForbidden C u v) =
          retainedInactive C v :=
      safeTargetSet_eq_retainedInactive_upper_of_sameRetained
        C hsame
    let chooseWitness :
        {c : Fin n // c ∈ retainedInactive C v} → V :=
      fun c =>
        Classical.choose
          ((mem_outgoingRetained_iff C u c.1).1
            (by
              have hcSafeSet :
                  c.1 ∈ Finset.univ \ residualForbidden C u v := by
                rw [hset]
                exact c.2
              have hcSafe :
                  c.1 ∉ residualForbidden C u v := by
                exact (Finset.mem_sdiff.mp hcSafeSet).2
              exact
                (safe_hard_colour_outgoing_lower_inactive_upper
                  D n hwidth hsame hnoCommon hcSafe).1))
    have hchoose :
        ∀ c : {c : Fin n // c ∈ retainedInactive C v},
          u < chooseWitness c ∧
          C.color u (chooseWitness c) = c.1.castSucc := by
      intro c
      exact Classical.choose_spec
        ((mem_outgoingRetained_iff C u c.1).1
          (by
            have hcSafeSet :
                c.1 ∈ Finset.univ \ residualForbidden C u v := by
              rw [hset]
              exact c.2
            have hcSafe :
                c.1 ∉ residualForbidden C u v :=
              (Finset.mem_sdiff.mp hcSafeSet).2
            exact
              (safe_hard_colour_outgoing_lower_inactive_upper
                D n hwidth hsame hnoCommon hcSafe).1))
    have hright :
        ∀ c : {c : Fin n // c ∈ retainedInactive C v},
          v < chooseWitness c := by
      intro c
      rcases lt_trichotomy (chooseWitness c) v with hwv | heq | hvw
      · have hresolved :=
          safe_hard_interior_witness_resolves
            D n hn hwidth
            (hchoose c).1 hwv hres hsame
            (hchoose c).2
        exact False.elim
          (hresolve
            ⟨chooseWitness c, (hchoose c).1, hwv,
              hresolved.1, hresolved.2⟩)
      · subst v
        have hret :
            (C.color u (chooseWitness c)).val < n := by
          rw [(hchoose c).2]
          simp
        exact False.elim (hres hret)
      · exact hvw
    let f :
        {c : Fin n // c ∈ retainedInactive C v} →
          {w : V // w ∈ strictRightVertices v} :=
      fun c => ⟨chooseWitness c,
        (mem_strictRightVertices v (chooseWitness c)).2
          (hright c)⟩
    have hf : Function.Injective f := by
      intro c d hcd
      apply Subtype.ext
      have hw :
          chooseWitness c = chooseWitness d :=
        congrArg Subtype.val hcd
      have hcol :
          c.1.castSucc = d.1.castSucc := by
        calc
          c.1.castSucc = C.color u (chooseWitness c) :=
            (hchoose c).2.symm
          _ = C.color u (chooseWitness d) := by rw [hw]
          _ = d.1.castSucc := (hchoose d).2
      exact Fin.ext (congrArg Fin.val hcol)
    have hcard :
        (retainedInactive C v).card ≤
          (strictRightVertices v).card := by
      have h :=
        Fintype.card_le_of_injective f hf
      simpa only [Fintype.card_coe] using h
    have hfree :
        projectedFree C v =
          (retainedInactive C v).card := by
      unfold projectedFree
      rw [retainedInactive_card]
    rw [hvExact, hfree]
    exact hcard

#print axioms exact_safe_hard_resolves_or_upper_exponent_le_right_count

end DirectionData
end JSP000404Research
