import JSP000404Research.ConcreteSharpCentre
import JSP000404Research.SharpCentre
import JSP000404Research.ProjectionOrderedVertices
import Mathlib.Tactic

/-!
# Generic finite-type multiplicity of the top lower-branch exponent

TopExponentMultiplicity states the result for Fin m.  The Hall reductions use
arbitrary finite ordered index types such as ProjectionOrdered V, so record the
same theorem generically.

If Fintype.card V >= 3 and delta < 1/2, there is at most one centre with

  centreExponent = n - 1.

Each such centre is sharp by ConcreteSharpCentre. Two distinct sharp centres
plus any third distinct centre contradict TwoSharpNoThird.
-/

namespace JSP000404Research

theorem generic_topExponent_filter_card_le_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 3 ≤ Fintype.card V)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ((Finset.univ : Finset V).filter
      (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab

  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have heab : e a ≠ e b := by
    exact e.injective.ne hab
  obtain ⟨kc,hkca,hkcb⟩ :=
    Fin.exists_ne_and_ne_of_two_lt
      (e a) (e b) (by omega)
  let c : V := e.symm kc
  have hca : c ≠ a := by
    intro h
    apply hkca
    calc
      kc = e (e.symm kc) := (e.apply_symm_apply kc).symm
      _ = e c := by rfl
      _ = e a := congrArg e h
  have hcb : c ≠ b := by
    intro h
    apply hkcb
    calc
      kc = e (e.symm kc) := (e.apply_symm_apply kc).symm
      _ = e c := by rfl
      _ = e b := congrArg e h

  have hdelta1 : delta < 1 := by linarith
  have hsharpA :=
    concrete_unit_deficit_is_sharp
      hp hcap hn hdelta0 hdelta1 ht hlam
      a (C a) ha
  have hsharpB :=
    concrete_unit_deficit_is_sharp
      hp hcap hn hdelta0 hdelta1 ht hlam
      b (C b) hb

  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  exact two_sharp_no_third_small_delta
    hp hcap hdeltaHalf hlampos
    hab hca.symm hcb.symm
    hsharpA hsharpB

#print axioms generic_topExponent_filter_card_le_one


namespace ProjectionOrdered

theorem angleCap_reindexedPoint
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ}
    (hcap : AngleCap p lam) :
    AngleCap (reindexedPoint p) lam := by
  intro a b c hab hac hbc
  unfold reindexedPoint
  exact hcap
    (toOriginal a) (toOriginal b) (toOriginal c)
    (by
      intro h
      exact hab (toOriginal_injective h))
    (by
      intro h
      exact hac (toOriginal_injective h))
    (by
      intro h
      exact hbc (toOriginal_injective h))

theorem projectionOrdered_topExponent_filter_card_le_one
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ((Finset.univ : Finset (ProjectionOrdered V)).filter
      (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hcapRe :
      AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  exact generic_topExponent_filter_card_le_one
    (reindexedPoint_injective hp)
    hcapRe hcard hn hdelta0 hdeltaHalf ht hlam C

#print axioms angleCap_reindexedPoint
#print axioms projectionOrdered_topExponent_filter_card_le_one

end ProjectionOrdered
end JSP000404Research
