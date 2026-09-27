import JSP000404Research.CutSaturatedEndpointDichotomy
import JSP000404Research.CutCentreTransitionPath
import Mathlib.Tactic

/-!
# Pulling an arbitrary-cut zero-unit step back to actual rays

A HasZeroQuotientUnitStep witness in the cut-sorted normalized value list is
an adjacent pair of rays whose occupied unit bands differ by one while the
normalized projective gap itself still has floor zero.

This file recovers those actual rays.  Because every cut-sign change costs at
least one normalized Sendov unit, a gap of floor zero cannot change the
cut-adjusted sign.  Thus every unsafe saturated endpoint found by
CutSaturatedEndpointDichotomy produces two concrete same-sign rays in
consecutive cut bands separated by less than one cap unit.
-/

namespace JSP000404Research

def HasZeroQuotientUnitCutRayStepFrom
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V) :
    OtherVertex i → List (OtherVertex i) → Prop
  | _, [] => False
  | j, k :: ks =>
      (
        Nat.floor (cutNormalizedRayTheta hp t c i k) =
            Nat.floor (cutNormalizedRayTheta hp t c i j) + 1
        ∧
        Nat.floor
          (cutNormalizedRayTheta hp t c i k -
            cutNormalizedRayTheta hp t c i j) = 0
      )
      ∨
      HasZeroQuotientUnitCutRayStepFrom hp t c i k ks

@[simp] theorem hasZeroQuotientUnitCutRayStepFrom_nil
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V) (j : OtherVertex i) :
    ¬ HasZeroQuotientUnitCutRayStepFrom hp t c i j [] := by
  simp [HasZeroQuotientUnitCutRayStepFrom]

@[simp] theorem hasZeroQuotientUnitCutRayStepFrom_cons
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V)
    (j k : OtherVertex i)
    (ks : List (OtherVertex i)) :
    HasZeroQuotientUnitCutRayStepFrom hp t c i j (k :: ks) ↔
      (
        Nat.floor (cutNormalizedRayTheta hp t c i k) =
            Nat.floor (cutNormalizedRayTheta hp t c i j) + 1
        ∧
        Nat.floor
          (cutNormalizedRayTheta hp t c i k -
            cutNormalizedRayTheta hp t c i j) = 0
      )
      ∨
      HasZeroQuotientUnitCutRayStepFrom hp t c i k ks := by
  rfl

theorem hasZeroQuotientUnitStep_map_cut_iff_rayStep
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (i : V)
    (j : OtherVertex i)
    (js : List (OtherVertex i)) :
    HasZeroQuotientUnitStep
        (cutNormalizedRayTheta hp t c i j)
        (js.map (cutNormalizedRayTheta hp t c i))
      ↔
    HasZeroQuotientUnitCutRayStepFrom hp t c i j js := by
  induction js generalizing j with
  | nil =>
      simp [HasZeroQuotientUnitStep,
        HasZeroQuotientUnitCutRayStepFrom]
  | cons k ks ih =>
      simp only [List.map_cons,
        hasZeroQuotientUnitStep_cons,
        hasZeroQuotientUnitCutRayStepFrom_cons]
      rw [ih]

/-- A cut-sorted zero-unit-step value witness gives an actual adjacent pair of
rays carrying exactly that step. -/
theorem exists_cutRay_pair_of_zeroUnitStep
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (ht0 : 0 ≤ t)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hstep : HasZeroQuotientUnitStep a xs) :
    ∃ j k : OtherVertex i,
      j ∈ R.rays ∧
      k ∈ R.rays ∧
      cutNormalizedRayTheta hp t c i j ≤
        cutNormalizedRayTheta hp t c i k ∧
      Nat.floor (cutNormalizedRayTheta hp t c i k) =
        Nat.floor (cutNormalizedRayTheta hp t c i j) + 1 ∧
      Nat.floor
        (cutNormalizedRayTheta hp t c i k -
          cutNormalizedRayTheta hp t c i j) = 0 := by
  cases hrays : R.rays with
  | nil =>
      exact False.elim (R.nonempty hrays)
  | cons j js =>
      have hvalues' :
          R.normalizedValues t =
            cutNormalizedRayTheta hp t c i j ::
              js.map (cutNormalizedRayTheta hp t c i) := by
        simp [CentreCutRayCycle.normalizedValues, hrays]
      have hcons :
          a :: xs =
            cutNormalizedRayTheta hp t c i j ::
              js.map (cutNormalizedRayTheta hp t c i) := by
        rw [← hvalues, hvalues']
      have ha :
          a = cutNormalizedRayTheta hp t c i j :=
        (List.cons.inj hcons).1
      have hxs :
          xs = js.map (cutNormalizedRayTheta hp t c i) :=
        (List.cons.inj hcons).2
      subst a
      subst xs
      have hrayStep :
          HasZeroQuotientUnitCutRayStepFrom hp t c i j js :=
        (hasZeroQuotientUnitStep_map_cut_iff_rayStep
          hp t c i j js).1 hstep
      have hsorted :
          (j :: js).Pairwise
            (fun x y =>
              cutNormalizedRayTheta hp t c i x ≤
                cutNormalizedRayTheta hp t c i y) := by
        have h :=
          R.normalizedValues_pairwise ht0
        simpa [CentreCutRayCycle.normalizedValues, hrays] using h
      induction js generalizing j with
      | nil =>
          simp [HasZeroQuotientUnitCutRayStepFrom] at hrayStep
      | cons k ks ih =>
          have hp0 := List.pairwise_cons.mp hsorted
          have hjk :
              cutNormalizedRayTheta hp t c i j ≤
                cutNormalizedRayTheta hp t c i k :=
            hp0.1 k (by simp)
          rw [hasZeroQuotientUnitCutRayStepFrom_cons] at hrayStep
          rcases hrayStep with hhead | htail
          · exact ⟨j, k, by simp [hrays], by simp [hrays],
              hjk, hhead.1, hhead.2⟩
          · obtain ⟨u, v, hu, hv, huv,
              hfloor, hzero⟩ :=
              ih k hp0.2 htail
            exact ⟨u, v,
              by simpa [hrays] using hu,
              by simpa [hrays] using hv,
              huv, hfloor, hzero⟩

/-- In the genuine positive Sendov scale, a zero-quotient unit step cannot
change the adjusted cut sign. -/
theorem exists_sameSign_cutRay_pair_of_zeroUnitStep
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hstep : HasZeroQuotientUnitStep a xs) :
    ∃ j k : OtherVertex i,
      j ≠ k ∧
      Nat.floor (cutNormalizedRayTheta hp t c i k) =
        Nat.floor (cutNormalizedRayTheta hp t c i j) + 1 ∧
      Nat.floor
        (cutNormalizedRayTheta hp t c i k -
          cutNormalizedRayTheta hp t c i j) = 0 ∧
      cutNormalizedRayTheta hp t c i j ≤
        cutNormalizedRayTheta hp t c i k ∧
      cutRaySign hp c i j =
        cutRaySign hp c i k := by
  obtain ⟨j, k, _hj, _hk, hjkLe,
      hfloor, hzero⟩ :=
    R.exists_cutRay_pair_of_zeroUnitStep
      ht.le hvalues hstep
  have hjk : j ≠ k := by
    intro heq
    subst k
    omega
  have hgap0 :
      0 ≤
        cutNormalizedRayTheta hp t c i k -
          cutNormalizedRayTheta hp t c i j :=
    sub_nonneg.mpr hjkLe
  have hgapLt :
      cutNormalizedRayTheta hp t c i k -
          cutNormalizedRayTheta hp t c i j < 1 := by
    have h :=
      Nat.lt_floor_add_one
        (cutNormalizedRayTheta hp t c i k -
          cutNormalizedRayTheta hp t c i j)
    rw [hzero] at h
    norm_num at h ⊢
    exact h
  have hthetaLe :
      cutRayTheta hp c i j ≤
        cutRayTheta hp c i k := by
    unfold cutNormalizedRayTheta at hjkLe
    have hcoef : 0 < t / Real.pi :=
      div_pos ht Real.pi_pos
    have hjkLe' :
        (t / Real.pi) * cutRayTheta hp c i j ≤
          (t / Real.pi) * cutRayTheta hp c i k := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hjkLe
    exact (mul_le_mul_left hcoef).mp hjkLe'
  have hsign :
      cutRaySign hp c i j =
        cutRaySign hp c i k := by
    by_contra hne
    have hcost :=
      one_le_t_mul_cutRay_gap_of_sign_ne
        hp hcap ht hlam hc0 hcpi i
        hjk hthetaLe hne
    have hcoordEq :
        t * ((cutRayTheta hp c i k -
            cutRayTheta hp c i j) / Real.pi)
          =
        cutNormalizedRayTheta hp t c i k -
          cutNormalizedRayTheta hp t c i j := by
      unfold cutNormalizedRayTheta
      ring
    rw [hcoordEq] at hcost
    linarith
  exact ⟨j, k, hjk, hfloor, hzero,
    hjkLe, hsign⟩

#print axioms exists_cutRay_pair_of_zeroUnitStep
#print axioms exists_sameSign_cutRay_pair_of_zeroUnitStep

end JSP000404Research
