import JSP000404Research.ExposedSupportIntervalFinFour
import Mathlib.Tactic

/-!
# Quantitative support interval for an arbitrary strictly exposed centre

The Fin 4 proof used only one genuinely planar obstruction: three sorted
canonical rays with signs

  sigma, !sigma, sigma

cannot share a strict supporting vector.

That obstruction is cardinality-free.  For an arbitrary sorted ray list it
implies a no-return rule: once the canonical sign differs from the first sign,
it can never return to the first sign later in the sorted order.  Thus the
ordinary sign list has at most one sign change.  Appending the antiperiodic
lifted endpoint !sigma preserves the no-return property, while the endpoint
parity forces at least one transition.  Hence the lifted path changes sign
exactly once.

OneTransitionSupportInterval then gives a support interval of turn at least
lambda for every strictly exposed centre, with no Fin 4 assumption.
-/

namespace JSP000404Research

/-- Once a Boolean path leaves its initial value, it never returns. -/
def BoolNoReturnFrom (a : Bool) : List Bool → Prop
  | [] => True
  | b :: bs =>
      (b ≠ a → ∀ c ∈ bs, c ≠ a) ∧ BoolNoReturnFrom a bs

theorem bool_eq_of_ne_same
    {a b c : Bool}
    (hb : b ≠ a) (hc : c ≠ a) :
    c = b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem boolTransitionCountFrom_eq_zero_of_all_eq
    (a : Bool) (xs : List Bool)
    (hall : ∀ b ∈ xs, b = a) :
    boolTransitionCountFrom a xs = 0 := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons b bs ih =>
      have hb : b = a := hall b (by simp)
      subst b
      simp only [boolTransitionCountFrom, if_pos rfl, zero_add]
      apply ih a
      intro c hc
      exact hall c (by simp [hc])

theorem boolTransitionCountFrom_le_one_of_noReturn
    (a : Bool) (xs : List Bool)
    (h : BoolNoReturnFrom a xs) :
    boolTransitionCountFrom a xs ≤ 1 := by
  induction xs generalizing a with
  | nil =>
      simp [boolTransitionCountFrom]
  | cons b bs ih =>
      rcases h with ⟨hhead, htail⟩
      by_cases hab : b = a
      · subst b
        simp only [boolTransitionCountFrom, if_pos rfl, zero_add]
        exact ih a htail
      · have hallB : ∀ c ∈ bs, c = b := by
          intro c hc
          exact bool_eq_of_ne_same hab (hhead hab c hc)
        have hzero :
            boolTransitionCountFrom b bs = 0 :=
          boolTransitionCountFrom_eq_zero_of_all_eq b bs hallB
        simp [boolTransitionCountFrom, hab, hzero]

theorem boolNoReturnFrom_append_not
    (a : Bool) (xs : List Bool)
    (h : BoolNoReturnFrom a xs) :
    BoolNoReturnFrom a (xs ++ [!a]) := by
  induction xs with
  | nil =>
      simp [BoolNoReturnFrom]
  | cons b bs ih =>
      rcases h with ⟨hhead, htail⟩
      simp only [List.cons_append, BoolNoReturnFrom]
      constructor
      · intro hba c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hhead hba c hc
        · simp only [List.mem_singleton] at hc
          subst c
          cases a <;> simp
      · exact ih htail

/-- Strict support makes the sorted canonical sign sequence no-return relative
to the first ray's sign. -/
theorem boolNoReturn_restSigns_of_strictSupport
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b))
    (u : Plane)
    (hu : StrictSupportsAt p i u) :
    BoolNoReturnFrom
      (raySignAt hp i first)
      (rest.map (raySignAt hp i)) := by
  induction rest with
  | nil =>
      simp [BoolNoReturnFrom]
  | cons r rs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hfirstR :
          rayThetaAt hp i first ≤ rayThetaAt hp i r :=
        hpair.1 r (by simp)
      have htailPair :
          (r :: rs).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) :=
        hpair.2
      have hfirstTail :
          ∀ k ∈ rs,
            rayThetaAt hp i first ≤ rayThetaAt hp i k := by
        intro k hk
        exact hpair.1 k (by simp [hk])
      have hsortedRec :
          (first :: rs).Pairwise
            (fun a b =>
              rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
        apply List.pairwise_cons.mpr
        constructor
        · exact hfirstTail
        · exact (List.pairwise_cons.mp htailPair).2
      simp only [List.map_cons, BoolNoReturnFrom]
      constructor
      · intro hrDiff c hc
        rw [List.mem_map] at hc
        obtain ⟨k, hk, rfl⟩ := hc
        intro hkFirst
        have hrNot :
            raySignAt hp i r =
              !raySignAt hp i first := by
          cases hF : raySignAt hp i first <;>
            cases hR : raySignAt hp i r <;>
            simp_all
        have hrk :
            rayThetaAt hp i r ≤ rayThetaAt hp i k :=
          (List.pairwise_cons.mp htailPair).1 k hk
        exact no_strictSupport_of_three_alternating_sorted
          hp first r k
          hfirstR hrk hrNot hkFirst u hu
      · exact ih hsortedRec

/-- Cardinality-free version of the Fin 4 transition theorem. -/
theorem one_sign_transition_of_strictlyExposed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hExpose : StrictlyExposedAt p i) :
    ∃ first : OtherVertex i, ∃ rest : List (OtherVertex i),
      C.rays = first :: rest ∧
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 1 := by
  obtain ⟨first, rest, hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases h : C.rays with
    | nil =>
        exact False.elim (C.nonempty h)
    | cons first rest =>
        exact ⟨first, rest, h⟩
  obtain ⟨u, hu⟩ := hExpose
  have hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    rw [← hrays]
    exact C.theta_sorted
  have hnoActual :=
    boolNoReturn_restSigns_of_strictSupport
      hp first rest hsorted u hu
  have hnoLift :
      BoolNoReturnFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest) := by
    unfold liftedCentreSignPath
    exact boolNoReturnFrom_append_not
      (raySignAt hp i first)
      (rest.map (raySignAt hp i))
      hnoActual
  have hle1 :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) ≤ 1 :=
    boolTransitionCountFrom_le_one_of_noReturn
      _ _ hnoLift
  have hlast :=
    liftedCentreSignPath_last_not hp i first rest
  have hone :=
    boolTransitionCountFrom_eq_one_of_last_not_of_le_two
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      hlast (hle1.trans (by omega))
  exact ⟨first, rest, hrays, hone⟩

/-- Every strictly exposed centre under the global cap owns at least one full
lambda unit of strict-support direction arc. -/
theorem exists_supportIntervalCertificate_of_strictlyExposed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hExpose : StrictlyExposedAt p i) :
    ∃ S : SupportIntervalCertificate (p := p) i,
      lam ≤ S.turnLength := by
  obtain ⟨first, rest, hrays, htrans⟩ :=
    one_sign_transition_of_strictlyExposed
      hp C hExpose
  exact exists_supportIntervalCertificate_of_one_sign_transition
    hp hcap ht htone hlam i C first rest hrays htrans

#print axioms boolTransitionCountFrom_le_one_of_noReturn
#print axioms boolNoReturn_restSigns_of_strictSupport
#print axioms one_sign_transition_of_strictlyExposed
#print axioms exists_supportIntervalCertificate_of_strictlyExposed

end JSP000404Research
