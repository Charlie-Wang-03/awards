import JSP000404Research.ExactWitnessTransitionPosition
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Bridging concrete transition positions to aligned sign-path occurrence

ExactWitnessTransitionPosition certifies quotient one on an actual ordinary or
wrap sign-changing gap.  TransitionQuotientOccurrence is phrased recursively
on aligned sign and quotient lists.

This file supplies the missing index/list bridge.
-/

namespace JSP000404Research

/-- Length of the ordinary consecutive quotient list. -/
theorem consecutiveRayQuotients_length
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    (consecutiveRayQuotients hp i t first rest).length =
      rest.length := by
  induction rest generalizing first with
  | nil => rfl
  | cons r rs ih =>
      simp [consecutiveRayQuotients, ih r]

/-- An ordinary indexed sign-changing ray pair gives a recursive transition
occurrence, independently of the final appended wrap step. -/
theorem transitionQuotientOccurs_of_ordinary_ray_index
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (finalSign : Bool)
    (qwrap q : ℕ)
    (m : ℕ)
    (hm : m + 1 < (first :: rest).length)
    (hq :
      Nat.floor
        (t * ((rayThetaAt hp i
              ((first :: rest).get ⟨m + 1, hm⟩) -
            rayThetaAt hp i
              ((first :: rest).get
                ⟨m, by omega⟩)) /
          Real.pi)) = q)
    (hsign :
      raySignAt hp i
          ((first :: rest).get ⟨m, by omega⟩)
        ≠
      raySignAt hp i
          ((first :: rest).get ⟨m + 1, hm⟩)) :
    TransitionQuotientOccurs q
      (raySignAt hp i first)
      (rest.map (raySignAt hp i) ++ [finalSign])
      (consecutiveRayQuotients hp i t first rest ++ [qwrap]) := by
  induction rest generalizing first m with
  | nil =>
      simp at hm
  | cons r rs ih =>
      cases m with
      | zero =>
          simp only [List.get, consecutiveRayQuotients,
            List.map_cons, List.cons_append,
            TransitionQuotientOccurs]
          left
          exact ⟨hq, hsign⟩
      | succ m =>
          have hm' :
              m + 1 < (r :: rs).length := by
            simpa using hm
          simp only [consecutiveRayQuotients,
            List.map_cons, List.cons_append,
            TransitionQuotientOccurs]
          right
          apply ih r m hm'
          · simpa using hq
          · simpa using hsign

/-- Generic final-step occurrence lemma. -/
theorem transitionQuotientOccurs_append_final
    (a finalSign : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (q : ℕ)
    (hlen : signs.length = qs.length)
    (hchange :
      boolLastFrom a signs ≠ finalSign) :
    TransitionQuotientOccurs q a
      (signs ++ [finalSign])
      (qs ++ [q]) := by
  induction signs generalizing a qs with
  | nil =>
      have hnil : qs = [] :=
        List.length_eq_zero.mp (by simpa using hlen.symm)
      subst qs
      simp only [List.nil_append, TransitionQuotientOccurs]
      left
      exact ⟨rfl, hchange⟩
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons r rs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.cons_append, TransitionQuotientOccurs]
          right
          apply ih b rs hlen
          simpa [boolLastFrom] using hchange

/-- The positional exact-witness transition certificate yields a recursive
transition occurrence of quotient one in some displayed centre sign path. -/
theorem exactWitness_unit_transition_occurs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b) :
    ∃ first : OtherVertex W.b,
      ∃ rest : List (OtherVertex W.b),
        C.rays = first :: rest
        ∧
        TransitionQuotientOccurs 1
          (raySignAt hp W.b first)
          (liftedCentreSignPath hp W.b first rest)
          (quotientList t C.gaps) := by
  have hpos :=
    exactWitness_unit_transition_position
      hp hcap hn hdelta0 ht hlam W C
  rcases hpos with hord | hwrap
  · obtain ⟨m, hm, hq, hsign⟩ := hord
    obtain ⟨first, rest, hrays⟩ :
        ∃ first rest, C.rays = first :: rest := by
      cases hR : C.rays with
      | nil =>
          exact False.elim (C.nonempty hR)
      | cons first rest =>
          exact ⟨first, rest, hR⟩
    have hm' :
        m + 1 < (first :: rest).length := by
      simpa [hrays] using hm
    have hq' :
        Nat.floor
          (t * ((rayThetaAt hp W.b
                ((first :: rest).get ⟨m + 1, hm'⟩) -
              rayThetaAt hp W.b
                ((first :: rest).get
                  ⟨m, by omega⟩)) /
            Real.pi)) = 1 := by
      simpa [hrays] using hq
    have hsign' :
        raySignAt hp W.b
            ((first :: rest).get ⟨m, by omega⟩)
          ≠
        raySignAt hp W.b
            ((first :: rest).get ⟨m + 1, hm'⟩) := by
      simpa [hrays] using hsign
    let qwrap :=
      wrapRayQuotient hp W.b t first
        (rest.getLastD first)
    have hocc :=
      transitionQuotientOccurs_of_ordinary_ray_index
        hp W.b t first rest
        (!raySignAt hp W.b first)
        qwrap 1 m hm' hq' hsign'
    refine ⟨first, rest, hrays, ?_⟩
    rw [centreQuotientList_decompose
      C t first rest hrays]
    simpa [liftedCentreSignPath, qwrap] using hocc
  · obtain ⟨first, rest, hrays, hqwrap, hsign⟩ := hwrap
    have hlen :
        (rest.map (raySignAt hp W.b)).length =
          (consecutiveRayQuotients
            hp W.b t first rest).length := by
      simp [consecutiveRayQuotients_length]
    have hlast :
        boolLastFrom
            (raySignAt hp W.b first)
            (rest.map (raySignAt hp W.b))
          =
        raySignAt hp W.b (rest.getLastD first) := by
      rw [boolLastFrom_eq_getLastD, map_getLastD]
    have hchange :
        boolLastFrom
            (raySignAt hp W.b first)
            (rest.map (raySignAt hp W.b))
          ≠
        !raySignAt hp W.b first := by
      rw [hlast]
      exact hsign
    have hocc :=
      transitionQuotientOccurs_append_final
        (raySignAt hp W.b first)
        (!raySignAt hp W.b first)
        (rest.map (raySignAt hp W.b))
        (consecutiveRayQuotients hp W.b t first rest)
        1 hlen hchange
    refine ⟨first, rest, hrays, ?_⟩
    rw [centreQuotientList_decompose
      C t first rest hrays, hqwrap]
    simpa [liftedCentreSignPath] using hocc

#print axioms transitionQuotientOccurs_of_ordinary_ray_index
#print axioms transitionQuotientOccurs_append_final
#print axioms exactWitness_unit_transition_occurs

end JSP000404Research
