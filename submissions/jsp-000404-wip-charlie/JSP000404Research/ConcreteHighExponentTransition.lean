import JSP000404Research.CentreSignPath
import JSP000404Research.CentreExponent
import Mathlib.Tactic

/-!
# Concrete high-exponent transition gap

The abstract CentreExponent theorem previously required two geometric inputs:

* sign changes only across positive quotient gaps;
* antiperiodicity of the lifted sign path.

CentreSignPath now proves both for the actual canonical projective ray cycle.
This file removes those abstract hypotheses.

In the lower Sendov branch, any concrete centre with exponent k >= n-2
therefore has exactly one sign transition, and that transition is carried by
a positive quotient gap of its actual projective gap cycle.
-/

namespace JSP000404Research

/-- The Sendov scale t=n+delta is positive and at least one when n>=1 and
delta>=0. -/
theorem sendov_scale_one_le
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta) :
    1 ≤ t := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [ht]
  linarith

theorem sendov_scale_pos
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta) :
    0 < t :=
  lt_of_lt_of_le zero_lt_one
    (sendov_scale_one_le hn hdelta0 ht)

/-- Fully concrete high-exponent transition theorem. -/
theorem concrete_centre_large_exponent_has_positive_transition_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hlarge : n - 2 ≤ centreExponent C t) :
    ∃ first : OtherVertex i,
      ∃ rest : List (OtherVertex i),
      ∃ pre post : List ℕ, ∃ qe : ℕ,
        C.rays = first :: rest ∧
        qe ≠ 0 ∧
        quotientList t C.gaps =
          pre ++ qe :: post ∧
        liftedCentreSignPath hp i first rest =
          List.replicate pre.length (raySignAt hp i first) ++
            List.replicate (post.length + 1)
              (!raySignAt hp i first) := by
  obtain ⟨first, rest, hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases h : C.rays with
    | nil =>
        exact False.elim (C.nonempty h)
    | cons first rest =>
        exact ⟨first, rest, h⟩
  have ht1 : 1 ≤ t :=
    sendov_scale_one_le hn hdelta0 ht
  have htpos : 0 < t :=
    lt_of_lt_of_le zero_lt_one ht1
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap htpos ht1 hlam i C first rest hrays
  have hlast :
      boolLastFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
        =
      !raySignAt hp i first :=
    liftedCentreSignPath_last_not hp i first rest
  obtain ⟨pre, post, qe, hqe, hq, hs⟩ :=
    centre_large_exponent_has_positive_transition_gap
      C n delta t hn hdelta0 hdelta1 ht hlarge
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      hchanges hlast
  exact ⟨first, rest, pre, post, qe,
    hrays, hqe, hq, hs⟩

#print axioms sendov_scale_one_le
#print axioms concrete_centre_large_exponent_has_positive_transition_gap

end JSP000404Research
