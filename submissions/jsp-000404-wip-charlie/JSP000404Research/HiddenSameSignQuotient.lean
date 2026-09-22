import JSP000404Research.FourCentreTransitionCases
import JSP000404Research.UniqueTransitionGap
import Mathlib.Tactic

/-!
# The hidden support-two quotient occurs on a same-sign step

The unique-transition decomposition has aligned form

  quotients = pre ++ qe :: post

  signs =
    replicate pre.length a ++
      replicate (post.length+1) (!a).

Thus qe is the only quotient step whose endpoint signs differ.  Any other
quotient value occurring in the list occurs on a same-sign step.

For a deficit-two/support-two centre with qe=1, the existing arithmetic theorem
gives a hidden quotient n-1.  Since n>=3, n-1 != 1, so that hidden quotient is
necessarily carried by a same-sign adjacent ray step.

This is the combinatorial bridge needed before applying
triangle_quotient_credit_transfer in arbitrary cardinality.
-/

namespace JSP000404Research

/-- A quotient value occurs at an aligned step whose two endpoint signs agree. -/
def SameSignQuotientOccurs (q : ℕ) :
    Bool → List Bool → List ℕ → Prop
  | _, [], [] => False
  | a, b :: bs, r :: rs =>
      (r = q ∧ a = b) ∨ SameSignQuotientOccurs q b bs rs
  | _, _, _ => False

theorem sameSignQuotientOccurs_replicate
    (q : ℕ) (a : Bool) (qs : List ℕ)
    (hq : q ∈ qs) :
    SameSignQuotientOccurs q a
      (List.replicate qs.length a) qs := by
  induction qs generalizing a with
  | nil =>
      simp at hq
  | cons r rs ih =>
      rw [List.mem_cons] at hq
      simp only [List.length_cons, List.replicate_succ,
        SameSignQuotientOccurs]
      rcases hq with rfl | hq
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (ih a hq)

theorem sameSignQuotientOccurs_of_two_blocks
    (a : Bool)
    (pre post : List ℕ)
    (qe q : ℕ)
    (hqne : q ≠ qe)
    (hqmem : q ∈ pre ++ qe :: post) :
    SameSignQuotientOccurs q a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ qe :: post) := by
  induction pre generalizing a with
  | nil =>
      simp only [List.length_nil, List.replicate_zero,
        List.nil_append] at hqmem ⊢
      rw [List.mem_cons] at hqmem
      rcases hqmem with hbad | hpost
      · exact False.elim (hqne hbad)
      · rw [List.replicate_succ]
        simp only [SameSignQuotientOccurs]
        right
        exact sameSignQuotientOccurs_replicate
          q (!a) post hpost
  | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, List.mem_cons] at hqmem ⊢
      rcases hqmem with hr | hrest
      · left
        exact ⟨hr.symm, rfl⟩
      · right
        exact ih a hrest

theorem hidden_n_sub_one_sameSignOccurrence
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (pre post : List ℕ) (qe n : ℕ)
    (hn : 3 ≤ n)
    (hqe : qe = 1)
    (hq :
      qs = pre ++ qe :: post)
    (hsigns :
      signs =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a))
    (hhidden : n - 1 ∈ qs) :
    SameSignQuotientOccurs (n - 1) a signs qs := by
  rw [hq, hsigns]
  apply sameSignQuotientOccurs_of_two_blocks
  · rw [hqe]
    omega
  · rw [← hq]
    exact hhidden

/-- Concrete support-two specialization using the already-proved hidden
n-1 quotient theorem. -/
theorem support_two_unit_transition_hidden_sameSign
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hqe0 : qe ≠ 0)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first))
    (hqeOne : qe = 1) :
    SameSignQuotientOccurs (n - 1)
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨H, hHqe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos i C first rest pre post qe
      hrays hqe0 hq hsignLift
  have hhidden :
      n - 1 ∈ quotientList t C.gaps := by
    apply mixed_support_two_has_hidden_n_sub_one
      C H hn hdelta0 hdeltaHalf ht hexp hsupport
    rw [hHqe, hqeOne]
  exact hidden_n_sub_one_sameSignOccurrence
    (raySignAt hp i first)
    (liftedCentreSignPath hp i first rest)
    (quotientList t C.gaps)
    pre post qe n hn hqeOne hq hsignLift hhidden

#print axioms sameSignQuotientOccurs_of_two_blocks
#print axioms hidden_n_sub_one_sameSignOccurrence
#print axioms support_two_unit_transition_hidden_sameSign

end JSP000404Research
