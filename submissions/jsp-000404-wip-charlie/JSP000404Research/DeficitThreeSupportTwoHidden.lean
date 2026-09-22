import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.GeneralNontransitionPayment
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Hidden quotient in a support-two deficit-three centre

For a quotient list with exactly two positive positions, cut at the unique
sign-transition position

  qs = pre ++ qe :: post.

The cyclic complement post ++ pre has positive support exactly one.  If the
full quotient sum is N, that unique other positive position has value N-qe.

Crucially, this is a positional statement: the hidden position lies in pre or
post, so it is a same-sign step even when its numerical value happens to equal
qe.

For exact deficit three / support two, N=n-1.  Hence a unit transition qe=1
forces a same-sign quotient n-2, which pays a genuine Euclidean angle of at
least (n-2)*lambda.
-/

namespace JSP000404Research

theorem hidden_sum_sub_qe_mem_internal_of_positiveCount_two
    (pre post : List ℕ) (qe N : ℕ)
    (hqe0 : qe ≠ 0)
    (hsupport :
      listPositiveCount (pre ++ qe :: post) = 2)
    (hsum :
      (pre ++ qe :: post).sum = N) :
    0 < N - qe ∧
      N - qe ∈ post ++ pre := by
  have hinternalSupport :
      listPositiveCount (post ++ pre) = 1 := by
    rw [listPositiveCount_append] at hsupport ⊢
    simp [listPositiveCount, hqe0] at hsupport
    omega
  have hinternalSum :
      (post ++ pre).sum = N - qe := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil,
      add_zero] at hsum ⊢
    omega
  have hposSum :
      0 < (post ++ pre).sum :=
    list_sum_pos_of_positiveCount_pos
      (post ++ pre) (by omega)
  have hpos : 0 < N - qe := by
    rwa [hinternalSum] at hposSum
  have hmemSum :
      (post ++ pre).sum ∈ post ++ pre :=
    list_sum_mem_of_positiveCount_one
      (post ++ pre) hinternalSupport hposSum
  rw [hinternalSum] at hmemSum
  exact ⟨hpos, hmemSum⟩

/-- Any occurrence in pre or post, i.e. outside the distinguished transition
position, is carried by a same-sign step in the two-block sign shape. -/
theorem sameSignQuotientOccurs_of_mem_outside_transition
    (q qe : ℕ) (a : Bool)
    (pre post : List ℕ)
    (hmem : q ∈ pre ∨ q ∈ post) :
    SameSignQuotientOccurs q a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ qe :: post) := by
  induction pre generalizing a with
  | nil =>
      rcases hmem with hpre | hpost
      · simp at hpre
      · simp only [List.length_nil, List.replicate_zero,
          List.nil_append, List.replicate_succ]
        simp only [SameSignQuotientOccurs]
        right
        exact sameSignQuotientOccurs_replicate
          q (!a) post hpost
  | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, SameSignQuotientOccurs]
      rcases hmem with hpre | hpost
      · simp only [List.mem_cons] at hpre
        rcases hpre with hr | hrs
        · left
          exact ⟨hr.symm, rfl⟩
        · right
          exact ih a (Or.inl hrs)
      · right
        exact ih a (Or.inr hpost)

/-- Exact support-two transition decomposition: the unique other positive
position equals totalSum-qe and is same-sign. -/
theorem support_two_transition_hidden_sameSign
    (a : Bool)
    (signs : List Bool)
    (pre post : List ℕ)
    (qe N : ℕ)
    (hqe0 : qe ≠ 0)
    (hsigns :
      signs =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a))
    (hsupport :
      listPositiveCount (pre ++ qe :: post) = 2)
    (hsum :
      (pre ++ qe :: post).sum = N) :
    0 < N - qe ∧
      SameSignQuotientOccurs (N - qe) a signs
        (pre ++ qe :: post) := by
  obtain ⟨hpos, hmemInternal⟩ :=
    hidden_sum_sub_qe_mem_internal_of_positiveCount_two
      pre post qe N hqe0 hsupport hsum
  have hmemOutside :
      N - qe ∈ pre ∨ N - qe ∈ post := by
    rw [List.mem_append] at hmemInternal
    rcases hmemInternal with hpost | hpre
    · exact Or.inr hpost
    · exact Or.inl hpre
  rw [hsigns]
  exact ⟨hpos,
    sameSignQuotientOccurs_of_mem_outside_transition
      (N - qe) qe a pre post hmemOutside⟩

/-- Concrete exact deficit-three/support-two transition decomposition. -/
theorem exists_deficit_three_support_two_hidden_sameSign
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    ∃ first : OtherVertex i,
      ∃ rest : List (OtherVertex i),
      ∃ pre post : List ℕ,
      ∃ qe : ℕ,
      ∃ H : HighExponentTransitionIntervalCertificate hp t i C,
        C.rays = first :: rest ∧
        qe ≠ 0 ∧
        quotientList t C.gaps = pre ++ qe :: post ∧
        liftedCentreSignPath hp i first rest =
          List.replicate pre.length (raySignAt hp i first) ++
            List.replicate (post.length + 1)
              (!raySignAt hp i first) ∧
        H.qe = qe ∧
        0 < (n - 1) - qe ∧
        SameSignQuotientOccurs ((n - 1) - qe)
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
          (quotientList t C.gaps) := by
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨first, rest, pre, post, qe,
      hrays, hqe, hq, hsign⟩ :=
    exists_transition_decomposition_of_support_le_two
      hp hcap htpos htone hlam i C (by omega)
  obtain ⟨H, hHqe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos i C first rest pre post qe
      hrays hqe hq hsign
  have hdelta1 : delta < 1 := by linarith
  have hsumFn :=
    deficit_three_support_two_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hsumList :
      (pre ++ qe :: post).sum = n - 1 := by
    rw [← hq, ← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have hsupportList :
      listPositiveCount (pre ++ qe :: post) = 2 := by
    rw [← hq, ← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  obtain ⟨hhiddenPos, hocc0⟩ :=
    support_two_transition_hidden_sameSign
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      pre post qe (n - 1)
      hqe hsign hsupportList hsumList
  have hocc :
      SameSignQuotientOccurs ((n - 1) - qe)
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) := by
    rw [hq]
    exact hocc0
  exact ⟨first, rest, pre, post, qe, H,
    hrays, hqe, hq, hsign, hHqe,
    hhiddenPos, hocc⟩

/-- Preserved decomposition form: unit transition implies a hidden same-sign
quotient n-2 and hence a genuine angle payment (n-2)*lambda. -/
theorem deficit_three_support_two_unit_transition_hidden_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    {n : ℕ}
    (hn : 4 ≤ n)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (hrays : C.rays = first :: rest)
    (hq :
      quotientList t C.gaps = pre ++ 1 :: post)
    (hsign :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first))
    (hsupportList :
      listPositiveCount (pre ++ 1 :: post) = 2)
    (hsumList :
      (pre ++ 1 :: post).sum = n - 1) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (((n - 2 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  obtain ⟨hpos, hocc0⟩ :=
    support_two_transition_hidden_sameSign
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      pre post 1 (n - 1)
      (by decide) hsign hsupportList hsumList
  have hhidden : (n - 1) - 1 = n - 2 := by omega
  have hocc :
      SameSignQuotientOccurs (n - 2)
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) := by
    rw [hq, ← hhidden]
    exact hocc0
  exact sameSignQuotient_pays_angle
    hp htpos hlam i C first rest hrays
    (n - 2) hocc

#print axioms hidden_sum_sub_qe_mem_internal_of_positiveCount_two
#print axioms sameSignQuotientOccurs_of_mem_outside_transition
#print axioms support_two_transition_hidden_sameSign
#print axioms exists_deficit_three_support_two_hidden_sameSign
#print axioms deficit_three_support_two_unit_transition_hidden_angle

end JSP000404Research
