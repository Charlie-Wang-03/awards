import JSP000404Research.MixedSupportThreeMultiplicity
import JSP000404Research.SupportThreeTransitionDichotomy
import Mathlib.Tactic

/-!
# Two non-exposed three-transition support-three minima in the mixed branch

Fix the six-point profile and one support-one minimum a.

The strict-support packing theorem says that, after top and a, three additional
strictly exposed centres are impossible.  Among the remaining four minima
therefore at most two are strictly exposed, so at least two are not.

Every n-3 centre has quotient support one, two, or three.  Support at most two
always implies strict exposure.  Hence each non-exposed remaining minimum has
support exactly three.  The support-three transition dichotomy then forces all
three positive quotient positions to be sign transitions.

Thus the mixed hard branch always contains two distinct non-top centres with

  positiveSupport = 3,
  not StrictlyExposedAt,
  transition count = 3.
-/

namespace JSP000404Research

theorem mixed_support_one_has_two_nonexposed_support_three
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top a : V)
    (hta : top ≠ a)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1) :
    ∃ b c : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      positiveSupport (centreQuotient (C b) t) = 3 ∧
      positiveSupport (centreQuotient (C c) t) = 3 ∧
      ¬ StrictlyExposedAt p b ∧
      ¬ StrictlyExposedAt p c := by
  classical
  let R : Finset V := (Finset.univ.erase top).erase a
  let E : Finset V := R.filter (StrictlyExposedAt p)
  have hRcard : R.card = 4 := by
    dsimp [R]
    have haMem :
        a ∈ (Finset.univ.erase top : Finset V) := by
      simp [hta.symm]
    rw [Finset.card_erase_of_mem haMem,
        Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
    norm_num

  have hEcard : E.card ≤ 2 := by
    by_contra hnot
    have h3 : 3 ≤ E.card := by omega
    obtain ⟨T, hTsub, hTcard⟩ :=
      Finset.exists_subset_card_eq h3
    have hTexp :
        ∀ v ∈ T, StrictlyExposedAt p v := by
      intro v hv
      exact (Finset.mem_filter.mp (hTsub hv)).2
    have hTR :
        ∀ v ∈ T, v ∈ R := by
      intro v hv
      exact (Finset.mem_filter.mp (hTsub hv)).1

    obtain ⟨b, hbT, c, hcT, hbc⟩ :=
      Finset.two_le_card.mp (by omega : 2 ≤ T.card)
    let T' := T.erase b
    have hT'card : T'.card = 2 := by
      dsimp [T']
      rw [Finset.card_erase_of_mem hbT, hTcard]
    obtain ⟨c0, hc0T', d, hdT', hc0d⟩ :=
      Finset.two_le_card.mp (by omega : 2 ≤ T'.card)
    have hc0T : c0 ∈ T := (Finset.mem_erase.mp hc0T').2
    have hdT : d ∈ T := (Finset.mem_erase.mp hdT').2
    have hbc0 : b ≠ c0 :=
      (Finset.mem_erase.mp hc0T').1.symm
    have hbd : b ≠ d :=
      (Finset.mem_erase.mp hdT').1.symm

    have hbR := hTR b hbT
    have hcR := hTR c0 hc0T
    have hdR := hTR d hdT
    have hbTop :
        b ≠ top := by
      dsimp [R] at hbR
      exact (Finset.mem_erase.mp
        (Finset.mem_erase.mp hbR).2).1
    have hcTop :
        c0 ≠ top := by
      dsimp [R] at hcR
      exact (Finset.mem_erase.mp
        (Finset.mem_erase.mp hcR).2).1
    have hdTop :
        d ≠ top := by
      dsimp [R] at hdR
      exact (Finset.mem_erase.mp
        (Finset.mem_erase.mp hdR).2).1
    have hbA :
        b ≠ a := by
      dsimp [R] at hbR
      exact (Finset.mem_erase.mp hbR).1
    have hcA :
        c0 ≠ a := by
      dsimp [R] at hcR
      exact (Finset.mem_erase.mp hcR).1
    have hdA :
        d ≠ a := by
      dsimp [R] at hdR
      exact (Finset.mem_erase.mp hdR).1

    exact no_three_additional_exposed_after_top_support_one
      hp hcap (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hta hbTop.symm hcTop.symm hdTop.symm
      hbA.symm hcA.symm hdA.symm
      hbc0 hbd hc0d
      (C top) (C a) (C b) (C c0) (C d)
      hTop (hMin a hta.symm) hsupA
      (hTexp b hbT)
      (hTexp c0 hc0T)
      (hTexp d hdT)

  let N : Finset V := R \ E
  have hEsub : E ⊆ R := Finset.filter_subset _ _
  have hNcard : 2 ≤ N.card := by
    dsimp [N]
    rw [Finset.card_sdiff hEsub, hRcard]
    omega
  obtain ⟨b, hbN, c, hcN, hbc⟩ :=
    Finset.two_le_card.mp hNcard

  have hbR : b ∈ R := (Finset.mem_sdiff.mp hbN).1
  have hcR : c ∈ R := (Finset.mem_sdiff.mp hcN).1
  have hbNotE : b ∉ E := (Finset.mem_sdiff.mp hbN).2
  have hcNotE : c ∉ E := (Finset.mem_sdiff.mp hcN).2
  have hbTop :
      b ≠ top := by
    dsimp [R] at hbR
    exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp hbR).2).1
  have hcTop :
      c ≠ top := by
    dsimp [R] at hcR
    exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp hcR).2).1
  have hbA :
      b ≠ a := by
    dsimp [R] at hbR
    exact (Finset.mem_erase.mp hbR).1
  have hcA :
      c ≠ a := by
    dsimp [R] at hcR
    exact (Finset.mem_erase.mp hcR).1
  have hbNotExp : ¬ StrictlyExposedAt p b := by
    intro h
    apply hbNotE
    dsimp [E]
    exact Finset.mem_filter.mpr ⟨hbR, h⟩
  have hcNotExp : ¬ StrictlyExposedAt p c := by
    intro h
    apply hcNotE
    dsimp [E]
    exact Finset.mem_filter.mpr ⟨hcR, h⟩

  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  have hbSup3 :
      positiveSupport (centreQuotient (C b) t) = 3 := by
    rcases concrete_deficit_three_structure
        (C b) (by omega : 4 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht (hMin b hbTop)
      with h1 | h2 | h3
    · exfalso
      apply hbNotExp
      exact strictlyExposedAt_of_positiveSupport_le_two
        hp hcap htpos htone hlam b (C b)
        (by rw [h1.1]; omega)
    · exfalso
      apply hbNotExp
      exact strictlyExposedAt_of_positiveSupport_le_two
        hp hcap htpos htone hlam b (C b)
        (by rw [h2.1])
    · exact h3.1

  have hcSup3 :
      positiveSupport (centreQuotient (C c) t) = 3 := by
    rcases concrete_deficit_three_structure
        (C c) (by omega : 4 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht (hMin c hcTop)
      with h1 | h2 | h3
    · exfalso
      apply hcNotExp
      exact strictlyExposedAt_of_positiveSupport_le_two
        hp hcap htpos htone hlam c (C c)
        (by rw [h1.1]; omega)
    · exfalso
      apply hcNotExp
      exact strictlyExposedAt_of_positiveSupport_le_two
        hp hcap htpos htone hlam c (C c)
        (by rw [h2.1])
    · exact h3.1

  exact ⟨b,c,hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,hbNotExp,hcNotExp⟩

/-- Transition-strengthened form: the two forced non-exposed support-three
centres each use all three positive quotient positions as sign transitions. -/
theorem mixed_support_one_has_two_three_transition_centres
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top a : V)
    (hta : top ≠ a)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1) :
    ∃ b c : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      positiveSupport (centreQuotient (C b) t) = 3 ∧
      positiveSupport (centreQuotient (C c) t) = 3 ∧
      (∃ first rest,
        (C b).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp b first)
          (liftedCentreSignPath hp b first rest) = 3) ∧
      (∃ first rest,
        (C c).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp c first)
          (liftedCentreSignPath hp c first rest) = 3) := by
  obtain ⟨b,c,hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,hbNotExp,hcNotExp⟩ :=
    mixed_support_one_has_two_nonexposed_support_three
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨fb,rb,hbrays,hbtrans⟩ :=
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap htpos htone hlam
      b (C b) hbSup3 hbNotExp
  obtain ⟨fc,rc,hcrays,hctrans⟩ :=
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap htpos htone hlam
      c (C c) hcSup3 hcNotExp
  exact ⟨b,c,hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,
    ⟨fb,rb,hbrays,hbtrans⟩,
    ⟨fc,rc,hcrays,hctrans⟩⟩

#print axioms mixed_support_one_has_two_nonexposed_support_three
#print axioms mixed_support_one_has_two_three_transition_centres

end JSP000404Research
