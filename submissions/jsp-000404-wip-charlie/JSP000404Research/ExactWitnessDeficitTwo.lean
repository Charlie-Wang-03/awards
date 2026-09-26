
import JSP000404Research.ExactWitnessCentreBound
import JSP000404Research.DeficitTwo
import JSP000404Research.SingleSupportDeficit
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Exact witness centres in the deficit-two layer are support two

The exact witness centre quotient list contains quotient 1.

If its exponent is n-2, DeficitTwo gives only two arithmetic possibilities:

* support one and quotient sum n-1;
* support two and quotient sum n.

The first case is impossible for n>=3.  With support one, the quotient equal
to 1 is the unique nonzero coordinate, so the full quotient sum is exactly
one, contradicting sum=n-1.

Hence an exact maximum-angle witness centre in the second exponent layer has

  positiveSupport = 2,
  quotient sum = n.
-/

namespace JSP000404Research

open scoped BigOperators

theorem centreQuotient_exists_eq_one_of_exactWitness
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
    ∃ e, centreQuotient C t e = 1 := by
  have hone :
      1 ∈ quotientList t C.gaps :=
    one_mem_witnessCentre_quotientList
      hp hcap hn hdelta0 ht hlam W C
  rw [← centreQuotient_ofFn C t] at hone
  simpa using hone

/-- If a finite quotient function has support one and takes the value one,
its total sum is one. -/
theorem sum_eq_one_of_positiveSupport_one_of_exists_eq_one
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hsupport : positiveSupport q = 1)
    (hone : ∃ e, q e = 1) :
    (∑ i, q i) = 1 := by
  classical
  obtain ⟨e, he⟩ := hone
  obtain ⟨u, hu, huniq⟩ :=
    existsUnique_positive_of_one_support q hsupport
  have hePos : q e ≠ 0 := by
    rw [he]
    norm_num
  have heu : e = u := huniq e hePos
  have huOne : q u = 1 := by
    rw [← heu]
    exact he
  have hrest :
      (∑ i ∈ (Finset.univ : Finset I).erase u, q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hne
    have hiu : i = u := huniq i hne
    have hiNe : i ≠ u :=
      (Finset.mem_erase.mp hi).1
    exact hiNe hiu
  have hsplit :=
    Finset.add_sum_erase
      (Finset.univ : Finset I) q (Finset.mem_univ u)
  rw [hrest, huOne] at hsplit
  simpa using hsplit.symm

theorem exactWitness_deficitTwo_support_two
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
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 2) :
    positiveSupport (centreQuotient C t) = 2 ∧
      (∑ r, centreQuotient C t r) = n := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :
      (∑ r, centreQuotient C t r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hell :
      n - floorExcess (centreQuotient C t) = 2 := by
    change n - centreExponent C t = 2
    rw [hexp]
    omega
  rcases deficit_two_structure
      (centreQuotient C t) n hn hQ hell with h1 | h2
  · have hone :=
      centreQuotient_exists_eq_one_of_exactWitness
        hp hcap hn hdelta0 ht hlam W C
    have hsumOne :=
      sum_eq_one_of_positiveSupport_one_of_exists_eq_one
        (centreQuotient C t) h1.1 hone
    rw [h1.2] at hsumOne
    omega
  · exact h2


noncomputable def positiveIndexSet
    {I : Type*} [Fintype I]
    (q : I → ℕ) : Finset I := by
  classical
  exact Finset.univ.filter fun i => q i ≠ 0

@[simp] theorem mem_positiveIndexSet
    {I : Type*} [Fintype I]
    (q : I → ℕ) (i : I) :
    i ∈ positiveIndexSet q ↔ q i ≠ 0 := by
  classical
  simp [positiveIndexSet]

theorem positiveIndexSet_card_eq_positiveSupport
    {I : Type*} [Fintype I]
    (q : I → ℕ) :
    (positiveIndexSet q).card = positiveSupport q := by
  classical
  unfold positiveIndexSet positiveSupport
  rw [Finset.card_filter]
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih]
      by_cases hqa : q a = 0 <;> simp [hqa]

/-- A support-two quotient vector containing a unit entry and having total n
has one unique other positive coordinate of value n-1. -/
theorem support_two_with_one_exact_shape
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (n : ℕ)
    (hsupport : positiveSupport q = 2)
    (hsum : (∑ i, q i) = n)
    {e : I}
    (he : q e = 1) :
    ∃ f : I,
      f ≠ e ∧
      q f = n - 1 ∧
      ∀ i : I, i ≠ e → i ≠ f → q i = 0 := by
  classical
  let P := positiveIndexSet q
  have hPcard : P.card = 2 := by
    dsimp [P]
    rw [positiveIndexSet_card_eq_positiveSupport, hsupport]
  have heP : e ∈ P := by
    dsimp [P]
    simp [he]
  obtain ⟨a, b, hab, hP⟩ :=
    Finset.card_eq_two.mp hPcard
  have heCases : e = a ∨ e = b := by
    rw [hP] at heP
    simpa using heP
  rcases heCases with hea | heb
  · let f := b
    have hfe : f ≠ e := by
      intro h
      apply hab
      rw [← hea, ← h]
    have hzero :
        ∀ i : I, i ≠ e → i ≠ f → q i = 0 := by
      intro i hie hif
      by_contra hqi
      have hiP : i ∈ P := by
        dsimp [P]
        simpa using hqi
      rw [hP] at hiP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiP
      rcases hiP with hia | hib
      · exact hie (hia.trans hea.symm)
      · exact hif (by simpa [f] using hib)
    have hsumPair :
        (∑ i, q i) = q e + q f := by
      calc
        (∑ i, q i)
            =
          q e + ∑ i ∈ (Finset.univ : Finset I).erase e, q i := by
            symm
            exact Finset.add_sum_erase
              (Finset.univ : Finset I) q (Finset.mem_univ e)
        _ = q e + q f := by
          have hfMem :
              f ∈ (Finset.univ : Finset I).erase e := by
            simp [hfe]
          rw [← Finset.add_sum_erase
              ((Finset.univ : Finset I).erase e)
              q hfMem]
          have hrest :
              (∑ i ∈ ((Finset.univ : Finset I).erase e).erase f,
                q i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hie' : i ≠ e := by
              exact (Finset.mem_erase.mp
                (Finset.mem_of_mem_erase hi)).1
            have hif' : i ≠ f :=
              (Finset.mem_erase.mp hi).1
            exact hzero i hie' hif'
          rw [hrest]
          omega
    refine ⟨f, hfe, ?_, hzero⟩
    rw [hsum, he] at hsumPair
    omega
  · let f := a
    have hfe : f ≠ e := by
      intro h
      apply hab
      rw [← h, heb]
    have hzero :
        ∀ i : I, i ≠ e → i ≠ f → q i = 0 := by
      intro i hie hif
      by_contra hqi
      have hiP : i ∈ P := by
        dsimp [P]
        simpa using hqi
      rw [hP] at hiP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiP
      rcases hiP with hia | hib
      · exact hif (by simpa [f] using hia)
      · exact hie (hib.trans heb.symm)
    have hsumPair :
        (∑ i, q i) = q e + q f := by
      calc
        (∑ i, q i)
            =
          q e + ∑ i ∈ (Finset.univ : Finset I).erase e, q i := by
            symm
            exact Finset.add_sum_erase
              (Finset.univ : Finset I) q (Finset.mem_univ e)
        _ = q e + q f := by
          have hfMem :
              f ∈ (Finset.univ : Finset I).erase e := by
            simp [hfe]
          rw [← Finset.add_sum_erase
              ((Finset.univ : Finset I).erase e)
              q hfMem]
          have hrest :
              (∑ i ∈ ((Finset.univ : Finset I).erase e).erase f,
                q i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hie' : i ≠ e := by
              exact (Finset.mem_erase.mp
                (Finset.mem_of_mem_erase hi)).1
            have hif' : i ≠ f :=
              (Finset.mem_erase.mp hi).1
            exact hzero i hie' hif'
          rw [hrest]
          omega
    refine ⟨f, hfe, ?_, hzero⟩
    rw [hsum, he] at hsumPair
    omega

/-- Exact-witness second-layer quotient shape: one coordinate equals 1, the
other positive coordinate equals n-1, and all remaining coordinates vanish. -/
theorem exactWitness_deficitTwo_exact_quotient_pair
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
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 2) :
    ∃ e f : Fin C.gaps.length,
      e ≠ f ∧
      centreQuotient C t e = 1 ∧
      centreQuotient C t f = n - 1 ∧
      ∀ i, i ≠ e → i ≠ f →
        centreQuotient C t i = 0 := by
  have hstruct :=
    exactWitness_deficitTwo_support_two
      hp hcap hn hdelta0 hdeltaHalf ht hlam W C hexp
  obtain ⟨e, he⟩ :=
    centreQuotient_exists_eq_one_of_exactWitness
      hp hcap hn hdelta0 ht hlam W C
  obtain ⟨f, hfe, hf, hzero⟩ :=
    support_two_with_one_exact_shape
      (centreQuotient C t) n
      hstruct.1 hstruct.2 he
  exact ⟨e, f, hfe.symm, he, hf, hzero⟩

#print axioms centreQuotient_exists_eq_one_of_exactWitness
#print axioms sum_eq_one_of_positiveSupport_one_of_exists_eq_one
#print axioms exactWitness_deficitTwo_support_two
#print axioms support_two_with_one_exact_shape
#print axioms exactWitness_deficitTwo_exact_quotient_pair

end JSP000404Research
