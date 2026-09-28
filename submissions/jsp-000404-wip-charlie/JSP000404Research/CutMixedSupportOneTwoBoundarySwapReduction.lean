import JSP000404Research.CutMixedSupportOneTwoBoundarySwap
import JSP000404Research.ThirdLayerTransitionPacking
import JSP000404Research.SupportThreeTransitionDichotomy
import JSP000404Research.ExposedSupportIntervalGeneral
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Global reduction of the support-(1,2) boundary-swap branch

Suppose the six-point third-layer profile contains

* top s with exponent n-1,
* a support-one minimum a,
* a support-two saturation-bad minimum b whose cut floor span is n-1.

The boundary-swap quotient rigidity forces every transition certificate at b
to have quotient 2.

Consequences.

1. No fourth centre d distinct from s,a,b can have quotient support <=2.
   ThirdLayerTransitionPacking would construct transition certificates at b,d
   both of quotient one, contradicting q_b=2.

2. No fourth centre d can be strictly exposed.  The strict-support turn lower
   bounds from s,a,b are respectively n, n-2,2 cap units, already totaling
   2n.  Any further exposed centre contributes at least one cap unit, giving
   (2n+1)lambda > 2pi because delta<1/2.

Therefore every remaining exact n-3 minimum has support exactly three, is not
strictly exposed, and hence has exactly three sign transitions.
-/

namespace JSP000404Research

theorem no_fourth_support_le_two_of_support_one_two_span_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {top a b d : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (htd : top ≠ d)
    (hab : a ≠ b)
    (had : a ≠ d)
    (hbd : b ≠ d)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1)
    (hsupD :
      positiveSupport (centreQuotient (C d) t) ≤ 2) :
    False := by
  obtain ⟨HB, HD, hHB1, _hHD1⟩ :=
    third_layer_packing_forces_two_unit_transitions
      hp hcap (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hta htb htd hab had hbd
      (C top) (C a) (C b) (C d)
      hTop hA hsupA
      (by rw [hsupB]; omega) hsupD
  have hHB2 :=
    cut_span_n_sub_one_support_two_any_transition_qe_eq_two
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hc0 hcpi hta htb hab hTop hA hsupA
      hB hsupB hBadB R hvalues hspan HB
  omega

/-- The three saturated support arcs top/support-one/support-two already consume
2n cap units, so a fourth strictly exposed point is impossible. -/
theorem no_fourth_strictlyExposed_of_support_one_two_span_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {top a b d : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (htd : top ≠ d)
    (hab : a ≠ b)
    (had : a ≠ d)
    (hbd : b ≠ d)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1)
    (hExposeD : StrictlyExposedAt p d) :
    False := by
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hdelta1 : delta < 1 := by linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  let HTop :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        top (C top) (by rw [hTop]; omega))
  obtain ⟨HA, _hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam
      a (C a) (by rw [hsupA]; omega)
  obtain ⟨HB, _hHBpos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam
      b (C b) (by rw [hsupB]; omega)
  obtain ⟨SD, hturnD⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp hcap htpos htone hlam
      (Classical.choice
        (exists_centreProjectiveCycle hp d
          ⟨⟨top, htd⟩⟩))
      hExposeD

  have hqTop : HTop.qe = n :=
    unit_deficit_transition_qe_eq_n
      (C top) HTop (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hTop
  have hqA : HA.qe = n - 2 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        (C a) HA hsupA
    rw [hA] at h
    omega
  have hqB : HB.qe = 2 :=
    cut_span_n_sub_one_support_two_any_transition_qe_eq_two
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hc0 hcpi hta htb hab hTop hA hsupA
      hB hsupB hBadB R hvalues hspan HB

  let STop : SupportIntervalCertificate (p := p) top :=
    SupportIntervalCertificate.ofHighExponent HTop
  let SA : SupportIntervalCertificate (p := p) a :=
    SupportIntervalCertificate.ofHighExponent HA
  let SB : SupportIntervalCertificate (p := p) b :=
    SupportIntervalCertificate.ofHighExponent HB

  have hturnTop :
      (n : ℝ) * lam ≤ STop.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HTop htpos hlam
    rw [hqTop] at h
    exact h
  have hturnA :
      ((n - 2 : ℕ) : ℝ) * lam ≤ SA.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HA htpos hlam
    rw [hqA] at h
    exact h
  have hturnB :
      (2 : ℝ) * lam ≤ SB.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HB htpos hlam
    rw [hqB] at h
    norm_num at h ⊢
    exact h

  let centre : Fin 4 → V := ![top,a,b,d]
  have hcentre : Function.Injective centre := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp [centre] at huv ⊢ <;>
      try { exact False.elim (hta huv) } <;>
      try { exact False.elim (htb huv) } <;>
      try { exact False.elim (htd huv) } <;>
      try { exact False.elim (hab huv) } <;>
      try { exact False.elim (had huv) } <;>
      try { exact False.elim (hbd huv) } <;>
      try { exact False.elim (hta huv.symm) } <;>
      try { exact False.elim (htb huv.symm) } <;>
      try { exact False.elim (htd huv.symm) } <;>
      try { exact False.elim (hab huv.symm) } <;>
      try { exact False.elim (had huv.symm) } <;>
      try { exact False.elim (hbd huv.symm) }

  let cert : ∀ r : Fin 4,
      SupportIntervalCertificate (p := p) (centre r) :=
    ![STop,SA,SB,SD]

  have hpack :
      (∑ r : Fin 4, (cert r).turnLength) ≤
        2 * Real.pi :=
    SupportIntervalCertificate.turnLength_sum_le_two_pi
      centre hcentre cert

  have hlower :
      (n : ℝ) * lam +
          ((n - 2 : ℕ) : ℝ) * lam +
          2 * lam + lam
        ≤
      ∑ r : Fin 4, (cert r).turnLength := by
    simpa [cert, centre, Fin.sum_univ_succ] using
      add_le_add
        (add_le_add
          (add_le_add hturnTop hturnA)
          hturnB)
        hturnD

  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 2 ≤ n))
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hncast, hpi, ht] at hpack hlower
  nlinarith

/-- A remaining exact n-3 minimum is forced into the support-three,
three-transition non-exposed branch. -/
theorem fourth_minimum_support_three_three_transitions_of_support_one_two_span
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {top a b d : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (htd : top ≠ d)
    (hab : a ≠ b)
    (had : a ≠ d)
    (hbd : b ≠ d)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hD : centreExponent (C d) t = n - 3)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1) :
    positiveSupport (centreQuotient (C d) t) = 3 ∧
    ¬ StrictlyExposedAt p d ∧
    ∃ first : OtherVertex d,
      ∃ rest : List (OtherVertex d),
        (C d).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp d first)
          (liftedCentreSignPath hp d first rest) = 3 := by
  have hsupport3 :
      positiveSupport (centreQuotient (C d) t) = 3 := by
    rcases concrete_deficit_three_structure
        (C d) (by omega : 4 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hD
      with h1 | h2 | h3
    · exfalso
      exact no_fourth_support_le_two_of_support_one_two_span_n_sub_one
        hp hcap C hn5 hdelta0 hdeltaHalf ht hlam hc0 hcpi
        hta htb htd hab had hbd hTop hA hsupA hB hsupB
        hBadB R hvalues hspan
        (by rw [h1.1]; omega)
    · exfalso
      exact no_fourth_support_le_two_of_support_one_two_span_n_sub_one
        hp hcap C hn5 hdelta0 hdeltaHalf ht hlam hc0 hcpi
        hta htb htd hab had hbd hTop hA hsupA hB hsupB
        hBadB R hvalues hspan
        (by rw [h2.1]; omega)
    · exact h3.1
  have hnotExposed :
      ¬ StrictlyExposedAt p d := by
    intro hExpose
    exact no_fourth_strictlyExposed_of_support_one_two_span_n_sub_one
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam hc0 hcpi
      hta htb htd hab had hbd hTop hA hsupA hB hsupB
      hBadB R hvalues hspan hExpose
  obtain ⟨first,rest,hrays,hthree⟩ :=
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
      (sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht)
      hlam d (C d) hsupport3 hnotExposed
  exact ⟨hsupport3,hnotExposed,
    first,rest,hrays,hthree⟩

#print axioms no_fourth_support_le_two_of_support_one_two_span_n_sub_one
#print axioms no_fourth_strictlyExposed_of_support_one_two_span_n_sub_one
#print axioms fourth_minimum_support_three_three_transitions_of_support_one_two_span

end JSP000404Research
