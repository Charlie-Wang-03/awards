import JSP000404Research.SupportTwoTransitionClusterBridge
import JSP000404Research.SupportThreeZeroAngleBlocks
import JSP000404Research.CyclicActualAngles
import Mathlib.Tactic

/-!
# Actual-angle narrow clusters for transition-one support-two centres

For a concrete deficit-two/support-two centre whose distinguished transition
quotient is one, the quotient cycle has shape

  pre ++ 1 :: post

and after rotating past that transition, the remaining unique positive
quotient is n-1.  Splitting there leaves two all-zero quotient blocks.

This file aligns the same cuts with the cyclic list of actual Euclidean
angles.  The total actual-angle mass of the two zero blocks is at most
delta*lambda.
-/

namespace JSP000404Research

theorem supportTwo_transition_one_has_two_narrow_angle_blocks
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    (hqe : cert.qe = 1)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    ∃ pre post leftQ rightQ : List ℕ,
    ∃ Apre Apost : List ℝ, ∃ Ae : ℝ,
    ∃ leftA rightA : List ℝ, ∃ Ah : ℝ,
      quotientList t C.gaps = pre ++ 1 :: post ∧
      cyclicRayAngles (p := p) i first rest =
        Apre ++ Ae :: Apost ∧
      pre.length = Apre.length ∧
      post.length = Apost.length ∧
      post ++ pre = leftQ ++ (n - 1) :: rightQ ∧
      Apost ++ Apre = leftA ++ Ah :: rightA ∧
      leftQ.length = leftA.length ∧
      rightQ.length = rightA.length ∧
      (∀ q ∈ leftQ, q = 0) ∧
      (∀ q ∈ rightQ, q = 0) ∧
      leftA.sum + rightA.sum ≤ delta * lam := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone : 1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨pre,post,gpre,gpost,ge,
      leftQ,rightQ,leftG,rightG,gh,
      hq,hgaps,hpreG,hpostG,
      hhiddenQ,hhiddenG,
      hleftG,hrightG,
      hleftZero,hrightZero,
      _hhiddenAlign,_hzeroWidth⟩ :=
    supportTwo_transition_one_has_two_narrow_zero_blocks
      hcap hn hdelta0 hdeltaHalf ht hlam
      C hexp hsupport cert hqe

  let As := cyclicRayAngles (p := p) i first rest
  have halignA :=
    centre_zeroQuotientAngleAligned
      hp hcap htpos htone hlam
      i C first rest hrays
  have hlenQA :
      (quotientList t C.gaps).length = As.length :=
    zeroQuotientAngleAligned_length_q_angle halignA
  have hsplitLen :
      (pre ++ 1 :: post).length = As.length := by
    rw [← hq]
    exact hlenQA
  obtain ⟨Apre,Ae,Apost,hAs,hpreA⟩ :=
    companion_decomposition_at_prefix
      pre 1 post As hsplitLen
  have hpostA :
      post.length = Apost.length := by
    have hlen := congrArg List.length hAs
    simp at hlen
    rw [hpreA] at hlen
    omega

  have hInternalLen :
      (post ++ pre).length = (Apost ++ Apre).length := by
    simp [hpreA,hpostA]
  have hHiddenLen :
      (leftQ ++ (n - 1) :: rightQ).length =
        (Apost ++ Apre).length := by
    rw [← hhiddenQ]
    exact hInternalLen
  obtain ⟨leftA,Ah,rightA,hAhidden,hleftA⟩ :=
    companion_decomposition_at_prefix
      leftQ (n - 1) rightQ (Apost ++ Apre) hHiddenLen
  have hrightA :
      rightQ.length = rightA.length := by
    have hlen := congrArg List.length hAhidden
    simp at hlen
    rw [hleftA] at hlen
    omega

  have hzeroTotal :
      listZeroAngleMass
          (quotientList t C.gaps)
          (cyclicRayAngles (p := p) i first rest)
        ≤ delta * lam :=
    centre_zeroAngleMass_le_delta_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      i C hexp hsupport first rest hrays

  have hrotMass :
      listZeroAngleMass
          (post ++ pre)
          (Apost ++ Apre)
        =
      listZeroAngleMass
          (quotientList t C.gaps)
          (cyclicRayAngles (p := p) i first rest) := by
    rw [hq,hAs]
    rw [listZeroAngleMass_append
      pre (1 :: post) Apre (Ae :: Apost) hpreA]
    simp only [listZeroAngleMass, if_neg (by decide : (1 : ℕ) ≠ 0), zero_add]
    rw [listZeroAngleMass_append
      post pre Apost Apre hpostA]
    ring

  have hblocksMass :
      listZeroAngleMass
          (post ++ pre)
          (Apost ++ Apre)
        =
      leftA.sum + rightA.sum := by
    rw [hhiddenQ,hAhidden]
    exact listZeroAngleMass_two_zero_blocks
      leftQ rightQ leftA rightA
      (n - 1) Ah
      (by omega)
      hleftA.symm hrightA
      hleftZero hrightZero

  have hsmall :
      leftA.sum + rightA.sum ≤ delta * lam := by
    rw [← hblocksMass, hrotMass]
    exact hzeroTotal

  exact ⟨pre,post,leftQ,rightQ,
    Apre,Apost,Ae,leftA,rightA,Ah,
    hq,hAs,hpreA,hpostA,
    hhiddenQ,hAhidden,
    hleftA.symm,hrightA,
    hleftZero,hrightZero,hsmall⟩

#print axioms supportTwo_transition_one_has_two_narrow_angle_blocks

end JSP000404Research
