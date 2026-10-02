import JSP000404Research.ProjectionConsecutiveSupportTwoTransitionDichotomy
import JSP000404Research.SecondLayerFourSupportReduction
import Mathlib.Tactic

/-!
# Transition-pattern terminal in the unique-support-one four-centre branch

Let o be second-layer support-one and a,b,c second-layer support-two, all
sharing one consecutive three-band retained palette.  The support-one
transition quotient is n-1.  Each support-two transition quotient belongs to
{1,n-1}.

Four-centre transition packing therefore implies:
* at most one of a,b,c can have transition quotient n-1;
* if one does, the other two have quotient one and the total transition
  quotient sum is exactly 2n.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem uniqueSupportOne_threeSupportTwo_transition_pattern
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {o a b c : ProjectionOrdered V}
    (hoa : o ≠ a) (hob : o ≠ b) (hoc : o ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hoSecond : centreExponent (Cfam o) t = n - 2)
    (haSecond : centreExponent (Cfam a) t = n - 2)
    (hbSecond : centreExponent (Cfam b) t = n - 2)
    (hcSecond : centreExponent (Cfam c) t = n - 2)
    (hoSupport :
      positiveSupport (centreQuotient (Cfam o) t) = 1)
    (haSupport :
      positiveSupport (centreQuotient (Cfam a) t) = 2)
    (hbSupport :
      positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport :
      positiveSupport (centreQuotient (Cfam c) t) = 2)
    (haLoss :
      a ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hcLoss :
      c ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hpalA :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R a).map Fin.valEmbedding =
        threeNatInterval m)
    (hpalB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R b).map Fin.valEmbedding =
        threeNatInterval m)
    (hpalC :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R c).map Fin.valEmbedding =
        threeNatInterval m) :
    ∃ Ho :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t o (Cfam o),
    ∃ Ha :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t a (Cfam a),
    ∃ Hb :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t b (Cfam b),
    ∃ Hc :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t c (Cfam c),
      Ho.qe = n - 1 ∧
      (Ha.qe = 1 ∨ Ha.qe = n - 1) ∧
      (Hb.qe = 1 ∨ Hb.qe = n - 1) ∧
      (Hc.qe = 1 ∨ Hc.qe = n - 1) ∧
      ¬ (Ha.qe = n - 1 ∧ Hb.qe = n - 1) ∧
      ¬ (Ha.qe = n - 1 ∧ Hc.qe = n - 1) ∧
      ¬ (Hb.qe = n - 1 ∧ Hc.qe = n - 1) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  let Ho :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        o (Cfam o) (by rw [hoSecond]; omega))
  let Ha :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        a (Cfam a) (by rw [haSecond]; omega))
  let Hb :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        b (Cfam b) (by rw [hbSecond]; omega))
  let Hc :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht hlam
        c (Cfam c) (by rw [hcSecond]; omega))

  have hqo : Ho.qe = n - 1 := by
    have h :=
      support_one_transitionInterval_qe_eq_exponent_add_one
        (Cfam o) Ho hoSupport
    rw [hoSecond] at h
    omega

  have hqa :=
    planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam a
      haLoss haSecond haSupport hpalA Ha
  have hqb :=
    planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam b
      hbLoss hbSecond hbSupport hpalB Hb
  have hqc :=
    planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam c
      hcLoss hcSecond hcSupport hpalC Hc

  have hpack :=
    four_transition_quotient_sum_le_two_n
      (reindexedPoint_injective hp)
      (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      hoa hob hoc hab hac hbc
      (Cfam o) (Cfam a) (Cfam b) (Cfam c)
      Ho Ha Hb Hc

  refine ⟨Ho,Ha,Hb,Hc,hqo,hqa,hqb,hqc,?_,?_,?_⟩
  · rintro ⟨haN,hbN⟩
    rw [hqo,haN,hbN] at hpack
    have hcPos : 1 ≤ Hc.qe :=
      Nat.one_le_iff_ne_zero.mpr Hc.qe_ne
    omega
  · rintro ⟨haN,hcN⟩
    rw [hqo,haN,hcN] at hpack
    have hbPos : 1 ≤ Hb.qe :=
      Nat.one_le_iff_ne_zero.mpr Hb.qe_ne
    omega
  · rintro ⟨hbN,hcN⟩
    rw [hqo,hbN,hcN] at hpack
    have haPos : 1 ≤ Ha.qe :=
      Nat.one_le_iff_ne_zero.mpr Ha.qe_ne
    omega

#print axioms uniqueSupportOne_threeSupportTwo_transition_pattern

end ProjectionOrdered
end JSP000404Research
