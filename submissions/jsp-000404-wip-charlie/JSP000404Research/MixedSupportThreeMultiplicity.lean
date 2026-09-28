import JSP000404Research.SupportOneExposureBudget
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Support-three multiplicity in the mixed six-point branch

Fix the six-point profile with one sharp top and five n-3 minima. Suppose one
minimum a has quotient support one.

Among the other four minima, at least two must have support three. Otherwise
at least three of them have support at most two. Together with the top and a,
the support-interval packing theorem for three additional support-at-most-two
centres gives an immediate contradiction.
-/

namespace JSP000404Research

theorem mixed_support_one_has_at_least_two_support_three
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
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
    2 ≤
      (((Finset.univ.erase top).erase a).filter
        (fun v =>
          positiveSupport (centreQuotient (C v) t) = 3)).card := by
  classical
  let R : Finset V := (Finset.univ.erase top).erase a
  let S3 : Finset V :=
    R.filter fun v =>
      positiveSupport (centreQuotient (C v) t) = 3
  have hRcard : R.card = 4 := by
    dsimp [R]
    have haMem :
        a ∈ (Finset.univ.erase top : Finset V) := by
      simp [hta.symm]
    rw [Finset.card_erase_of_mem haMem,
        Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
    norm_num

  by_contra hnot
  have hS3le : S3.card ≤ 1 := by
    dsimp [S3]
    omega
  let L : Finset V := R \ S3
  have hS3sub : S3 ⊆ R := Finset.filter_subset _ _
  have hLcard : 3 ≤ L.card := by
    dsimp [L]
    rw [Finset.card_sdiff hS3sub, hRcard]
    omega

  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq hLcard

  have hT_R : T ⊆ R := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hTsub hv)).1

  have hTnotS3 :
      ∀ v ∈ T,
        positiveSupport (centreQuotient (C v) t) ≠ 3 := by
    intro v hv
    have hvL := hTsub hv
    have hvNot := (Finset.mem_sdiff.mp hvL).2
    intro h3
    apply hvNot
    dsimp [S3]
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp hvL).1, h3⟩

  have hTneTop : ∀ v ∈ T, v ≠ top := by
    intro v hv
    have hvR := hT_R hv
    dsimp [R] at hvR
    exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp hvR).2).1

  have hTneA : ∀ v ∈ T, v ≠ a := by
    intro v hv
    have hvR := hT_R hv
    dsimp [R] at hvR
    exact (Finset.mem_erase.mp hvR).1

  have hTsupport :
      ∀ v ∈ T,
        positiveSupport (centreQuotient (C v) t) ≤ 2 := by
    intro v hv
    have hvTop := hTneTop v hv
    have hstruct :=
      concrete_deficit_three_structure
        (C v) (by omega : 4 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht (hMin v hvTop)
    rcases hstruct with h1 | h2 | h3
    · rw [h1.1]
      omega
    · rw [h2.1]
    · exact False.elim ((hTnotS3 v hv) h3.1)

  have hTthree : T.card = 3 := hTcard
  obtain ⟨b, hbT, c, hcT, hbc⟩ :=
    Finset.two_le_card.mp (by omega : 2 ≤ T.card)
  let T' := T.erase b
  have hT'card : T'.card = 2 := by
    dsimp [T']
    rw [Finset.card_erase_of_mem hbT, hTthree]
  obtain ⟨c0, hc0T', d, hdT', hc0d⟩ :=
    Finset.two_le_card.mp (by omega : 2 ≤ T'.card)
  have hc0T : c0 ∈ T := (Finset.mem_erase.mp hc0T').2
  have hdT : d ∈ T := (Finset.mem_erase.mp hdT').2
  have hbc0 : b ≠ c0 :=
    (Finset.mem_erase.mp hc0T').1.symm
  have hbd : b ≠ d :=
    (Finset.mem_erase.mp hdT').1.symm

  exact no_three_support_le_two_after_top_support_one
    hp hcap (by omega : 4 ≤ n)
    hdelta0 hdeltaHalf ht hlam
    hta
    (hTneTop b hbT).symm
    (hTneTop c0 hc0T).symm
    (hTneTop d hdT).symm
    (hTneA b hbT).symm
    (hTneA c0 hc0T).symm
    (hTneA d hdT).symm
    hbc0 hbd hc0d
    (C top) (C a) (C b) (C c0) (C d)
    hTop (hMin a hta.symm) hsupA
    (hTsupport b hbT)
    (hTsupport c0 hc0T)
    (hTsupport d hdT)

#print axioms mixed_support_one_has_at_least_two_support_three

end JSP000404Research
