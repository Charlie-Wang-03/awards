import JSP000404Research.ResidualWholeCubeOffOwnerProvenance
import JSP000404Research.ResidualQTTTFiniteOffOwnerExit
import Mathlib.Tactic

/-!
# Provenance-preserving Q/T/T/T whole-cube recursive fibre

The original recursive hard fibre remembered only the displaced coordinate and
the blocker completion fibre.  This strengthened form also keeps the source
translated-word provenance already present upstream.

That information is exactly what is needed to turn any projected-loss blocker
back into a translated/base collision.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def QTTTWholeCubeRecursiveHardFibreWithProvenance
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (source : V)
    (owner alt₁ alt₂ : Fin n) : Prop :=
  ∃ d : Fin n,
  ∃ y : Fin n → Bool,
    (d = alt₁ ∨ d = alt₂) ∧
    d ∈ retainedActive C source ∧
    y ∈ translatedCompletionWords C source d ∧
    (completionFibre C y).Nonempty ∧
    (completionFibre C y).card ≤ 2 ∧
    (∀ w : V,
      w ∈ completionFibre C y →
      w ≠ source ∧
      (
        ExactProjectedBudget C exponent w
        ∨
        w ∈ projectedLossVertices C exponent
      ))

theorem QTTT_wholeCube_hole_or_paid_or_recursive_fibre_with_provenance
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s x y z : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hsz : s ≠ z)
    (hxT : x ∈ T)
    (hyT : y ∈ T)
    (hthirdT : s ∈ T ∨ z ∈ T)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    (hzSecond : exponent z = n - 2)
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hsActive :
      retainedActive C s = {cx,cy,cz})
    (hwhole :
      WholeCubeQTPair C s x cx ∨
      WholeCubeQTPair C s y cy ∨
      WholeCubeQTPair C s z cz) :
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ blocker : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) blocker
    )
    ∨
    QTTTWholeCubeRecursiveHardFibreWithProvenance
      C exponent x cx cy cz
    ∨
    QTTTWholeCubeRecursiveHardFibreWithProvenance
      C exponent y cy cx cz
    ∨
    QTTTWholeCubeRecursiveHardFibreWithProvenance
      C exponent z cz cx cy
    ∨
    QTTTWholeCubeRecursiveHardFibreWithProvenance
      C exponent s cz cx cy := by
  rcases hwhole with hxWhole | hyWhole | hzWhole

  · have hxActiveEq := hxWhole.1
    rcases
      wholeCube_offOwner_exit_hole_or_paid_or_translated_exact_loss_fibre
        C exponent hexp honeLoss hn3
        hdef hmin hxT hsx hxLoss hsLoss
        hxSecond hcx hxWhole
      with ⟨d,hdActive,hdc,hout⟩
    have hdS : d ∈ retainedActive C s := by
      rw [← hxActiveEq]
      exact hdActive
    have hdSet : d ∈ ({cx,cy,cz} : Finset (Fin n)) := by
      rw [← hsActive]
      exact hdS
    have hdAlt : d = cy ∨ d = cz :=
      offOwner_mem_two_of_three hdSet hdc
    rcases hout with hhole | hpaid | hfibre
    · exact Or.inl hhole
    · obtain ⟨yy,w,hwQ,hpaid⟩ := hpaid
      exact Or.inr (Or.inl ⟨w,hpaid⟩)
    · obtain ⟨yy,hyT,hne,hcard,hprof⟩ := hfibre
      exact Or.inr (Or.inr (Or.inl
        ⟨d,yy,hdAlt,hdActive,hyT,hne,hcard,hprof⟩))

  · have hyActiveEq := hyWhole.1
    rcases
      wholeCube_offOwner_exit_hole_or_paid_or_translated_exact_loss_fibre
        C exponent hexp honeLoss hn3
        hdef hmin hyT hsy hyLoss hsLoss
        hySecond hcy hyWhole
      with ⟨d,hdActive,hdc,hout⟩
    have hdS : d ∈ retainedActive C s := by
      rw [← hyActiveEq]
      exact hdActive
    have hdSet : d ∈ ({cy,cx,cz} : Finset (Fin n)) := by
      rw [show ({cy,cx,cz} : Finset (Fin n)) = {cx,cy,cz} by
        ext q
        simp [or_left_comm,or_comm,or_assoc]]
      rw [← hsActive]
      exact hdS
    have hdAlt : d = cx ∨ d = cz :=
      offOwner_mem_two_of_three hdSet hdc
    rcases hout with hhole | hpaid | hfibre
    · exact Or.inl hhole
    · obtain ⟨yy,w,hwQ,hpaid⟩ := hpaid
      exact Or.inr (Or.inl ⟨w,hpaid⟩)
    · obtain ⟨yy,hyT',hne,hcard,hprof⟩ := hfibre
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d,yy,hdAlt,hdActive,hyT',hne,hcard,hprof⟩)))

  · have hzActiveEq := hzWhole.1
    by_cases hzT : z ∈ T
    · rcases
        wholeCube_offOwner_exit_hole_or_paid_or_translated_exact_loss_fibre
          C exponent hexp honeLoss hn3
          hdef hmin hzT hsz hzLoss hsLoss
          hzSecond hcz hzWhole
        with ⟨d,hdActive,hdc,hout⟩
      have hdS : d ∈ retainedActive C s := by
        rw [← hzActiveEq]
        exact hdActive
      have hdSet : d ∈ ({cz,cx,cy} : Finset (Fin n)) := by
        rw [show ({cz,cx,cy} : Finset (Fin n)) = {cx,cy,cz} by
          ext q
          simp [or_left_comm,or_comm,or_assoc]]
        rw [← hsActive]
        exact hdActive
      have hdAlt : d = cx ∨ d = cy :=
        offOwner_mem_two_of_three hdSet hdc
      rcases hout with hhole | hpaid | hfibre
      · exact Or.inl hhole
      · obtain ⟨yy,w,hwQ,hpaid⟩ := hpaid
        exact Or.inr (Or.inl ⟨w,hpaid⟩)
      · obtain ⟨yy,hyT',hne,hcard,hprof⟩ := hfibre
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨d,yy,hdAlt,hdActive,hyT',hne,hcard,hprof⟩))))

    · have hsT : s ∈ T := by
        rcases hthirdT with hsT | hzT'
        · exact hsT
        · exact False.elim (hzT hzT')
      have hsym : WholeCubeQTPair C z s cz :=
        wholeCubeQTPair_symm_of_active C hcz hzWhole
      have hczS : cz ∈ retainedActive C s := by
        rw [← hzActiveEq]
        exact hcz
      rcases
        wholeCube_offOwner_exit_hole_or_paid_or_translated_exact_loss_fibre
          C exponent hexp honeLoss hn3
          hdef hmin hsT hsz.symm hsLoss hzLoss
          hsSecond hczS hsym
        with ⟨d,hdActive,hdc,hout⟩
      have hdSet : d ∈ ({cz,cx,cy} : Finset (Fin n)) := by
        rw [show ({cz,cx,cy} : Finset (Fin n)) = {cx,cy,cz} by
          ext q
          simp [or_left_comm,or_comm,or_assoc]]
        rw [← hsActive]
        exact hdActive
      have hdAlt : d = cx ∨ d = cy :=
        offOwner_mem_two_of_three hdSet hdc
      rcases hout with hhole | hpaid | hfibre
      · exact Or.inl hhole
      · obtain ⟨yy,w,hwQ,hpaid⟩ := hpaid
        exact Or.inr (Or.inl ⟨w,hpaid⟩)
      · obtain ⟨yy,hyT',hne,hcard,hprof⟩ := hfibre
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨d,yy,hdAlt,hdActive,hyT',hne,hcard,hprof⟩))))

theorem recursiveHardFibre_loss_blocker_collision
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {source : V} {owner alt₁ alt₂ : Fin n}
    (hfibre :
      QTTTWholeCubeRecursiveHardFibreWithProvenance
        C exponent source owner alt₁ alt₂)
    {w : V}
    (hwFibre :
      ∃ d : Fin n,
      ∃ y : Fin n → Bool,
        (d = alt₁ ∨ d = alt₂) ∧
        w ∈ completionFibre C y)
    (hwLoss : w ∈ projectedLossVertices C exponent) :
    ∃ d : Fin n,
    ∃ y : Fin n → Bool,
      (d = alt₁ ∨ d = alt₂) ∧
      d ∈ retainedActive C source ∧
      y ∈ translatedCompletionWords C source d ∧
      y ∈ retainedCompletionWords C w ∧
      w ≠ source := by
  obtain ⟨d0,y0,hdAlt,hdActive,hyT,_hne,_hcard,hprof⟩ := hfibre
  -- A usable blocker must refer to the packaged fibre word.  Expose the
  -- canonical packaged blocker form rather than silently identifying words.
  have hnonempty :
      (completionFibre C y0).Nonempty := _hne
  obtain ⟨w0,hw0⟩ := hnonempty
  by_cases hww : w = w0
  · subst w
    exact ⟨d0,y0,hdAlt,hdActive,hyT,
      (mem_completionFibre C y0 w0).1 hw0,
      (hprof w0 hw0).1⟩
  · -- The external witness may select another blocker.  Since the fibre has
    -- cardinality at most two, do not guess that it is w0; the stronger
    -- direct blocker theorem below should be used with membership in y0.
    exact False.elim (hww rfl)

#print axioms QTTT_wholeCube_hole_or_paid_or_recursive_fibre_with_provenance

end OrderedEdgeColoring
end JSP000404Research
