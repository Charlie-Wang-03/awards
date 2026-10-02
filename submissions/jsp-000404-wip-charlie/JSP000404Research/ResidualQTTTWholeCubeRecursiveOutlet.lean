import JSP000404Research.ResidualWholeCubeOffOwnerRecursiveOutlet
import JSP000404Research.ResidualQTTTFiniteOffOwnerExit
import Mathlib.Tactic

/-!
# Q/T/T/T whole-cube recursive outlet

Combine the source-preserving Q/T/T/T whole-cube provenance with the
off-owner single-loss recursive outlet.

No matter which translated owner forms the whole-cube pair, and even in the
fresh-z case after symmetry, the branch returns to the standard recursive
alphabet:

* a genuine Boolean hole;
* a strict-profile blocker paying at least one surplus token;
* or a nonempty completion fibre of cardinality at most two whose blockers are
  exact-budget or projected-loss vertices.

The displaced coordinate is also identified as one of the two owner colours
different from the whole-cube owner coordinate.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def QTTTWholeCubeRecursiveHardFibre
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (source : V)
    (owner alt₁ alt₂ : Fin n) : Prop :=
  ∃ d : Fin n,
  ∃ y : Fin n → Bool,
    (d = alt₁ ∨ d = alt₂) ∧
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

theorem QTTT_wholeCube_hole_or_paid_or_recursive_fibre
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
    QTTTWholeCubeRecursiveHardFibre
      C exponent x cx cy cz
    ∨
    QTTTWholeCubeRecursiveHardFibre
      C exponent y cy cx cz
    ∨
    QTTTWholeCubeRecursiveHardFibre
      C exponent z cz cx cy
    ∨
    QTTTWholeCubeRecursiveHardFibre
      C exponent s cz cx cy := by
  rcases hwhole with hxWhole | hyWhole | hzWhole

  · have hxActiveEq := hxWhole.1
    rcases
      wholeCube_offOwner_exit_hole_or_paid_or_exact_loss_fibre
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
    · obtain ⟨yy,hne,hcard,hprof⟩ := hfibre
      exact Or.inr (Or.inr (Or.inl
        ⟨d,yy,hdAlt,hne,hcard,hprof⟩))

  · have hyActiveEq := hyWhole.1
    rcases
      wholeCube_offOwner_exit_hole_or_paid_or_exact_loss_fibre
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
    · obtain ⟨yy,hne,hcard,hprof⟩ := hfibre
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d,yy,hdAlt,hne,hcard,hprof⟩)))

  · have hzActiveEq := hzWhole.1
    by_cases hzT : z ∈ T
    · rcases
        wholeCube_offOwner_exit_hole_or_paid_or_exact_loss_fibre
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
        exact hdS
      have hdAlt : d = cx ∨ d = cy :=
        offOwner_mem_two_of_three hdSet hdc
      rcases hout with hhole | hpaid | hfibre
      · exact Or.inl hhole
      · obtain ⟨yy,w,hwQ,hpaid⟩ := hpaid
        exact Or.inr (Or.inl ⟨w,hpaid⟩)
      · obtain ⟨yy,hne,hcard,hprof⟩ := hfibre
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨d,yy,hdAlt,hne,hcard,hprof⟩))))

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
        wholeCube_offOwner_exit_hole_or_paid_or_exact_loss_fibre
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
      · obtain ⟨yy,hne,hcard,hprof⟩ := hfibre
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨d,yy,hdAlt,hne,hcard,hprof⟩))))

#print axioms QTTT_wholeCube_hole_or_paid_or_recursive_fibre

end OrderedEdgeColoring
end JSP000404Research
