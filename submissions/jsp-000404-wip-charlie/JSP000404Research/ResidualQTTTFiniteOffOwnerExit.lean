import JSP000404Research.ResidualWholeCubeOffOwnerExit
import JSP000404Research.ResidualQTTTWholeCubeAugmentingTerminal
import Mathlib.Tactic

/-!
# Finite off-owner exit terminal for Q/T/T/T

In a Q/T/T/T whole-cube state the completion palette is exactly
{cx,cy,cz}.  Once one owner coordinate c is consumed by the whole-cube pair,
the augmenting off-owner exit must use one of the other two owner coordinates.

Thus the whole-cube branch reduces to four provenance-aware exit types:
* s -> x at cy or cz;
* s -> y at cx or cz;
* s -> z at cx or cy;
* in the fresh-z symmetric case, z -> s at cx or cy.

Each exit still carries a third core source distinct from both endpoints.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def QTTTOffOwnerExitAt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (completion partner : V)
    (owner alt₁ alt₂ : Fin n) : Prop :=
  ∃ d : Fin n,
  ∃ word : Fin n → Bool,
  ∃ w : V,
    (d = alt₁ ∨ d = alt₂) ∧
    d ∈ retainedActive C partner ∧
    word ∈ translatedCompletionWords C partner d ∧
    word ∈ enlargedProjectedCandidateBlock C exponent w ∧
    w ∈ T ∧
    w ≠ partner ∧
    w ≠ completion

theorem offOwner_mem_two_of_three
    {n : ℕ}
    {d c a b : Fin n}
    (hd : d ∈ ({c,a,b} : Finset (Fin n)))
    (hdc : d ≠ c) :
    d = a ∨ d = b := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h
  · exact False.elim (hdc h)
  · exact Or.inl h
  · exact Or.inr h

theorem QTTT_wholeCube_forces_finite_off_owner_exit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsActive :
      retainedActive C s = {cx,cy,cz})
    (hwhole :
      WholeCubeQTPair C s x cx ∨
      WholeCubeQTPair C s y cy ∨
      WholeCubeQTPair C s z cz) :
    QTTTOffOwnerExitAt C exponent T s x cx cy cz
    ∨ QTTTOffOwnerExitAt C exponent T s y cy cx cz
    ∨ QTTTOffOwnerExitAt C exponent T s z cz cx cy
    ∨ QTTTOffOwnerExitAt C exponent T z s cz cx cy := by
  rcases hwhole with hxWhole | hyWhole | hzWhole
  · have hxActiveEq := hxWhole.1
    obtain ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
        _hnotX,_hnotS,hwT,hwNeX,hwNeS⟩ :=
      minimal_core_wholeCubeQTPair_has_off_owner_third_exit
        C exponent hn3 hdef hmin
        hxT hsx hxLoss hsLoss hxSecond hcx hxWhole
    have hdS : d ∈ retainedActive C s := by
      rw [← hxActiveEq]
      exact hdActive
    have hdSet : d ∈ ({cx,cy,cz} : Finset (Fin n)) := by
      rw [← hsActive]
      exact hdS
    have hdAlt : d = cy ∨ d = cz :=
      offOwner_mem_two_of_three hdSet hdc
    exact Or.inl
      ⟨d,word,w,hdAlt,hdActive,hdWord,hwBlock,hwT,hwNeX,hwNeS⟩

  · have hyActiveEq := hyWhole.1
    obtain ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
        _hnotY,_hnotS,hwT,hwNeY,hwNeS⟩ :=
      minimal_core_wholeCubeQTPair_has_off_owner_third_exit
        C exponent hn3 hdef hmin
        hyT hsy hyLoss hsLoss hySecond hcy hyWhole
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
    exact Or.inr (Or.inl
      ⟨d,word,w,hdAlt,hdActive,hdWord,hwBlock,hwT,hwNeY,hwNeS⟩)

  · have hzActiveEq := hzWhole.1
    by_cases hzT : z ∈ T
    · obtain ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
          _hnotZ,_hnotS,hwT,hwNeZ,hwNeS⟩ :=
        minimal_core_wholeCubeQTPair_has_off_owner_third_exit
          C exponent hn3 hdef hmin
          hzT hsz hzLoss hsLoss hzSecond hcz hzWhole
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
      exact Or.inr (Or.inr (Or.inl
        ⟨d,word,w,hdAlt,hdActive,hdWord,hwBlock,hwT,hwNeZ,hwNeS⟩))
    · have hsT : s ∈ T := by
        rcases hthirdT with hsT | hzT'
        · exact hsT
        · exact False.elim (hzT hzT')
      have hsym : WholeCubeQTPair C z s cz :=
        wholeCubeQTPair_symm_of_active C hcz hzWhole
      have hczS : cz ∈ retainedActive C s := by
        rw [← hzActiveEq]
        exact hcz
      obtain ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
          _hnotS,_hnotZ,hwT,hwNeS,hwNeZ⟩ :=
        minimal_core_wholeCubeQTPair_has_off_owner_third_exit
          C exponent hn3 hdef hmin
          hsT hsz.symm hsLoss hzLoss hsSecond hczS hsym
      have hdSet : d ∈ ({cz,cx,cy} : Finset (Fin n)) := by
        rw [show ({cz,cx,cy} : Finset (Fin n)) = {cx,cy,cz} by
          ext q
          simp [or_left_comm,or_comm,or_assoc]]
        rw [← hsActive]
        exact hdActive
      have hdAlt : d = cx ∨ d = cy :=
        offOwner_mem_two_of_three hdSet hdc
      exact Or.inr (Or.inr (Or.inr
        ⟨d,word,w,hdAlt,hdActive,hdWord,hwBlock,hwT,hwNeS,hwNeZ⟩))

#print axioms QTTT_wholeCube_forces_finite_off_owner_exit

end OrderedEdgeColoring
end JSP000404Research
