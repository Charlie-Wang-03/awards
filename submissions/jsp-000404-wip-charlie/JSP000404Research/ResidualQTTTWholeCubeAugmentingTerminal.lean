import JSP000404Research.ResidualWholeCubePairExtraSharedWitness
import JSP000404Research.ResidualQTTTWholeCubeCoreSplit
import Mathlib.Tactic

/-!
# Q/T/T/T whole-cube augmenting terminal

Assume the source-preserving Q/T/T/T state satisfies

* x,y are in the minimal deficient core T;
* at least one of s,z is in T;
* a whole-cube Q/T partner exists among x,y,z.

If the whole-cube partner lies in T, the quantitative whole-cube shared-mass
argument forces an additional shared word supplied by a third core vertex.

Therefore the only non-augmenting provenance state is the genuinely fresh-z
case:

  z ∉ T,  s ∈ T,  WholeCubeQTPair C s z cz.

This replaces the previous coarse core/fresh split by a one-branch frontier.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def WholeCubeThirdSourceWitness
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ w : V,
    word ∈ enlargedProjectedCandidateBlock C exponent v ∧
    word ∈ enlargedProjectedCandidateBlock C exponent w ∧
    word ∉ retainedCompletionWords C v ∧
    word ∉ retainedCompletionWords C s ∧
    w ∈ T ∧
    w ≠ v ∧
    w ≠ s

theorem QTTT_wholeCube_augmenting_or_single_fresh_terminal
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
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    (hzSecond : exponent z = n - 2)
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hwhole :
      WholeCubeQTPair C s x cx ∨
      WholeCubeQTPair C s y cy ∨
      WholeCubeQTPair C s z cz) :
    WholeCubeThirdSourceWitness C exponent T s x
    ∨ WholeCubeThirdSourceWitness C exponent T s y
    ∨ WholeCubeThirdSourceWitness C exponent T s z
    ∨
      (z ∉ T ∧ s ∈ T ∧ WholeCubeQTPair C s z cz) := by
  rcases hwhole with hxWhole | hyWhole | hzWhole
  · left
    exact minimal_core_wholeCubeQTPair_has_third_source
      C exponent hn3 hdef hmin
      hxT hsx hxLoss hsLoss
      hxSecond hcx hxWhole
  · right; left
    exact minimal_core_wholeCubeQTPair_has_third_source
      C exponent hn3 hdef hmin
      hyT hsy hyLoss hsLoss
      hySecond hcy hyWhole
  · by_cases hzT : z ∈ T
    · right; right; left
      exact minimal_core_wholeCubeQTPair_has_third_source
        C exponent hn3 hdef hmin
        hzT hsz hzLoss hsLoss
        hzSecond hcz hzWhole
    · right; right; right
      have hsT : s ∈ T := by
        rcases hthirdT with hsT | hzT'
        · exact hsT
        · exact False.elim (hzT hzT')
      exact ⟨hzT,hsT,hzWhole⟩

#print axioms QTTT_wholeCube_augmenting_or_single_fresh_terminal


/-- Strengthened terminal: every whole-cube Q/T/T/T state with the preserved
core provenance forces a third-core-source augmenting witness.  The apparent
fresh-z exception is removed by swapping the symmetric whole-cube pair and
using the core completion owner s as the translated endpoint. -/
theorem QTTT_wholeCube_forces_third_core_source
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
    (hwhole :
      WholeCubeQTPair C s x cx ∨
      WholeCubeQTPair C s y cy ∨
      WholeCubeQTPair C s z cz) :
    WholeCubeThirdSourceWitness C exponent T s x
    ∨ WholeCubeThirdSourceWitness C exponent T s y
    ∨ WholeCubeThirdSourceWitness C exponent T s z
    ∨ WholeCubeThirdSourceWitness C exponent T z s := by
  rcases hwhole with hxWhole | hyWhole | hzWhole
  · exact Or.inl
      (minimal_core_wholeCubeQTPair_has_third_source
        C exponent hn3 hdef hmin
        hxT hsx hxLoss hsLoss hxSecond hcx hxWhole)
  · exact Or.inr (Or.inl
      (minimal_core_wholeCubeQTPair_has_third_source
        C exponent hn3 hdef hmin
        hyT hsy hyLoss hsLoss hySecond hcy hyWhole))
  · by_cases hzT : z ∈ T
    · exact Or.inr (Or.inr (Or.inl
        (minimal_core_wholeCubeQTPair_has_third_source
          C exponent hn3 hdef hmin
          hzT hsz hzLoss hsLoss hzSecond hcz hzWhole)))
    · have hsT : s ∈ T := by
        rcases hthirdT with hsT | hzT'
        · exact hsT
        · exact False.elim (hzT hzT')
      have hsym :
          WholeCubeQTPair C z s cz :=
        wholeCubeQTPair_symm_of_active C hcz hzWhole
      have hczS : cz ∈ retainedActive C s := by
        rcases hzWhole with ⟨hactiveEq,_⟩
        rw [← hactiveEq]
        exact hcz
      exact Or.inr (Or.inr (Or.inr
        (minimal_core_wholeCubeQTPair_has_third_source
          C exponent hn3 hdef hmin
          hsT hsz.symm hsLoss hzLoss hsSecond hczS hsym)))

#print axioms QTTT_wholeCube_forces_third_core_source

end OrderedEdgeColoring
end JSP000404Research
