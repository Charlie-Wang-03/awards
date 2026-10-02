import JSP000404Research.ResidualWholeCubeSecondCoordinateProfile
import Mathlib.Tactic

/-!
# Q/T/T/T whole-cube profile terminal

Compose the whole-cube third-core-source theorem with the profile reduction of
its second translated coordinate.

After the standard strict/exact/top/deep outlets are removed, the only
remaining whole-cube state is a second-layer core vertex carrying a translated
collision at a second active coordinate d distinct from the original
whole-cube owner coordinate c.

The fresh-z case is handled symmetrically, exactly as in
QTTT_wholeCube_forces_third_core_source.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTTT_wholeCube_profile_or_secondCoordinate_secondLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    (hexpLt : ∀ q, exponent q < n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
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
    (
      ∃ q : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) q
    )
    ∨
    (
      ∃ q : V,
        ExactProjectedBudget C exponent q
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q = n - 1
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q + 3 ≤ n
    )
    ∨
    WholeCubeSecondCoordinateSecondLayerWitness C exponent T s x cx
    ∨
    WholeCubeSecondCoordinateSecondLayerWitness C exponent T s y cy
    ∨
    WholeCubeSecondCoordinateSecondLayerWitness C exponent T s z cz
    ∨
    WholeCubeSecondCoordinateSecondLayerWitness C exponent T z s cz := by

  have classify
      {a b : V} {c : Fin n}
      (haLoss : a ∈ projectedLossVertices C exponent)
      (hpair : WholeCubeQTPair C b a c)
      (hwit : WholeCubeThirdSourceWitness C exponent T b a) :
      (
        ∃ q : V,
          1 ≤ dyadicProfileSurplus exponent (projectedFree C) q
      )
      ∨
      (
        ∃ q : V,
          ExactProjectedBudget C exponent q
      )
      ∨
      (
        ∃ q : V,
          q ∈ projectedLossVertices C exponent ∧
          exponent q = n - 1
      )
      ∨
      (
        ∃ q : V,
          q ∈ projectedLossVertices C exponent ∧
          exponent q + 3 ≤ n
      )
      ∨
      WholeCubeSecondCoordinateSecondLayerWitness
        C exponent T b a c :=
    wholeCubeThirdSource_profile_reduction
      C exponent hexpLt hexp honeLoss
      haLoss hpair hwit

  rcases hwhole with hxWhole | hyWhole | hzWhole
  · have hwit :=
      minimal_core_wholeCubeQTPair_has_third_source
        C exponent hn3 hdef hmin
        hxT hsx hxLoss hsLoss hxSecond hcx hxWhole
    rcases classify hxLoss hxWhole hwit with
      hstrict | hexact | htop | hdeep | hsecond
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl hexact)
    · exact Or.inr (Or.inr (Or.inl htop))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hdeep)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsecond))))
  · have hwit :=
      minimal_core_wholeCubeQTPair_has_third_source
        C exponent hn3 hdef hmin
        hyT hsy hyLoss hsLoss hySecond hcy hyWhole
    rcases classify hyLoss hyWhole hwit with
      hstrict | hexact | htop | hdeep | hsecond
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl hexact)
    · exact Or.inr (Or.inr (Or.inl htop))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hdeep)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hsecond)))))
  · by_cases hzT : z ∈ T
    · have hwit :=
        minimal_core_wholeCubeQTPair_has_third_source
          C exponent hn3 hdef hmin
          hzT hsz hzLoss hsLoss hzSecond hcz hzWhole
      rcases classify hzLoss hzWhole hwit with
        hstrict | hexact | htop | hdeep | hsecond
      · exact Or.inl hstrict
      · exact Or.inr (Or.inl hexact)
      · exact Or.inr (Or.inr (Or.inl htop))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hdeep)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hsecond))))))
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
      have hwit :=
        minimal_core_wholeCubeQTPair_has_third_source
          C exponent hn3 hdef hmin
          hsT hsz.symm hsLoss hzLoss hsSecond hczS hsym
      rcases classify hsLoss hsym hwit with
        hstrict | hexact | htop | hdeep | hsecond
      · exact Or.inl hstrict
      · exact Or.inr (Or.inl hexact)
      · exact Or.inr (Or.inr (Or.inl htop))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hdeep)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hsecond))))))

#print axioms QTTT_wholeCube_profile_or_secondCoordinate_secondLayer

end OrderedEdgeColoring
end JSP000404Research
