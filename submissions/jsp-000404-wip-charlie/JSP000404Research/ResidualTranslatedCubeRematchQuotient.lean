import JSP000404Research.ResidualWholeCubeSecondCoordinateRecursion
import Mathlib.Tactic

/-!
# Quotienting exact T/T full rematches

A lossless T/T full rematch carries exactly:

* equality of the retained-active palettes;
* equality of the translated completion cubes.

These data define the natural equivalence relation on translated-cube states.
After quotienting by this relation, every ttFull recursion step is stationary,
so it does not need a numerical descent measure.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

structure TranslatedCubeState
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) where
  vertex : V
  coord : Fin n
  active : coord ∈ retainedActive C vertex

def TranslatedCubeState.Equivalent
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    (a b : TranslatedCubeState C) : Prop :=
  retainedActive C a.vertex =
      retainedActive C b.vertex
  ∧
  translatedCompletionWords C a.vertex a.coord =
      translatedCompletionWords C b.vertex b.coord

theorem translatedCubeState_equivalent_refl
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    (a : TranslatedCubeState C) :
    a.Equivalent a :=
  ⟨rfl,rfl⟩

theorem translatedCubeState_equivalent_symm
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    {a b : TranslatedCubeState C}
    (h : a.Equivalent b) :
    b.Equivalent a :=
  ⟨h.1.symm,h.2.symm⟩

theorem translatedCubeState_equivalent_trans
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    {a b c : TranslatedCubeState C}
    (hab : a.Equivalent b)
    (hbc : b.Equivalent c) :
    a.Equivalent c :=
  ⟨hab.1.trans hbc.1,hab.2.trans hbc.2⟩

instance translatedCubeStateSetoid
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Setoid (TranslatedCubeState C) where
  r := TranslatedCubeState.Equivalent
  iseqv :=
    ⟨translatedCubeState_equivalent_refl,
      translatedCubeState_equivalent_symm,
      translatedCubeState_equivalent_trans⟩

abbrev TranslatedCubeQuotient
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :=
  Quotient (translatedCubeStateSetoid C)

theorem ttFull_states_equivalent
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hdV : d ∈ retainedActive C v)
    (heW : e ∈ retainedActive C w)
    (hactiveEq :
      retainedActive C v = retainedActive C w)
    (hfull :
      translatedCompletionWords C v d =
        translatedCompletionWords C w e) :
    (TranslatedCubeState.mk v d hdV :
      TranslatedCubeState C).Equivalent
      (TranslatedCubeState.mk w e heW) :=
  ⟨hactiveEq,hfull⟩

theorem ttFull_same_quotient_state
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hdV : d ∈ retainedActive C v)
    (heW : e ∈ retainedActive C w)
    (hactiveEq :
      retainedActive C v = retainedActive C w)
    (hfull :
      translatedCompletionWords C v d =
        translatedCompletionWords C w e) :
    Quotient.mk
        (translatedCubeStateSetoid C)
        (TranslatedCubeState.mk v d hdV)
      =
    Quotient.mk
        (translatedCubeStateSetoid C)
        (TranslatedCubeState.mk w e heW) := by
  apply Quotient.sound
  exact ttFull_states_equivalent
    C hdV heW hactiveEq hfull

#print axioms ttFull_same_quotient_state

end OrderedEdgeColoring
end JSP000404Research
