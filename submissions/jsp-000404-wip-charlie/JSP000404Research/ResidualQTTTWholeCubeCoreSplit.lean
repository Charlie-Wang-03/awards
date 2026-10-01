import JSP000404Research.ResidualQTTTConsecutivePaletteTerminal
import Mathlib.Tactic

/-!
# Core/fresh split for a Q/T/T/T whole-cube partner

If the two original translated owners x,y are known to lie in a deficient
core T, while the third-exit blocker z may be fresh, then the whole-cube
Q/T-pair terminal splits naturally:

* either the whole-cube translated owner is a core vertex (x or y);
* or it is exactly the fresh third owner z.

This preserves the provenance required by minimal-core arguments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def WholeCubeQTPair
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (s v : V) (c : Fin n) : Prop :=
  retainedActive C v = retainedActive C s ∧
  translatedCompletionWords C v c =
    retainedCompletionWords C s

theorem QTTT_wholeCube_partner_core_or_fresh
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {T : Finset V}
    {s x y z : V}
    (hxT : x ∈ T)
    (hyT : y ∈ T)
    {cx cy cz : Fin n}
    (hwhole :
      WholeCubeQTPair C s x cx ∨
      WholeCubeQTPair C s y cy ∨
      WholeCubeQTPair C s z cz) :
    (
      ∃ v ∈ T, ∃ c : Fin n,
        (v = x ∧ c = cx ∨ v = y ∧ c = cy) ∧
        WholeCubeQTPair C s v c
    )
    ∨
    WholeCubeQTPair C s z cz := by
  rcases hwhole with hx | hy | hz
  · left
    exact ⟨x,hxT,cx,Or.inl ⟨rfl,rfl⟩,hx⟩
  · left
    exact ⟨y,hyT,cy,Or.inr ⟨rfl,rfl⟩,hy⟩
  · exact Or.inr hz

#print axioms QTTT_wholeCube_partner_core_or_fresh

end OrderedEdgeColoring
end JSP000404Research
