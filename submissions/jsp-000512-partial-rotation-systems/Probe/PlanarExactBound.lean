import Probe.GenusZeroListColoring
import Probe.GutnerRotation
import Probe.GutnerObstruction

namespace JSP512Probe

namespace RotationSystem

variable {V C : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Finite combinatorial planarity: existence of an orientable genus-zero
rotation system. This is the standard rotation-system model of finite planar
graphs; the external Heffter--Edmonds--Ringel correspondence identifies it with
the usual topological notion. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ R : RotationSystem G, R.HasGenusZero

/-- Thomassen's upper bound in the standard finite rotation-system formulation
of planarity. -/
theorem planar_five_list_coloring (hp : IsPlanar G)
    (L : V → Finset C) (hL : ∀ x, 5 ≤ (L x).card) :
    ∃ c : G.Coloring C, ListColoring.Respects G L c := by
  obtain ⟨R, hR⟩ := hp
  exact R.genusZero_five_list_coloring hR L hL

end RotationSystem

/-- `k` guarantees planar list coloring when every finite combinatorially planar
simple graph is colorable from every assignment of lists of size at least `k`.
The color type is arbitrary. -/
def GuaranteesPlanarListColoring (k : ℕ) : Prop :=
  ∀ (V C : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
      RotationSystem.IsPlanar G →
      ∀ L : V → Finset C, (∀ x, k ≤ (L x).card) →
        ∃ c : G.Coloring C, ListColoring.Respects G L c

/-- Five colors per list always suffice for finite planar graphs. -/
theorem five_guarantees_planar_list_coloring :
    GuaranteesPlanarListColoring 5 := by
  intro V C _ _ G _ hp L hL
  exact RotationSystem.planar_five_list_coloring hp L hL

namespace Gutner

/-- The explicit 86-vertex Gutner obstruction is planar in the same
rotation-system formulation used by the universal upper bound. -/
theorem rotation_planar : RotationSystem.IsPlanar graph :=
  ⟨rotationSystem, rotation_genusZero⟩

end Gutner

/-- Four colors per list do not suffice, witnessed by Gutner's explicit finite
planar graph and four-element list assignment. -/
theorem four_does_not_guarantee_planar_list_coloring :
    ¬ GuaranteesPlanarListColoring 4 := by
  intro h
  obtain ⟨c, hc⟩ := h (Fin 86) ℕ Gutner.graph Gutner.rotation_planar Gutner.lists (by
    intro x
    have hx := Gutner.lists_card x
    omega)
  exact Gutner.no_list_coloring ⟨c, hc⟩

/-- Exact answer to JSP-000512 / Erdős #631 in the standard finite
rotation-system formulation of planarity: list size five always suffices, while
list size four does not. -/
theorem jsp000512_exact :
    GuaranteesPlanarListColoring 5 ∧ ¬ GuaranteesPlanarListColoring 4 :=
  ⟨five_guarantees_planar_list_coloring,
    four_does_not_guarantee_planar_list_coloring⟩

end JSP512Probe
