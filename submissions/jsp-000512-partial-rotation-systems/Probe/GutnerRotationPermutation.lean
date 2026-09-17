import Probe.GutnerRotationRowNodup
import Probe.GutnerRotationRowExhaustive
import Probe.GutnerRotationRowNontrivial
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
A structured permutation certificate for the explicit Gutner graph.

Each vertex's explicit neighbour row is converted by Mathlib's `List.formPerm`
into a cyclic permutation of that actual neighbour fibre.  The three finite row
certificates live in independent modules so Lake can build them in parallel.
-/
namespace JSP512Probe.Gutner

/-- The local cyclic permutation at one vertex. -/
def neighborPerm (u : Fin 86) : Equiv.Perm (graph.neighborSet u) :=
  (neighborRow u).formPerm

/-- Every neighbour is genuinely moved by the local cycle. -/
theorem neighborPerm_moves (u : Fin 86) (x : graph.neighborSet u) :
    neighborPerm u x ≠ x := by
  exact (List.formPerm_apply_mem_ne_self_iff
    (neighborRow u) (neighborRow_nodup u) x (neighborRow_exhaustive u x)).2
      (neighborRow_nontrivial u)

/-- Any two neighbours of one vertex lie in the same local cycle. -/
theorem neighborPerm_sameCycle (u : Fin 86) (x y : graph.neighborSet u) :
    (neighborPerm u).SameCycle x y := by
  exact (List.isCycle_formPerm (neighborRow_nodup u) (neighborRow_nontrivial u)).sameCycle
    (neighborPerm_moves u x) (neighborPerm_moves u y)

/-- Regard a dart as an element of its source's neighbour fibre. -/
def neighborOfDart (d : graph.Dart) : graph.neighborSet d.fst :=
  ⟨d.snd, d.adj⟩

/-- Rotate a dart inside its source fibre. -/
def rotateDart (d : graph.Dart) : graph.Dart :=
  graph.dartOfNeighborSet d.fst (neighborPerm d.fst (neighborOfDart d))

/-- Inverse rotation inside the same source fibre. -/
def unrotateDart (d : graph.Dart) : graph.Dart :=
  graph.dartOfNeighborSet d.fst ((neighborPerm d.fst).symm (neighborOfDart d))


theorem unrotate_rotate (d : graph.Dart) : unrotateDart (rotateDart d) = d := by
  rcases d with ⟨⟨u, v⟩, h⟩
  apply SimpleGraph.Dart.ext
  change (u, ↑((neighborPerm u).symm (neighborPerm u ⟨v, h⟩))) = (u, v)
  rw [Equiv.symm_apply_apply]


theorem rotate_unrotate (d : graph.Dart) : rotateDart (unrotateDart d) = d := by
  rcases d with ⟨⟨u, v⟩, h⟩
  apply SimpleGraph.Dart.ext
  change (u, ↑(neighborPerm u ((neighborPerm u).symm ⟨v, h⟩))) = (u, v)
  rw [Equiv.apply_symm_apply]

/-- The fibrewise cycles assemble to a permutation of all graph darts. -/
def rotationPerm : Equiv.Perm graph.Dart where
  toFun := rotateDart
  invFun := unrotateDart
  left_inv := unrotate_rotate
  right_inv := rotate_unrotate

end JSP512Probe.Gutner
