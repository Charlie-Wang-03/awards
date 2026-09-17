import Probe.GutnerGraph
import Probe.RotationSystem
import Mathlib.Data.Fin.VecNotation

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Counterclockwise cyclic neighbour order for the explicit Gutner graph.
The table is data only; the graph-theoretic obligations below are rechecked by
Lean's kernel. -/
def rotationRows : Fin 86 → List (Fin 86) :=
  ![
    [81,80,79,83,84,1,4,3,2,6,7,11,10,9,13,14,18,17,16,20,21,25,24,23,27,28,32,31,30,34,35,39,38,37,41,42,46,45,44,48,49,53,52,51,55,56,60,59,58,62,63,67,66,65,69,70,74,73,72,76,77],
    [0,84,85,79,82,81,77,78,72,75,74,70,71,65,68,67,63,64,58,61,60,56,57,51,54,53,49,50,44,47,46,42,43,37,40,39,35,36,30,33,32,28,29,23,26,25,21,22,16,19,18,14,15,9,12,11,7,8,2,5,4],
    [0,3,5,1,8,6], [0,4,5,2], [0,1,5,3], [4,1,2,3], [0,2,8,7],
    [0,6,8,1], [6,2,1,7], [0,10,12,1,15,13], [0,11,12,9], [0,1,12,10],
    [11,1,9,10], [0,9,15,14], [0,13,15,1], [13,9,1,14],
    [0,17,19,1,22,20], [0,18,19,16], [0,1,19,17], [18,1,16,17],
    [0,16,22,21], [0,20,22,1], [20,16,1,21],
    [0,24,26,1,29,27], [0,25,26,23], [0,1,26,24], [25,1,23,24],
    [0,23,29,28], [0,27,29,1], [27,23,1,28],
    [0,31,33,1,36,34], [0,32,33,30], [0,1,33,31], [32,1,30,31],
    [0,30,36,35], [0,34,36,1], [34,30,1,35],
    [0,38,40,1,43,41], [0,39,40,37], [0,1,40,38], [39,1,37,38],
    [0,37,43,42], [0,41,43,1], [41,37,1,42],
    [0,45,47,1,50,48], [0,46,47,44], [0,1,47,45], [46,1,44,45],
    [0,44,50,49], [0,48,50,1], [48,44,1,49],
    [0,52,54,1,57,55], [0,53,54,51], [0,1,54,52], [53,1,51,52],
    [0,51,57,56], [0,55,57,1], [55,51,1,56],
    [0,59,61,1,64,62], [0,60,61,58], [0,1,61,59], [60,1,58,59],
    [0,58,64,63], [0,62,64,1], [62,58,1,63],
    [0,66,68,1,71,69], [0,67,68,65], [0,1,68,66], [67,1,65,66],
    [0,65,71,70], [0,69,71,1], [69,65,1,70],
    [0,73,75,1,78,76], [0,74,75,72], [0,1,75,73], [74,1,72,73],
    [0,72,78,77], [0,76,78,1], [72,1,77,76],
    [0,80,82,1,85,83], [0,81,82,79], [0,1,82,80], [79,80,81,1],
    [0,79,85,84], [0,83,85,1], [83,79,1,84]
  ]

def cyclicSuccessor (row : List (Fin 86)) (x : Fin 86) : Fin 86 :=
  match row with
  | [] => x
  | first :: rest =>
      match (first :: rest).dropWhile (· != x) with
      | _ :: next :: _ => next
      | [_] => first
      | [] => x


def cyclicPredecessor (row : List (Fin 86)) (x : Fin 86) : Fin 86 :=
  cyclicSuccessor row.reverse x


def nextTarget (u v : Fin 86) : Fin 86 := cyclicSuccessor (rotationRows u) v

def prevTarget (u v : Fin 86) : Fin 86 := cyclicPredecessor (rotationRows u) v

/-- Every table successor is an actual neighbour. -/
theorem next_adj : ∀ d : graph.Dart, graph.Adj d.fst (nextTarget d.fst d.snd) := by
  decide +kernel

/-- Likewise for predecessors. -/
theorem prev_adj : ∀ d : graph.Dart, graph.Adj d.fst (prevTarget d.fst d.snd) := by
  decide +kernel


def rotateDart (d : graph.Dart) : graph.Dart :=
  ⟨(d.fst, nextTarget d.fst d.snd), next_adj d⟩


def unrotateDart (d : graph.Dart) : graph.Dart :=
  ⟨(d.fst, prevTarget d.fst d.snd), prev_adj d⟩


theorem unrotate_rotate : ∀ d : graph.Dart, unrotateDart (rotateDart d) = d := by
  decide +kernel


theorem rotate_unrotate : ∀ d : graph.Dart, rotateDart (unrotateDart d) = d := by
  decide +kernel

/-- Concrete cyclic rotation of the darts of Gutner's graph. -/
def rotationPerm : Equiv.Perm graph.Dart where
  toFun := rotateDart
  invFun := unrotateDart
  left_inv := unrotate_rotate
  right_inv := rotate_unrotate

instance rotationSameCycleDecidable : DecidableRel (Equiv.Perm.SameCycle rotationPerm) :=
  Equiv.Perm.instDecidableRelSameCycle rotationPerm

/-- Each source fibre is exactly one rotation cycle. -/
theorem rotation_local_cycle : ∀ d e : graph.Dart, d.fst = e.fst →
    Equiv.Perm.SameCycle rotationPerm d e := by
  decide +kernel

/-- A rotation system for the explicit 86-vertex Gutner graph. -/
def rotationSystem : RotationSystem graph where
  rotate := rotationPerm
  source := by intro d; rfl
  local_cycle := rotation_local_cycle

end JSP512Probe.Gutner
