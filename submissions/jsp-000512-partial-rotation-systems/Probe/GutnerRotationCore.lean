import Probe.GutnerRotationPermutation
import Probe.RotationSystem

/-!
The local-cycle obligation for the Gutner rotation system is proved from the
fibre cycles in `GutnerRotationPermutation`, without invoking the generic finite
`SameCycle` decision procedure on all darts.
-/
namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Rotating a dart rebuilt from one neighbour is exactly the local neighbour
permutation followed by the same dart reconstruction. -/
theorem rotateDart_dartOfNeighborSet (u : Fin 86) (x : graph.neighborSet u) :
    rotateDart (graph.dartOfNeighborSet u x) =
      graph.dartOfNeighborSet u (neighborPerm u x) := by
  apply SimpleGraph.Dart.ext
  rfl

/-- Iterating the global dart rotation is the same as iterating the local
neighbour permutation in the fixed source fibre. -/
theorem rotationPerm_pow (n : ℕ) (d : graph.Dart) :
    (rotationPerm ^ n) d =
      graph.dartOfNeighborSet d.fst ((neighborPerm d.fst ^ n) (neighborOfDart d)) := by
  induction n with
  | zero =>
      apply SimpleGraph.Dart.ext
      simp [neighborOfDart]
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      change rotateDart
          (graph.dartOfNeighborSet d.fst ((neighborPerm d.fst ^ n) (neighborOfDart d))) =
        graph.dartOfNeighborSet d.fst ((neighborPerm d.fst ^ (n + 1)) (neighborOfDart d))
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact rotateDart_dartOfNeighborSet d.fst
        ((neighborPerm d.fst ^ n) (neighborOfDart d))

/-- Each source fibre is exactly one rotation cycle. -/
theorem rotation_local_cycle : ∀ d e : graph.Dart, d.fst = e.fst →
    Equiv.Perm.SameCycle rotationPerm d e := by
  intro d e hsrc
  let x : graph.neighborSet d.fst := neighborOfDart d
  let y : graph.neighborSet d.fst := ⟨e.snd, by simpa [hsrc] using e.adj⟩
  have hxy : (neighborPerm d.fst).SameCycle x y :=
    neighborPerm_sameCycle d.fst x y
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, rotationPerm_pow]
  change graph.dartOfNeighborSet d.fst ((neighborPerm d.fst ^ n) x) = e
  rw [hn]
  apply SimpleGraph.Dart.ext
  simp [y, hsrc]

/-- A rotation system for the explicit 86-vertex Gutner graph. -/
def rotationSystem : RotationSystem graph where
  rotate := rotationPerm
  source := by intro d; rfl
  local_cycle := rotation_local_cycle

end JSP512Probe.Gutner
