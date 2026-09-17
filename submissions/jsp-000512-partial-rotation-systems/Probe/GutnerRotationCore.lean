import Probe.GutnerRotationPermutation
import Probe.RotationSystem

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance rotationSameCycleDecidable : DecidableRel (Equiv.Perm.SameCycle rotationPerm) :=
  Equiv.Perm.instDecidableRelSameCycle rotationPerm

/-- A canonical neighbour in each nonempty rotation row. -/
def baseTarget (u : Fin 86) : Fin 86 :=
  match rotationRows u with
  | [] => u
  | v :: _ => v

/-- Every vertex of the explicit obstruction has a canonical incident dart. -/
theorem base_adj : ∀ u : Fin 86, graph.Adj u (baseTarget u) := by
  decide +kernel


def baseDart (u : Fin 86) : graph.Dart :=
  ⟨(u, baseTarget u), base_adj u⟩

/-- It is enough to certify one route from every dart to the canonical dart at
its source. This avoids a quadratic all-pairs SameCycle computation. -/
theorem sameCycle_base : ∀ d : graph.Dart,
    Equiv.Perm.SameCycle rotationPerm d (baseDart d.fst) := by
  decide +kernel

/-- Each source fibre is exactly one rotation cycle. -/
theorem rotation_local_cycle : ∀ d e : graph.Dart, d.fst = e.fst →
    Equiv.Perm.SameCycle rotationPerm d e := by
  intro d e h
  have hd := sameCycle_base d
  have he := sameCycle_base e
  rw [← h] at he
  exact hd.trans he.symm

/-- A rotation system for the explicit 86-vertex Gutner graph. -/
def rotationSystem : RotationSystem graph where
  rotate := rotationPerm
  source := by intro d; rfl
  local_cycle := rotation_local_cycle

end JSP512Probe.Gutner
