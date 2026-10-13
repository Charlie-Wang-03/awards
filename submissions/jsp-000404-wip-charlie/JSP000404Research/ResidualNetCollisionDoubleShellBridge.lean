import JSP000404Research.ResidualNetCollisionBridgeFibreCapacity
import JSP000404Research.ResidualTwoFlipSourceEndpointBlocker
import Mathlib.Tactic

/-!
# Exact one-coordinate active shell around each original SOFT bridge endpoint

The canonical opposite double-flip target of a GENUINE NET collision
not only lies outside the two bridge completion cubes: its retained
active-bit violations against EACH endpoint are EXACTLY ONE, at the
original forward (reverse-lower endpoint) or reverse (forward-upper
endpoint) flip colour.

This is a pointwise, source-native exact strengthening of the
previous coarse "outside both cubes" theorem. It makes it possible
to bound collision fibres by TARGET-DEPENDENT eligible bridges rather
than ALL possible soft bridge carriers. No new axioms or geometry
hypotheses, and no covered word is counted as a true hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The set of retained ACTIVE coordinates at which a target Boolean
word fails a vertex's retained bit assignment. These are precisely
the constraints excluding the target from that vertex's cube. -/
noncomputable def retainedActiveViolationCoords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (d : Fin n → Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun e => e ∈ retainedActive C v ∧ d e ≠ retainedBit C v e)

/-- If w lies in the original vertex's completion cube, flipping
a SINGLE active coordinate ca, alongside another INACTIVE ci,
makes precisely ca violate the vertex's active-bit constraints. -/
theorem two_flip_one_active_one_inactive_exact_violation
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (ca ci : Fin n) (w : Fin n → Bool)
    (ha : ca ∈ retainedActive C v)
    (hi : ci ∉ retainedActive C v)
    (hw : w ∈ retainedCompletionWords C v) :
    retainedActiveViolationCoords C v
      (flipCompletionWord ca (flipCompletionWord ci w)) = {ca} := by
  classical
  have hne : ca ≠ ci := by
    intro heq
    exact hi (heq ▸ ha)
  ext e
  simp only [retainedActiveViolationCoords, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hea, hbad⟩
    by_contra he
    have heca : e ≠ ca := he
    have heci : e ≠ ci := by
      intro heci
      exact hi (heci ▸ hea)
    have hEq : flipCompletionWord ca (flipCompletionWord ci w) e =
        w e := by
      rw [flipCompletionWord_off ca e (flipCompletionWord ci w) heca,
        flipCompletionWord_off ci e w heci]
    have hcode := (mem_retainedCompletionWords C v w).1 hw e hea
    exact hbad (hEq.trans hcode)
  · intro he
    subst e
    refine ⟨ha, ?_⟩
    have hEq : flipCompletionWord ca (flipCompletionWord ci w) ca =
        ! (w ca) := by
      rw [flipCompletionWord_at,
        flipCompletionWord_off ci ca w hne]
    have hcode := (mem_retainedCompletionWords C v w).1 hw ca ha
    rw [hEq, ← hcode]
    cases w ca <;> decide

/-- At the TWO original soft bridge endpoints the actual canonical
NET collision diagonal has EXACTLY one retained-active violated bit
at EACH endpoint, respectively the distinct actual forward/reverse
hard transport flip colours. -/
theorem net_collision_certified_diagonal_exact_two_endpoint_shells
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
    let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
    retainedActiveViolationCoords C q.1.1 d = {cf} ∧
      retainedActiveViolationCoords C p.1.2 d = {cr} := by
  classical
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  change retainedActiveViolationCoords C q.1.1 d = {cf} ∧
      retainedActiveViolationCoords C p.1.2 d = {cr}
  have hsrc := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss s
  have hcoll : (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 := hsrc.1.trans hsrc.2.symm
  have hcross := forward_reverse_collision_cross_active_flip_colors
    C exponent hexp honeLoss x y hcoll
  change cf ∈ retainedActive C q.1.1 ∧
    cr ∈ retainedActive C p.1.2 at hcross
  have hci : cr ∉ retainedActive C q.1.1 :=
    (strictDescentRigidPairColor_spec
      C exponent hexp honeLoss q).2
  have hcf : cf ∉ retainedActive C p.1.2 :=
    (transportablePairColor_spec C p).2
  have hwB : s.1 ∈ retainedCompletionWords C q.1.1 := by
    rw [← hsrc.2]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  have hwV : s.1 ∈ retainedCompletionWords C p.1.2 := by
    rw [← hsrc.1]
    exact transportableHardWordToSingletonOrSoft_mem_upper C x
  have hne : cf ≠ cr :=
    net_collision_certified_forward_reverse_colours_distinct
      C exponent hexp honeLoss s
  have hd : d = flipCompletionWord cf (flipCompletionWord cr s.1) := rfl
  constructor
  · rw [hd]
    exact two_flip_one_active_one_inactive_exact_violation
      C q.1.1 cf cr s.1 hcross.1 hci hwB
  · rw [hd, flipCompletionWord_comm cf cr s.1 hne]
    exact two_flip_one_active_one_inactive_exact_violation
      C p.1.2 cr cf s.1 hcross.2 hcf hwV

#print axioms two_flip_one_active_one_inactive_exact_violation
#print axioms net_collision_certified_diagonal_exact_two_endpoint_shells

end OrderedEdgeColoring
end JSP000404Research
