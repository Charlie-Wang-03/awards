import JSP000404Research.ResidualNetCollisionDoubleShellBridge
import Mathlib.Tactic

/-!
# Target-dependent double-shell bridge fibres of ACTUAL NET collisions

For a FIXED candidate opposite diagonal d, not all source-compatible
soft bridges can produce it. A genuine bridge r=(b,v) must satisfy:

  * exactly one retained active-bit violation at b;
  * exactly one retained active-bit violation at v;
  * b's violated coordinate is inactive at v;
  * v's violated coordinate is inactive at b.

These are exact necessary properties of the source-certified two
flip colours, with no assumed full planar matching. We filter
the previously known doubly constrained source bridge carriers
accordingly and inject the genuine source fibre of d into THAT
target-dependent eligible set.

The eligible set remains a COVERED soft-bridge carrier set, not a
count of true Boolean holes or unreserved profile surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Source-native target-dependent soft bridge candidate pool. The
one violated retained bit at each endpoint MUST be one of its own
EXCLUSIVE active coordinates. -/
noncomputable def targetDoubleShellTwoBitBridgeCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) : Finset (V × V) :=
  (twoBitDisagreementBridgeCarriers C exponent).filter
    (fun r =>
      (retainedActiveViolationCoords C r.1 d).card = 1 ∧
      (retainedActiveViolationCoords C r.2 d).card = 1 ∧
      retainedActiveViolationCoords C r.1 d ⊆
        retainedActive C r.1 \ retainedActive C r.2 ∧
      retainedActiveViolationCoords C r.2 d ⊆
        retainedActive C r.2 \ retainedActive C r.1)

/-- Every real NET source's certified original soft bridge belongs
to the DOUBLE-SHELL filtered pool for its ACTUAL diagonal target. -/
theorem net_collision_bridge_owner_mem_target_double_shell
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s ∈
      targetDoubleShellTwoBitBridgeCarriers
        C exponent (netCollisionCertifiedDiagonal
          C exponent hexp honeLoss s) := by
  classical
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  have hshell :=
    net_collision_certified_diagonal_exact_two_endpoint_shells
      C exponent hexp honeLoss s
  change retainedActiveViolationCoords C q.1.1 d = {cf} ∧
    retainedActiveViolationCoords C p.1.2 d = {cr} at hshell
  have hsrc := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss s
  have hcoll :
    (transportableHardWordToSingletonOrSoft C x).1 =
    (strictDescentRigidWordToSingletonOrSoft
      C exponent hexp honeLoss y).1 :=
    hsrc.1.trans hsrc.2.symm
  have hcross :=
    forward_reverse_collision_cross_active_flip_colors
      C exponent hexp honeLoss x y hcoll
  change cf ∈ retainedActive C q.1.1 ∧
    cr ∈ retainedActive C p.1.2 at hcross
  have hcf : cf ∉ retainedActive C p.1.2 :=
    (transportablePairColor_spec C p).2
  have hcr : cr ∉ retainedActive C q.1.1 :=
    (strictDescentRigidPairColor_spec
      C exponent hexp honeLoss q).2
  have hbridge : (q.1.1,p.1.2) ∈
      twoBitDisagreementBridgeCarriers C exponent :=
    net_collision_certified_bridge_owner_mem_two_bit_carriers
      C exponent hexp honeLoss s
  change (q.1.1,p.1.2) ∈
    targetDoubleShellTwoBitBridgeCarriers C exponent d
  apply Finset.mem_filter.mpr
  refine ⟨hbridge, ?_, ?_, ?_, ?_⟩
  · simp [hshell.1]
  · simp [hshell.2]
  · rw [hshell.1]
    intro e he
    have hecf : e = cf := Finset.mem_singleton.mp he
    subst e
    exact Finset.mem_sdiff.mpr ⟨hcross.1, hcf⟩
  · rw [hshell.2]
    intro e he
    have hecr : e = cr := Finset.mem_singleton.mp he
    subst e
    exact Finset.mem_sdiff.mpr ⟨hcross.2, hcr⟩

/-- The actual fixed-diagonal source fibre has at most as many
elements as the TRUE target-specific double-shell compatible original
soft bridge candidates, not all candidate bridges. -/
theorem net_collision_fixed_diagonal_fibre_card_le_target_double_shell
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤
    (targetDoubleShellTwoBitBridgeCarriers C exponent d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let P := targetDoubleShellTwoBitBridgeCarriers C exponent d
  let f : {s : S // s ∈ F} → V × V :=
    fun s => netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss s.1
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hx : netCollisionCertifiedDiagonal C exponent hexp honeLoss x.1 =
        d := (Finset.mem_filter.mp x.2).2
    have hy : netCollisionCertifiedDiagonal C exponent hexp honeLoss y.1 =
        d := (Finset.mem_filter.mp y.2).2
    exact net_collision_same_bridge_same_diagonal_source_eq
      C exponent hexp honeLoss x.1 y.1 (hx.trans hy.symm) h
  have hsub : (Finset.univ : Finset {s : S // s ∈ F}).image f ⊆ P := by
    intro r hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
    have hs := net_collision_bridge_owner_mem_target_double_shell
      C exponent hexp honeLoss s.1
    have heq : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 =
        d := (Finset.mem_filter.mp s.2).2
    simpa only [heq] using hs
  change F.card ≤ P.card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ P.card := Finset.card_le_card hsub

/-- Each target-dependent double-shell pool is a subset of the
unfiltered source-compatible two-bit soft bridge carrier pool.
Thus the target-dependent fibre cap is NEVER weaker. -/
theorem target_double_shell_bridge_carriers_subset_two_bit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) :
    targetDoubleShellTwoBitBridgeCarriers C exponent d ⊆
      twoBitDisagreementBridgeCarriers C exponent := by
  intro r hr
  exact (Finset.mem_filter.mp hr).1

/-- A sharpened conditional debt-zero criterion: it is enough
that EACH ACTUALLY HIT target has at most ONE target-compatible
double-shell soft bridge. Crucially this is weaker than asking for
at most one potential bridge in the entire system; it is NOT
currently established unconditionally by planar AngleCap. -/
theorem net_collision_duplicate_debt_zero_of_target_double_shell_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hunique : ∀ d ∈ netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss,
      (targetDoubleShellTwoBitBridgeCarriers C exponent d).card ≤ 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_eq_zero
  intro d hd
  have hle := net_collision_fixed_diagonal_fibre_card_le_target_double_shell
    C exponent hexp honeLoss d
  have hone := hunique d hd
  omega


/-- A GLOBAL exact-debt upper bound by TARGET-SPECIFIC eligible
bridge excess. Unlike the former uniform choose-two/product bounds,
this local-to-global sum preserves the actual hole/covered target
partition without reusing a single target as a new hole credit. -/
theorem net_collision_duplicate_debt_le_sum_target_double_shell_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        ((targetDoubleShellTwoBitBridgeCarriers C exponent d).card - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have h := net_collision_fixed_diagonal_fibre_card_le_target_double_shell
    C exponent hexp honeLoss d
  omega

/-- A strictly quantified target-specific geometric obstruction:
positive actual duplicate debt FORCES some actually hit canonical
target to admit at least TWO distinct doubly-filtered compatible
original soft bridge candidates. It does NOT claim these candidate
bridges are false holes, nor that planar AngleCap rules them out. -/
theorem net_collision_positive_duplicate_forces_two_target_double_shell_bridges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    ∃ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      2 ≤ (targetDoubleShellTwoBitBridgeCarriers C exponent d).card := by
  classical
  by_contra hno
  have hunique : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      (targetDoubleShellTwoBitBridgeCarriers C exponent d).card ≤ 1 := by
    intro d hd
    by_contra hbad
    have htwo : 2 ≤ (targetDoubleShellTwoBitBridgeCarriers
        C exponent d).card := by omega
    exact hno ⟨d, hd, htwo⟩
  have hz := net_collision_duplicate_debt_zero_of_target_double_shell_unique
    C exponent hexp honeLoss hunique
  omega

#print axioms net_collision_duplicate_debt_le_sum_target_double_shell_excess
#print axioms net_collision_positive_duplicate_forces_two_target_double_shell_bridges

#print axioms net_collision_bridge_owner_mem_target_double_shell
#print axioms net_collision_fixed_diagonal_fibre_card_le_target_double_shell
#print axioms target_double_shell_bridge_carriers_subset_two_bit
#print axioms net_collision_duplicate_debt_zero_of_target_double_shell_unique

end OrderedEdgeColoring
end JSP000404Research
