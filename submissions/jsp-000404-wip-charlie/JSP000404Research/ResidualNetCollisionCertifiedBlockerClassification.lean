import JSP000404Research.ResidualNetCollisionCertifiedGlobalLedger
import Mathlib.Tactic

/-!
# Actual NET-collision diagonal blockers, with no externally chosen sources

The certified diagonal map uses the unique ORIGINAL forward hard
source and reverse strict-rigid source attached to every genuine
NET sink collision. We now transfer the earlier source/fifth-centre
IFF from a hand-provided collision witness to this canonical map.

This states the exact obstruction for the OBJECT USED IN THE GLOBAL
THREE-DEBT LEDGER, not merely a hypothetical pair of bridge cubes.
The "fifth centre" alternative has a certified opposite-bit
signature. No claim that it is geometrically impossible is made.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- On every actual NET collision, the canonical diagonal is
covered IFF one of its two ORIGINAL hard source endpoints
blocks the cross-flip, OR a fifth-or-later centre covers it
with the certified opposite-bit signature. -/
theorem net_collision_certified_diagonal_covered_iff_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
    let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
    d ∈ coveredCompletionWords C ↔
      (cr ∉ retainedActive C p.1.1 ∨
       cf ∉ retainedActive C q.1.2 ∨
       ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
         c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
         d ∈ retainedCompletionWords C c ∧
         ((cr ∈ retainedActive C c ∧
           retainedBit C c cr = !(retainedBit C p.1.2 cr)) ∨
          (cf ∈ retainedActive C c ∧
           retainedBit C c cf = !(retainedBit C q.1.1 cf)))) := by
  classical
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  have hsource :=
    net_collision_certified_sources_same_sink C exponent hexp honeLoss s
  have hfx : (transportableHardWordToSingletonOrSoft C x).1 = s.1 :=
    hsource.1
  have hry :
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 = s.1 :=
    hsource.2
  have hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 :=
    hfx.trans hry.symm
  have hiff :=
    actual_collision_diagonal_covered_iff_source_block_or_opposite_fifth
      C exponent hexp honeLoss x y hcollision
  change
    (flipCompletionWord cf
       (flipCompletionWord cr (transportableHardWordToSingletonOrSoft C x).1)
       ∈ coveredCompletionWords C) ↔
      (cr ∉ retainedActive C p.1.1 ∨
       cf ∉ retainedActive C q.1.2 ∨
       ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
         c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
         flipCompletionWord cf
           (flipCompletionWord cr
             (transportableHardWordToSingletonOrSoft C x).1)
             ∈ retainedCompletionWords C c ∧
         ((cr ∈ retainedActive C c ∧
           retainedBit C c cr = !(retainedBit C p.1.2 cr)) ∨
          (cf ∈ retainedActive C c ∧
           retainedBit C c cf = !(retainedBit C q.1.1 cf))))
       at hiff
  simpa only [hfx] using hiff

/-- Every DISTINCT certified diagonal that is already COVERED
has a genuine NET source collision and precisely one of the
two source-side blockers or an explicit fifth-centre
opposite-bit witness. This is the global BLOCKER debit's
witness decomposition, without treating covered targets
as actual Boolean holes. -/
theorem net_collision_certified_covered_has_concrete_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool)
    (hd : d ∈ netCollisionCertifiedCoveredDiagonals
      C exponent hexp honeLoss) :
    ∃ s : {word : Fin n → Bool //
        word ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss},
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d ∧
      (let x := netCollisionCertifiedForwardSource
        C exponent hexp honeLoss s
       let y := netCollisionCertifiedReverseSource
        C exponent hexp honeLoss s
       let p := transportableWordCarrier C x
       let q := strictDescentRigidWordCarrier C exponent y
       let cf := transportablePairColor C p
       let cr := strictDescentRigidPairColor
         C exponent hexp honeLoss q
       cr ∉ retainedActive C p.1.1 ∨
       cf ∉ retainedActive C q.1.2 ∨
       ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
         c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
         d ∈ retainedCompletionWords C c ∧
         ((cr ∈ retainedActive C c ∧
           retainedBit C c cr = !(retainedBit C p.1.2 cr)) ∨
          (cf ∈ retainedActive C c ∧
           retainedBit C c cf = !(retainedBit C q.1.1 cf)))) := by
  classical
  have hdimage : d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss :=
    (Finset.mem_inter.mp hd).1
  have hdcovered : d ∈ coveredCompletionWords C :=
    (Finset.mem_inter.mp hd).2
  unfold netCollisionCertifiedDiagonalWords at hdimage
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hdimage
  refine ⟨s, hs, ?_⟩
  have hiff :=
    net_collision_certified_diagonal_covered_iff_blocker
      C exponent hexp honeLoss s
  have hmember : netCollisionCertifiedDiagonal
      C exponent hexp honeLoss s ∈ coveredCompletionWords C := by
    rw [hs]
    exact hdcovered
  have hresult := hiff.mp hmember
  simpa only [hs] using hresult

#print axioms net_collision_certified_diagonal_covered_iff_blocker
#print axioms net_collision_certified_covered_has_concrete_blocker

end OrderedEdgeColoring
end JSP000404Research
