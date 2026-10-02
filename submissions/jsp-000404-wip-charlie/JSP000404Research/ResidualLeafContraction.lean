import JSP000404Research.ResidualEnlargedLossDegree
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Well-founded leaf contraction for enlarged Hall cores

A leaf of an inclusion-minimal deficient enlarged-candidate core can be
deleted and its exact deleted-vertex transfer moved to its unique parent.
The resulting weighted Hall state is still deficient, has the same
deficiency amount, and has strictly fewer vertices.

This is the well-founded state transition needed to consume the final
two-leaf graph terminal.  The original dyadic profile is used only to
construct and bound the first transfer; the contracted state itself is a
general weighted Hall state.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

structure LeafContractionState
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v w : V) : Prop where
  hvT : v ∈ T
  hwT : w ∈ T
  hvw : v ≠ w
  hunique :
    ∀ z : V,
      z ∈ T →
      z ≠ v →
      EnlargedBlocksCross C exponent v z →
      z = w

def contractedLeafDemand
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v w : V) : V → ℕ :=
  addDemandAt
    (fun x => 2 ^ exponent x)
    w
    (deletedVertexTransfer
      (fun x => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T v)

theorem leaf_contraction_deficient_preserves_amount
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v w : V}
    (hstate : LeafContractionState C exponent T v w) :
    BlockDeficient
      (contractedLeafDemand C exponent T v w)
      (enlargedProjectedCandidateBlock C exponent)
      (T.erase v)
    ∧
    blockDeficiencyAmount
      (contractedLeafDemand C exponent T v w)
      (enlargedProjectedCandidateBlock C exponent)
      (T.erase v)
      =
    blockDeficiencyAmount
      (fun x => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T
    ∧
    (T.erase v).card < T.card
    ∧
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
      (retainedCompletionWords C w).card := by
  have hwErase : w ∈ T.erase v :=
    Finset.mem_erase.mpr ⟨hstate.hvw.symm,hstate.hwT⟩
  have hpres :=
    minimal_deficient_delete_with_transfer_preserves_amount
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hstate.hvT hwErase
  have hbound :=
    minimal_enlargedCandidate_prune_any_leaf_to_parent
      C exponent hexpLt hexp honeLoss
      hdef hmin
      hstate.hvT hstate.hwT hstate.hvw hstate.hunique
  have hcard :
      (T.erase v).card < T.card := by
    rw [Finset.card_erase_of_mem hstate.hvT]
    have hpos : 0 < T.card := Finset.card_pos.mpr ⟨v,hstate.hvT⟩
    omega
  exact ⟨
    by simpa [contractedLeafDemand] using hpres.1,
    by simpa [contractedLeafDemand] using hpres.2,
    hcard,
    by simpa [contractedLeafDemand] using hbound.2
  ⟩

/-- Every concrete leaf outlet emitted by the collision-tree root has an
actual well-founded contraction step to its recorded parent. -/
theorem enlargedLeafOutlet_has_contraction
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    ∃ demand' : V → ℕ,
      BlockDeficient
        demand'
        (enlargedProjectedCandidateBlock C exponent)
        (T.erase v)
      ∧
      blockDeficiencyAmount
        demand'
        (enlargedProjectedCandidateBlock C exponent)
        (T.erase v)
        =
      blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T
      ∧
      (T.erase v).card < T.card
      ∧
      deletedVertexTransfer
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ≤
        (retainedCompletionWords C w).card := by
  let hstate : LeafContractionState C exponent T v w :=
    ⟨hvT,hwT,hvw,hunique⟩
  refine ⟨contractedLeafDemand C exponent T v w,?_⟩
  exact leaf_contraction_deficient_preserves_amount
    C exponent hexpLt hexp honeLoss
    hdef hmin hstate

#print axioms leaf_contraction_deficient_preserves_amount
#print axioms enlargedLeafOutlet_has_contraction

end OrderedEdgeColoring
end JSP000404Research
