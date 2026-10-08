import JSP000404Research.DirectionDataOneLayerProfileAnyWidth
import JSP000404Research.ResidualLossAnyPairExpansion
import Mathlib.Tactic

/-!
# No two-centre weighted Hall obstruction containing a true projected loss

An exact projected-loss centre in DirectionData is tight and
residual-inactive, and must contain two distinct adjacent retained
active coordinates. Its loss exponent therefore satisfies k(v) < n:
the seemingly possible top-layer case k(v)=n is excluded by a
genuine phase-slip geometry certificate.

The global n-bit one-layer profile is also guaranteed by the
nonempty local direction cycles, without external assumptions.

We combine these observations with the previously proved enlarged
candidate-pair expansion. For EVERY other vertex w (loss or non-loss,
including those with exponent n), the two-vertex target weighted
capacity is bounded by the union of enlarged candidate blocks:

  2^k(v) + 2^k(w) <= |B(v) union B(w)|.

Thus no deficient weighted Hall set of cardinality two can contain
a true projected-loss vertex. This does not exclude larger Hall
obstructions or prove the full n-bit inequality.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- In any valid direction cycle, an exact projected-loss centre has
strictly sub-top exponent: its two different retained active colours
force the projected free dimension to be at most n-2. -/
theorem projected_loss_exponent_lt_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (i : V)
    (hloss :
      i ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent)) :
    (cycles i).exponent < n := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  obtain ⟨c, d, hadj, hc, hd⟩ :=
    projected_loss_has_adjacent_retained_bands
      D ht cycles i hloss
  have hcd : c ≠ d := by
    intro heq
    have heqval := congrArg Fin.val heq
    omega
  have hsub : ({c, d} : Finset (Fin n)) ⊆ retainedActive B i := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hc
    · exact hd
  have hsmallCard : 2 ≤ (retainedActive B i).card := by
    have hcard := Finset.card_le_card hsub
    have hpair : ({c, d} : Finset (Fin n)).card = 2 := by
      simp [hcd]
    omega
  have hfree :
      (cycles i).exponent = projectedFree B i + 1 :=
    (mem_projectedLossVertices B
      (fun j => (cycles j).exponent) i).1 hloss
  dsimp [projectedFree] at hfree
  omega

/-- The target weight of any loss vertex plus ANY other vertex is
covered by their two enlarged Boolean candidate blocks. This
eliminates the global forall-exponent-less-than-n condition used in
the earlier abstract pair-expansion theorem. -/
theorem projected_loss_any_pair_enlarged_expands
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (v w : V)
    (hvw : v ≠ w)
    (hvloss :
      v ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent)) :
    let B := standardResidualColoring D n
      (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    2 ^ k v + 2 ^ k w ≤
      (enlargedProjectedCandidateBlock B k v ∪
       enlargedProjectedCandidateBlock B k w).card := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hprofile :=
    localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ x, k x ≤ n := hprofile.1
  have hone :
      ∀ x, (active B x).card ≤ n - k x + 1 := hprofile.2
  have hvLt : k v < n :=
    projected_loss_exponent_lt_n D ht cycles v hvloss
  by_cases hwLoss : w ∈ projectedLossVertices B k
  · have hwLt : k w < n :=
      projected_loss_exponent_lt_n D ht cycles w hwLoss
    exact two_projectedLoss_enlarged_blocks_expand
      B k hexp hone hvloss hwLoss hvLt hwLt hvw
  · exact projectedLoss_with_nonloss_enlarged_pair_expands
      B k hexp hone hvloss hwLoss hvLt hvw

/-- There is no weighted Hall deficiency on any two-element source
set containing one true projected-loss centre. -/
theorem no_two_vertex_deficiency_containing_true_projected_loss
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    {v w : V}
    (hvw : v ≠ w)
    (hvloss :
      v ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent)) :
    let B := standardResidualColoring D n
      (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    ¬ BlockDeficient
      (fun i => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k)
      {v, w} := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  change ¬ BlockDeficient
    (fun i => 2 ^ k i)
    (enlargedProjectedCandidateBlock B k)
    ({v, w} : Finset V)
  intro hbad
  unfold BlockDeficient at hbad
  have hbound :=
    projected_loss_any_pair_enlarged_expands
      D ht cycles v w hvw hvloss
  have hsum :
      (∑ x ∈ ({v, w} : Finset V), 2 ^ k x) =
        2 ^ k v + 2 ^ k w := by
    simp [hvw]
  have hunion :
      (({v, w} : Finset V).biUnion
        (enlargedProjectedCandidateBlock B k)) =
      enlargedProjectedCandidateBlock B k v ∪
        enlargedProjectedCandidateBlock B k w := by
    ext word
    simp
  rw [hsum, hunion] at hbad
  omega

#print axioms projected_loss_exponent_lt_n
#print axioms projected_loss_any_pair_enlarged_expands
#print axioms no_two_vertex_deficiency_containing_true_projected_loss

end DirectionData
end JSP000404Research
