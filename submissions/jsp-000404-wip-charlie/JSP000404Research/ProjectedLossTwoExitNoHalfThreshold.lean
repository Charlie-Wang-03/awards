import JSP000404Research.ExactProjectedLossIffTightInactive
import JSP000404Research.ResidualSingleFibreBranching
import Mathlib.Tactic

/-!
# Two independent Boolean exits from every projected loss

The exact projected-loss iff tight-and-residual-inactive theorem eliminates
the previously required special half-unit fractional-width restriction.

For any valid ordered DirectionData of width t < n+1, every projected-loss
centre has two consecutive retained active coordinates c,c+1.

Its retained completion cube is isolated from every other vertex cube,
since ANY shared completion word would force a residual edge incident to
this residual-inactive centre. Therefore each completion word is singly
covered, without globally assuming a one-layer budget at every vertex.

The two coordinate flips of EVERY word in this loss cube have disjoint
completion blocker fibres. If both exits are blocked, their blockers
must be distinct vertices. Otherwise one exit is a genuine Boolean hole.

These pointwise facts are unconditional for the stated local loss.
They do not assert a global injection across different source words.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- All completion words of a residual-inactive vertex have unique
carrier. This needs no exponent profile or global local-budget bounds. -/
theorem single_completion_of_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    {i : V}
    (hinactive : residualCoord n ∉ active B i)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords B i) :
    IsSingleCompletionWord B i word := by
  refine ⟨hword, ?_⟩
  intro w hw
  by_contra hwi
  have hiw : i ≠ w := Ne.symm hwi
  rcases retainedCompletion_overlap_forces_residual
      B hiw hword hw with hres | hres
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        B hres.1 hres.2).1
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        B hres.1 hres.2).2

#print axioms single_completion_of_residual_inactive
end OrderedEdgeColoring

namespace DirectionData

open OrderedEdgeColoring

/-- At ANY projected-loss centre for t < n+1, two adjacent
retained active colours yield disjoint one-bit-flip blocker fibres
for every word of the entire loss cube.

If neither flipped word is a hole, two different blocking vertices
must exist. In particular, a fixed blocker can never obstruct both
exits of a single source word. -/
theorem projected_loss_two_disjoint_flip_exits
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
    let B := standardResidualColoring D n
      (by exact_mod_cast ht)
    ∃ c d : Fin n,
      c.val + 1 = d.val ∧
      c ∈ retainedActive B i ∧
      d ∈ retainedActive B i ∧
      ∀ word : Fin n → Bool,
        word ∈ retainedCompletionWords B i →
          Disjoint
            (completionFibre B (flipBoolWordAt word c))
            (completionFibre B (flipBoolWordAt word d)) ∧
          ((completionFibre B (flipBoolWordAt word c)).card = 0 ∨
           (completionFibre B (flipBoolWordAt word d)).card = 0 ∨
           ∃ w z : V, w ≠ z ∧
             flipBoolWordAt word c ∈ retainedCompletionWords B w ∧
             flipBoolWordAt word d ∈ retainedCompletionWords B z) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  obtain ⟨c,d,hadj,hc,hd⟩ :=
    projected_loss_has_adjacent_retained_bands
      D ht cycles i hloss
  have hneq : c ≠ d := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hinactive : residualCoord n ∉ active B i :=
    (projected_loss_forces_tight_and_residual_inactive
      D ht cycles i hloss).2
  refine ⟨c, d, hadj, hc, hd, ?_⟩
  intro word hword
  have hsingle : IsSingleCompletionWord B i word :=
    single_completion_of_residual_inactive B hinactive hword
  have hdisj :
      Disjoint
        (completionFibre B (flipBoolWordAt word c))
        (completionFibre B (flipBoolWordAt word d)) :=
    two_single_flips_have_disjoint_blocker_fibres
      B hsingle hc hd hneq
  refine ⟨hdisj, ?_⟩
  by_cases hcHole :
      (completionFibre B (flipBoolWordAt word c)).card = 0
  · exact Or.inl hcHole
  · by_cases hdHole :
        (completionFibre B (flipBoolWordAt word d)).card = 0
    · exact Or.inr (Or.inl hdHole)
    · right
      right
      have hcPos :
          0 < (completionFibre B (flipBoolWordAt word c)).card := by
        omega
      have hdPos :
          0 < (completionFibre B (flipBoolWordAt word d)).card := by
        omega
      exact two_single_flips_nonempty_fibres_give_two_blockers
        B hsingle hc hd hneq
        (Finset.card_pos.mp hcPos)
        (Finset.card_pos.mp hdPos)

#print axioms projected_loss_two_disjoint_flip_exits

end DirectionData
end JSP000404Research
