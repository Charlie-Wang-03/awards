import JSP000404Research.BinaryEdgePartition
import JSP000404Research.ResidualBipartite
import Mathlib.Tactic

/-!
# Residual-edge merging at the Boolean-bit level

Keeping an OrderedEdgeColoring after eliminating the residual colour is
stronger than necessary.  For the final Hansel/Kraft argument we only need a
BinaryEdgePartition.

Let C be an ordered colouring with n+1 colours, with the last colour treated
as residual.  Retain the canonical incoming/outgoing bits of the first n
colours.

If every residual edge u<v is already separated by at least one retained bit,
then choose any such retained colour for that edge.  Old retained edges keep
their old colour.  This immediately produces a BinaryEdgePartition with only
n colours.

The genuinely difficult residual edges are therefore exactly those whose
endpoints agree on every retained bit.  They are "vertical pairs" in the
(n+1)-bit standard code.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Canonical Boolean bit of a retained old colour. -/
noncomputable def retainedBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    V → Fin n → Bool :=
  fun v c => bit C v c.castSucc

/-- Two vertices are separated by at least one retained old bit. -/
def RetainedSeparated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) (u v : V) : Prop :=
  ∃ c : Fin n, retainedBit C u c ≠ retainedBit C v c

/-- The old colour of a retained increasing edge separates its endpoints on
the corresponding retained bit. -/
theorem retainedBit_ne_of_retained_edge
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} (huv : u < v)
    (hret : (C.color u v).val < n) :
    retainedBit C u (retainedColor C u v hret) ≠
      retainedBit C v (retainedColor C u v hret) := by
  unfold retainedBit
  have hcu :
      (retainedColor C u v hret).castSucc = C.color u v := by
    apply Fin.ext
    simp [retainedColor]
  rw [hcu]
  -- The canonical incoming bit of an edge colour is false at its lower
  -- endpoint and true at its upper endpoint.
  have hin_v : incoming C (C.color u v) v := ⟨u, huv, rfl⟩
  have hnotin_u : ¬ incoming C (C.color u v) u := by
    rintro ⟨a, hau, hac⟩
    apply C.noMonoTwoPath hau huv
    simpa using hac
  simp [bit, hnotin_u, hin_v]

/-- If every residual increasing edge is separated by some retained bit, the
residual colour can be eliminated at the weaker BinaryEdgePartition level. -/
noncomputable def binaryPartitionOfResidualSeparated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hn : 0 < n)
    (hsep : ∀ {u v : V}, u < v → IsResidual C u v →
      RetainedSeparated C u v) :
    BinaryEdgePartition V n := by
  classical
  let target : V → V → Fin n := fun u v =>
    if h : u < v ∧ IsResidual C u v then
      Classical.choose (hsep h.1 h.2)
    else
      ⟨0, hn⟩
  refine
    { edgeColor := fun u v =>
        if hret : (C.color u v).val < n then
          retainedColor C u v hret
        else
          target u v
      bit := retainedBit C
      proper := ?_ }
  intro u v huv
  by_cases hret : (C.color u v).val < n
  · simp only [dif_pos hret]
    exact retainedBit_ne_of_retained_edge C huv hret
  · simp only [dif_neg hret]
    have hres : IsResidual C u v := hret
    have ht :
        retainedBit C u (target u v) ≠ retainedBit C v (target u v) := by
      unfold target
      simp only [dif_pos ⟨huv, hres⟩]
      exact Classical.choose_spec (hsep huv hres)
    exact ht

/-- Ordinary 2^n capacity follows immediately once all residual edges are
retained-bit separated. -/
theorem card_le_two_pow_of_residual_separated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hn : 0 < n)
    (hsep : ∀ {u v : V}, u < v → IsResidual C u v →
      RetainedSeparated C u v) :
    Fintype.card V ≤ 2 ^ n :=
  BinaryEdgePartition.card_le_two_pow
    (binaryPartitionOfResidualSeparated C hn hsep)

/-- Failure of retained separation means equality of all retained bits. -/
theorem not_retainedSeparated_iff
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) (u v : V) :
    ¬ RetainedSeparated C u v ↔
      ∀ c : Fin n, retainedBit C u c = retainedBit C v c := by
  unfold RetainedSeparated
  push_neg
  rfl

#print axioms retainedBit_ne_of_retained_edge
#print axioms binaryPartitionOfResidualSeparated
#print axioms card_le_two_pow_of_residual_separated
#print axioms not_retainedSeparated_iff

end OrderedEdgeColoring
end JSP000404Research
