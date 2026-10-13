import JSP000404Research.ResidualTwoFlipOppositeBitBlocker
import Mathlib.Tactic

/-!
# Exact targeted TRUE-hole versus opposite-bit blocker ledger

The existing bridge-overlap upper bound used the entire region outside
two endpoint cubes as a possible true-hole outlet, retaining ALL
externally covered words as a potential deficit.

We now choose the two actual cross-active flip colours cf,cr and
count only the corresponding DOUBLE-FLIPPED DIAGONAL IMAGE.
The map is globally injective. Its image partitions EXACTLY into:
  H_diag = image INTER true global Boolean holes;
  K_diag = image INTER global covered words.

Thus
  card(Q_b INTER Q_v) = card(H_diag) + card(K_diag).

Every word in K_diag is covered by a distinct external centre c
whose active palette and retained bit present one of two
explicit OPPOSITE-BIT blockers.

The deficit |K_diag| is sharper than the entire externally
covered two-cube exterior (whose many words may never occur as a
double-flip image). No assumption that K_diag vanishes is made.

This is a deterministic, local exact image accounting device,
NOT a global disjoint allocation across different bridge pairs
and NOT a proof of the sole WIP geometric payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def twoFlipBridgeDiagonalWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n) : Finset (Fin n → Bool) :=
  (retainedCompletionWords C b ∩ retainedCompletionWords C v).image
    (fun w => flipCompletionWord cf (flipCompletionWord cr w))

noncomputable def twoFlipBridgeTrueHoleWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n) : Finset (Fin n → Bool) :=
  twoFlipBridgeDiagonalWords C b v cf cr ∩
    ((Finset.univ : Finset (Fin n → Bool)) \
      coveredCompletionWords C)

noncomputable def twoFlipBridgeBlockedWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n) : Finset (Fin n → Bool) :=
  twoFlipBridgeDiagonalWords C b v cf cr ∩
    coveredCompletionWords C

/-- The exact source mass is partitioned into REAL hole diagonals
and precisely those COVERED diagonal words requiring an external
opposite-bit blocker. There is no coarse exterior overcounting. -/
theorem two_flip_bridge_overlap_card_eq_true_hole_add_blocked
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n) :
    (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card =
      (twoFlipBridgeTrueHoleWords C b v cf cr).card +
        (twoFlipBridgeBlockedWords C b v cf cr).card := by
  classical
  let D := twoFlipBridgeDiagonalWords C b v cf cr
  let K := coveredCompletionWords C
  let H := (Finset.univ : Finset (Fin n → Bool)) \ K
  have hpart : D = (D ∩ H) ∪ (D ∩ K) := by
    ext word
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hdisj : Disjoint (D ∩ H) (D ∩ K) := by
    apply Finset.disjoint_left.mpr
    intro word hwH hwK
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwH).2).2
      (Finset.mem_inter.mp hwK).2
  have hcardD : D.card =
      (D ∩ H).card + (D ∩ K).card := by
    calc
      D.card = ((D ∩ H) ∪ (D ∩ K)).card := by rw [← hpart]
      _ = (D ∩ H).card + (D ∩ K).card :=
        Finset.card_union_of_disjoint hdisj
  have hsource : D.card =
      (retainedCompletionWords C b ∩
        retainedCompletionWords C v).card := by
    unfold D twoFlipBridgeDiagonalWords
    rw [Finset.card_image_of_injective _
      (double_flip_completion_word_injective cf cr)]
  change D.card = (D ∩ H).card + (D ∩ K).card at *
  omega

/-- Only globally covered words IN THE ACTUAL double-flip image
can obstruct a true-hole payment. The full exterior-cover mass
from the older ledger is a potentially much looser upper bound. -/
theorem two_flip_bridge_overlap_le_global_holes_add_targeted_blocked
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n) :
    (retainedCompletionWords C b ∩
      retainedCompletionWords C v).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (twoFlipBridgeBlockedWords C b v cf cr).card := by
  have hsplit :=
    two_flip_bridge_overlap_card_eq_true_hole_add_blocked
      C b v cf cr
  have hsub :
      (twoFlipBridgeTrueHoleWords C b v cf cr).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card := by
    apply Finset.card_le_card
    intro w hw
    exact (Finset.mem_inter.mp hw).2
  omega

/-- EACH targeted blocker admits an actual source word in the two
endpoint overlap and a covering external third centre with an
OPPOSITE-BIT signature at one of the selected flip coordinates. -/
theorem two_flip_bridge_blocked_has_opposite_bit_external_centre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b v : V) (cf cr : Fin n)
    (hbv : b ≠ v)
    (hcfB : cf ∈ retainedActive C b)
    (hcrB : cr ∉ retainedActive C b)
    (hcrV : cr ∈ retainedActive C v)
    {d : Fin n → Bool}
    (hd : d ∈ twoFlipBridgeBlockedWords C b v cf cr) :
    ∃ w : Fin n → Bool,
      w ∈ retainedCompletionWords C b ∩
        retainedCompletionWords C v ∧
      flipCompletionWord cf (flipCompletionWord cr w) = d ∧
      ∃ c : V, c ≠ b ∧ c ≠ v ∧
        d ∈ retainedCompletionWords C c ∧
        ((cr ∈ retainedActive C c ∧
            retainedBit C c cr = !(retainedBit C v cr)) ∨
          (cf ∈ retainedActive C c ∧
            retainedBit C c cf = !(retainedBit C b cf))) := by
  classical
  have hdiag : d ∈ twoFlipBridgeDiagonalWords C b v cf cr :=
    (Finset.mem_inter.mp hd).1
  have hcover : d ∈ coveredCompletionWords C :=
    (Finset.mem_inter.mp hd).2
  unfold twoFlipBridgeDiagonalWords at hdiag
  obtain ⟨w,hw,hwd⟩ := Finset.mem_image.mp hdiag
  have houtside :=
    two_flip_diagonal_outside_bridge_endpoints
      C b v cf cr w hcfB hcrB hcrV
        (Finset.mem_inter.mp hw).1
        (Finset.mem_inter.mp hw).2
  have hdB : d ∉ retainedCompletionWords C b := by
    rw [← hwd]
    exact houtside.1
  have hdV : d ∉ retainedCompletionWords C v := by
    rw [← hwd]
    exact houtside.2
  have hext :=
    (two_cube_exterior_covered_iff_external_centre
      C b v d hdB hdV).mp hcover
  obtain ⟨c,hcb,hcv,hc⟩ := hext
  have hsource :
      flipCompletionWord cf (flipCompletionWord cr w) ∈
        retainedCompletionWords C c := by
    rw [hwd]
    exact hc
  have hob :=
    two_flip_diagonal_external_blocker_opposite_bit
      C b v c cf cr w hbv hcfB hcrB hcrV
        (Finset.mem_inter.mp hw).1
        (Finset.mem_inter.mp hw).2
        hsource
  exact ⟨w,hw,hwd,c,hcb,hcv,hc,hob⟩

#print axioms two_flip_bridge_overlap_card_eq_true_hole_add_blocked
#print axioms two_flip_bridge_overlap_le_global_holes_add_targeted_blocked
#print axioms two_flip_bridge_blocked_has_opposite_bit_external_centre

end OrderedEdgeColoring
end JSP000404Research
