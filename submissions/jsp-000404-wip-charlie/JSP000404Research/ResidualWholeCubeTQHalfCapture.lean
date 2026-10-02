import JSP000404Research.ResidualWholeCubeTQActiveOrOutward
import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Half-capture bound for the non-palette-growth T/Q branch

Fix a whole-cube pair (s,v,c) and a distinct active continuation coordinate d
at v.  Let w be a completion blocker of words in T_d(v).

If c is inactive at w, every captured source word y in

  T_d(v) ∩ Q_w

brings along flip_c(y) in Q_w, by whole-cube propagation.  Since c is active
at v and c != d, flipping c exits the translated slice T_d(v).  Thus the
captured source set and its c-flipped image are disjoint subsets of Q_w.

The flip is injective, so

  2 * |T_d(v) ∩ Q_w| <= |Q_w|.

For a second-layer projected-loss blocker w this becomes a dyadic half-capture
bound relative to a completion cube of size 2^(n-3).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem flip_other_active_not_mem_translated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcd : c ≠ d)
    (hword :
      word ∈ translatedCompletionWords C v d) :
    flipBoolWordAt word c ∉
      translatedCompletionWords C v d := by
  intro hflipT
  have hbase :
      flipBoolWordAt word d ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d word).1 hword
  have hflipBase :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d
      (flipBoolWordAt word c)).1 hflipT
  have hcomm :
      flipBoolWordAt (flipBoolWordAt word c) d =
        flipBoolWordAt (flipBoolWordAt word d) c := by
    exact flipBoolWordAt_commute word hcd
  rw [hcomm] at hflipBase
  exact flip_active_not_mem_completion C hbase hc hflipBase

noncomputable def wholeCubeTQCapturedWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v w : V) (d : Fin n) : Finset (Fin n → Bool) :=
  translatedCompletionWords C v d ∩
    retainedCompletionWords C w

theorem wholeCubeTQCapturedWords_flip_subset_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    (hcW : c ∉ retainedActive C w) :
    (wholeCubeTQCapturedWords C v w d).image
        (fun word => flipBoolWordAt word c)
      ⊆
    retainedCompletionWords C w := by
  intro z hz
  obtain ⟨word,hwordCap,rfl⟩ := Finset.mem_image.mp hz
  have hparts := Finset.mem_inter.mp hwordCap
  exact
    (wholeCube_TQ_inactive_owner_propagates_to_partner_translation
      C hcV hdV hdc hwhole hcW hparts.1 hparts.2).2

theorem wholeCubeTQCapturedWords_disjoint_flip_image
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hcd : c ≠ d) :
    Disjoint
      (wholeCubeTQCapturedWords C v w d)
      ((wholeCubeTQCapturedWords C v w d).image
        (fun word => flipBoolWordAt word c)) := by
  classical
  rw [Finset.disjoint_left]
  intro word hcap hflipImage
  obtain ⟨base,hbaseCap,hbaseFlip⟩ :=
    Finset.mem_image.mp hflipImage
  have hwordT :=
    (Finset.mem_inter.mp hcap).1
  have hbaseT :=
    (Finset.mem_inter.mp hbaseCap).1
  have heq : flipBoolWordAt base c = word := hbaseFlip
  rw [← heq] at hwordT
  exact flip_other_active_not_mem_translated
    C hcV hcd hbaseT hwordT

theorem wholeCubeTQ_inactive_owner_two_mul_capture_le_completion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    (hcW : c ∉ retainedActive C w) :
    2 * (wholeCubeTQCapturedWords C v w d).card
      ≤
    (retainedCompletionWords C w).card := by
  classical
  let S := wholeCubeTQCapturedWords C v w d
  let F := S.image (fun word => flipBoolWordAt word c)
  have hFcard : F.card = S.card := by
    dsimp [F]
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact flipBoolWordAt_injective c hab
  have hdisj : Disjoint S F := by
    exact wholeCubeTQCapturedWords_disjoint_flip_image
      C hcV hdc.symm
  have hsubS :
      S ⊆ retainedCompletionWords C w := by
    intro word hword
    exact (Finset.mem_inter.mp hword).2
  have hsubF :
      F ⊆ retainedCompletionWords C w := by
    exact wholeCubeTQCapturedWords_flip_subset_completion
      C hcV hdV hdc hwhole hcW
  have hunionSub :
      S ∪ F ⊆ retainedCompletionWords C w := by
    intro word hword
    rcases Finset.mem_union.mp hword with hs | hf
    · exact hsubS hs
    · exact hsubF hf
  have hcardSub := Finset.card_le_card hunionSub
  rw [Finset.card_union_of_disjoint hdisj,hFcard] at hcardSub
  omega

theorem wholeCubeTQ_inactive_secondLayer_capture_half
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    (hcW : c ∉ retainedActive C w)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hwSecond : exponent w = n - 2) :
    2 * (wholeCubeTQCapturedWords C v w d).card
      ≤
    2 ^ (n - 3) := by
  have hbase :=
    wholeCubeTQ_inactive_owner_two_mul_capture_le_completion
      C hcV hdV hdc hwhole hcW
  have hloss :=
    (mem_projectedLossVertices C exponent w).1 hwLoss
  have hfree : projectedFree C w = n - 3 := by
    rw [hwSecond] at hloss
    omega
  rw [retainedCompletionWords_card,hfree] at hbase
  exact hbase

#print axioms flip_other_active_not_mem_translated
#print axioms wholeCubeTQ_inactive_owner_two_mul_capture_le_completion
#print axioms wholeCubeTQ_inactive_secondLayer_capture_half

end OrderedEdgeColoring
end JSP000404Research
