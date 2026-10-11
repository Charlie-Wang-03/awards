import JSP000404Research.ResidualSafeFlipCubeObstruction
import JSP000404Research.ResidualCompletionMultiplicity
import JSP000404Research.ResidualCompletionIntersection
import Mathlib.Tactic

/-!
# Overlap rewiring for oriented safe flips

A same-retained pair of distinct vertices always gives one doubly covered
retained code. An oriented safe flip moves this code out of the lower cube
and into the upper cube, without producing a Boolean hole.

Here we characterize the *only* two possibilities for its new multiplicity:
either the flipped word is singly covered at the upper endpoint, or it has
a new, distinct residual partner. Any such partner has a completion cube
disjoint from the original lower endpoint's cube.

This is a concrete overlap-transfer invariant, not yet the globally
injective overlap/defect payment needed for JSP-000404.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Two distinct vertices with identical retained canonical bits yield
an overlap word, independently of whether their cubes have other points. -/
theorem sameRetained_base_mem_overlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V)
    (hneq : a ≠ v)
    (hsame : SameRetained C a v) :
    (fun d => retainedBit C a d) ∈ overlapCompletionWords C := by
  classical
  let word : Fin n → Bool := fun d => retainedBit C a d
  have hboth := retained_base_mem_both_completionWords C hsame
  have ha : a ∈ completionFibre C word :=
    (mem_completionFibre C word a).2 (Finset.mem_inter.mp hboth).1
  have hv : v ∈ completionFibre C word :=
    (mem_completionFibre C word v).2 (Finset.mem_inter.mp hboth).2
  have hsub : ({a, v} : Finset V) ⊆ completionFibre C word := by
    intro w hw
    rcases Finset.mem_insert.mp hw with heq | hw'
    · simpa [heq] using ha
    · have hwv : w = v := Finset.mem_singleton.mp hw'
      simpa [hwv] using hv
  have htwo : ({a, v} : Finset V).card = 2 := by
    simp [hneq]
  have hle : 2 ≤ (completionFibre C word).card := by
    calc
      2 = ({a, v} : Finset V).card := htwo.symm
      _ ≤ (completionFibre C word).card := Finset.card_le_card hsub
  have hmax := completionFibre_card_le_two C word
  apply (mem_overlapCompletionWords C word).2
  omega

/-- The upper endpoint covers the flipped word. If no second cube covers
it, the completion-fibre cardinality is exactly one; otherwise a new
distinct residual edge must support its additional coverage. -/
theorem oriented_safe_flip_singleton_or_new_residual_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v) :
    (completionFibre C (flippedRetainedCode C a c)).card = 1 ∨
      ∃ w : V,
        w ≠ a ∧ w ≠ v ∧
        flippedRetainedCode C a c ∈ retainedCompletionWords C w ∧
        ((v < w ∧ IsResidual C v w) ∨
          (w < v ∧ IsResidual C w v)) := by
  classical
  let word := flippedRetainedCode C a c
  have hvcube : word ∈ retainedCompletionWords C v :=
    sameRetained_flip_mem_inactive_upper_cube C a v c hsame hcInactive
  have hv : v ∈ completionFibre C word :=
    (mem_completionFibre C word v).2 hvcube
  have hcardPos : 0 < (completionFibre C word).card :=
    Finset.card_pos.mpr ⟨v, hv⟩
  have hmax := completionFibre_card_le_two C word
  by_cases hone : (completionFibre C word).card = 1
  · exact Or.inl hone
  · right
    have htwo : (completionFibre C word).card = 2 := by omega
    have hsecond :
        ∃ w : V, w ∈ completionFibre C word ∧ w ≠ v := by
      by_contra hnone
      push Not at hnone
      have hsub :
          completionFibre C word ⊆ ({v} : Finset V) := by
        intro w hw
        have heq : w = v := hnone w hw
        simp [heq]
      have hle :
          (completionFibre C word).card ≤ 1 := by
        calc
          (completionFibre C word).card ≤ ({v} : Finset V).card :=
            Finset.card_le_card hsub
          _ = 1 := by simp
      omega
    obtain ⟨w, hw, hwneV⟩ := hsecond
    have hwcube : word ∈ retainedCompletionWords C w :=
      (mem_completionFibre C word w).1 hw
    have hnotA : word ∉ retainedCompletionWords C a :=
      outgoing_flip_exits_lower_completion_cube C a c hcOutgoing
    have hwneA : w ≠ a := by
      intro h
      subst w
      exact hnotA hwcube
    exact ⟨w, hwneA, hwneV, hwcube,
      retainedCompletion_overlap_forces_residual
        C hwneV.symm hvcube hwcube⟩

/-- Triangle-free overlap graph: if two distinct other vertex cubes both
intersect the cube of v, those two cubes are disjoint from each other.
The proof combines the Helly property of Boolean subcubes with the
ordered-colouring prohibition on triple completion membership. -/
theorem retainedCompletion_two_neighbours_disjoint
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v w : V}
    (hav : a ≠ v)
    (haw : a ≠ w)
    (hvw : v ≠ w)
    (havOverlap :
      (retainedCompletionWords C a ∩
        retainedCompletionWords C v).Nonempty)
    (hvwOverlap :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).Nonempty) :
    Disjoint (retainedCompletionWords C a)
      (retainedCompletionWords C w) := by
  classical
  rw [Finset.disjoint_left]
  intro word haWord hwWord
  have hawOverlap :
      (retainedCompletionWords C a ∩
        retainedCompletionWords C w).Nonempty :=
    ⟨word, Finset.mem_inter.mpr ⟨haWord, hwWord⟩⟩
  obtain ⟨triple, htripleA, htripleV, htripleW⟩ :=
    three_retainedCompletion_pairwise_nonempty_common
      C havOverlap hawOverlap hvwOverlap
  exact no_three_distinct_share_retained_completion
    C hav haw hvw htripleA htripleV htripleW

/-- An oriented safe flip either reduces coverage multiplicity from two
to one, or rewires it to a new residual neighbour of the same upper
endpoint. The old and new *opposite-endpoint* cubes are disjoint.

This is the exact local overlap-routing certificate. No global rank
decrease or pairwise-disjoint accounting is claimed. -/
theorem oriented_safe_flip_singly_covered_or_disjoint_rewire
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hav : a ≠ v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v) :
    (fun d => retainedBit C a d) ∈ overlapCompletionWords C ∧
      ((completionFibre C (flippedRetainedCode C a c)).card = 1 ∨
        ∃ w : V,
          w ≠ a ∧ w ≠ v ∧
          flippedRetainedCode C a c ∈ retainedCompletionWords C w ∧
          Disjoint (retainedCompletionWords C a)
            (retainedCompletionWords C w) ∧
          ((v < w ∧ IsResidual C v w) ∨
            (w < v ∧ IsResidual C w v))) := by
  constructor
  · exact sameRetained_base_mem_overlapCompletionWords C a v hav hsame
  rcases oriented_safe_flip_singleton_or_new_residual_overlap
      C a v c hsame hcOutgoing hcInactive with hsingle | hre
  · exact Or.inl hsingle
  · right
    obtain ⟨w, hwa, hwv, hwcube, hres⟩ := hre
    have hbaseOverlap :
        (retainedCompletionWords C a ∩
          retainedCompletionWords C v).Nonempty :=
      ⟨fun d => retainedBit C a d,
        retained_base_mem_both_completionWords C hsame⟩
    have hflipOverlap :
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).Nonempty :=
      ⟨flippedRetainedCode C a c,
        Finset.mem_inter.mpr
          ⟨sameRetained_flip_mem_inactive_upper_cube
              C a v c hsame hcInactive, hwcube⟩⟩
    have hdisj :=
      retainedCompletion_two_neighbours_disjoint
        C hav hwa.symm hwv.symm hbaseOverlap hflipOverlap
    exact ⟨w, hwa, hwv, hwcube, hdisj, hres⟩

/-- A second completion-cube blocker for an oriented safe flip
must be strictly INSIDE the original residual pair's interval.

Proof: a blocker to the right of v would create a forbidden consecutive
residual two-path a-v-w. A blocker to the left of a would force the
retained edge w-a to have colour c (the only coordinate at which the
flipped word can disagree), contradicting that c is outgoing at a.

Unlike previous canonical-code blocker lemmas, w only needs to COVER
the flipped word in its partial completion cube. -/
theorem oriented_safe_flip_cube_partner_strictly_interior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v w : V} {c : Fin n}
    (hav : a < v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v)
    (hwneV : w ≠ v)
    (hwcube : flippedRetainedCode C a c ∈
      retainedCompletionWords C w) :
    a < w ∧ w < v ∧ IsResidual C w v := by
  classical
  have hvcube : flippedRetainedCode C a c ∈
      retainedCompletionWords C v :=
    sameRetained_flip_mem_inactive_upper_cube C a v c
      hsame hcInactive
  have hresAV : IsResidual C a v :=
    isResidual_of_sameRetained_lt C hav hsame
  have hwvRes : w < v ∧ IsResidual C w v := by
    rcases retainedCompletion_overlap_forces_residual
        C hwneV.symm hvcube hwcube with hright | hleft
    · exact False.elim
        (no_two_residual_on_path C hav hright.1
          hresAV hright.2)
    · exact hleft
  have hnotA :
      flippedRetainedCode C a c ∉ retainedCompletionWords C a :=
    outgoing_flip_exits_lower_completion_cube C a c hcOutgoing
  have haw : a < w := by
    rcases lt_trichotomy a w with haw | heq | hwa
    · exact haw
    · subst w
      exact False.elim (hnotA hwcube)
    · have hnotResWA : ¬ IsResidual C w a := by
        intro hresWA
        exact no_two_residual_on_path C hwa hav
          hresWA hresAV
      have hretWA : (C.color w a).val < n := by
        by_contra hret
        exact hnotResWA hret
      let d : Fin n := retainedColor C w a hretWA
      have hdW : d ∈ retainedActive C w :=
        retainedColor_mem_retainedActive_left C hwa hretWA
      have hdiff :
          retainedBit C w d ≠ retainedBit C a d :=
        retainedBit_ne_of_retained_edge C hwa hretWA
      have hdc : d = c := by
        by_contra hne
        have hbit :
            retainedBit C w d = retainedBit C a d := by
          calc
            retainedBit C w d =
                flippedRetainedCode C a c d :=
              ((mem_retainedCompletionWords C w _).1
                hwcube d hdW).symm
            _ = retainedBit C a d :=
              flippedRetainedCode_off C a c d hne
        exact hdiff hbit
      have hcol : C.color w a = c.castSucc := by
        apply Fin.ext
        simpa [d, retainedColor] using congrArg Fin.val hdc
      have hcin : c ∈ incomingRetained C a :=
        (mem_incomingRetained_iff C a c).2
          ⟨w, hwa, hcol⟩
      exact False.elim
        ((Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C a))
          hcin hcOutgoing)
  exact ⟨haw, hwvRes.1, hwvRes.2⟩

/-- The geometric-looking interior blocker found from a SECOND
completion-cube cover is precisely connected to the lower endpoint
by the originally flipped retained colour. No planar AngleCap assumption
is needed for this ordered-colouring statement. -/
theorem oriented_safe_flip_cube_partner_edgeColor_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v w : V} {c : Fin n}
    (hav : a < v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v)
    (hwneV : w ≠ v)
    (hwcube : flippedRetainedCode C a c ∈
      retainedCompletionWords C w) :
    C.color a w = c.castSucc := by
  classical
  obtain ⟨haw, hwv, hresWV⟩ :=
    oriented_safe_flip_cube_partner_strictly_interior
      C hav hsame hcOutgoing hcInactive hwneV hwcube
  have hnotResAW : ¬ IsResidual C a w := by
    intro hresAW
    exact no_two_residual_on_path C haw hwv hresAW hresWV
  have hretAW : (C.color a w).val < n := by
    by_contra hret
    exact hnotResAW hret
  let d : Fin n := retainedColor C a w hretAW
  have hdW : d ∈ retainedActive C w :=
    retainedColor_mem_retainedActive_right C haw hretAW
  have hdiff :
      retainedBit C a d ≠ retainedBit C w d :=
    retainedBit_ne_of_retained_edge C haw hretAW
  have hdc : d = c := by
    by_contra hne
    have heq :
        retainedBit C a d = retainedBit C w d := by
      calc
        retainedBit C a d = flippedRetainedCode C a c d :=
          (flippedRetainedCode_off C a c d hne).symm
        _ = retainedBit C w d :=
          ((mem_retainedCompletionWords C w _).1 hwcube d hdW)
    exact hdiff heq
  apply Fin.ext
  simpa [d, retainedColor] using congrArg Fin.val hdc

/-- Final local rewiring dichotomy with strict betweenness AND the
precise retained edge colour of the new secondary cube blocker. -/
theorem oriented_safe_flip_overlap_singleton_or_interior_rewire
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (c : Fin n)
    (hav : a < v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v) :
    (fun d => retainedBit C a d) ∈ overlapCompletionWords C ∧
      ((completionFibre C (flippedRetainedCode C a c)).card = 1 ∨
        ∃ w : V, a < w ∧ w < v ∧
          IsResidual C w v ∧
          C.color a w = c.castSucc ∧
          Disjoint (retainedCompletionWords C a)
            (retainedCompletionWords C w)) := by
  have hroute :=
    oriented_safe_flip_singly_covered_or_disjoint_rewire
      C a v c (ne_of_lt hav) hsame hcOutgoing hcInactive
  refine ⟨hroute.1, ?_⟩
  rcases hroute.2 with hone | hrewire
  · exact Or.inl hone
  · right
    obtain ⟨w, hwneA, hwneV, hwcube, hdisjoint, _hres⟩ := hrewire
    obtain ⟨haw, hwv, hresWV⟩ :=
      oriented_safe_flip_cube_partner_strictly_interior
        C hav hsame hcOutgoing hcInactive hwneV hwcube
    have hcol :=
      oriented_safe_flip_cube_partner_edgeColor_eq
        C hav hsame hcOutgoing hcInactive hwneV hwcube
    exact ⟨w, haw, hwv, hresWV, hcol, hdisjoint⟩

#print axioms sameRetained_base_mem_overlapCompletionWords
#print axioms oriented_safe_flip_cube_partner_edgeColor_eq
#print axioms oriented_safe_flip_overlap_singleton_or_interior_rewire
#print axioms oriented_safe_flip_cube_partner_strictly_interior
#print axioms oriented_safe_flip_singleton_or_new_residual_overlap
#print axioms retainedCompletion_two_neighbours_disjoint
#print axioms oriented_safe_flip_singly_covered_or_disjoint_rewire

end OrderedEdgeColoring
end JSP000404Research
