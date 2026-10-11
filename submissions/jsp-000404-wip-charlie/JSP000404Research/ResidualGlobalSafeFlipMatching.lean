import JSP000404Research.ResidualSafeFlipDoubleMatching
import JSP000404Research.ResidualOverlapPairDecomposition
import Mathlib.Tactic

/-!
# Global injective safe-flip re-routing across all same-retained pairs

A same-retained code cannot occur on three distinct vertices, because
their partial completion cubes would have a common Boolean word.
Hence two increasing same-retained pairs sharing an upper endpoint
have the SAME lower endpoint.

For EVERY doubly covered safe flip (a,v,c), the second covering cube
is a unique interior vertex w, with a<w<v, residual(w,v), and
colour(a,w)=c. Different source pairs with equal resulting residual
edges have the same upper endpoint and thus the same source lower
endpoint; edge colour then recovers c.

This builds a genuine GLOBAL INJECTION from doubly covered flips
across ALL increasing same-retained pairs into the set of residual
overlap-carrier edges. Unlike previous pair-local matching, different
original hard pairs cannot charge the same target residual edge.

This still does NOT map overlaps to global Boolean HOLES, or imply
the remaining global payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Three vertices cannot have the same retained canonical Boolean code;
in particular an increasing same-retained pair has unique lower endpoint
once its upper endpoint is specified. -/
theorem sameRetained_pairs_same_upper_unique_lower
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a b v : V}
    (hav : a < v)
    (hbv : b < v)
    (ha : SameRetained C a v)
    (hb : SameRetained C b v) :
    a = b := by
  by_contra hab
  let word : Fin n → Bool := fun d => retainedBit C v d
  have hv : word ∈ retainedCompletionWords C v := by
    apply (mem_retainedCompletionWords C v word).2
    intro d hd
    rfl
  have haw : word ∈ retainedCompletionWords C a := by
    apply (mem_retainedCompletionWords C a word).2
    intro d hd
    exact (ha d).symm
  have hbw : word ∈ retainedCompletionWords C b := by
    apply (mem_retainedCompletionWords C b word).2
    intro d hd
    exact (hb d).symm
  exact no_three_distinct_share_retained_completion
    C hab (ne_of_lt hav) (ne_of_lt hbv)
      haw hbw hv

/-- The full cube-covering witness for a doubled safe flip;
its image really belongs to the residual overlap carrier, not merely
to the set of residual edges. -/
theorem doubled_safe_flip_has_interior_overlap_edge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hav : a < v)
    (hsame : SameRetained C a v)
    {c : Fin n}
    (hc : c ∈ doubleSafeFlipColors C a v) :
    ∃ w : V,
      a < w ∧ w < v ∧ IsResidual C w v ∧
      C.color a w = c.castSucc ∧
      flippedRetainedCode C a c ∈ retainedCompletionWords C w := by
  have hdata := (mem_doubleSafeFlipColors C a v c).1 hc
  rcases oriented_safe_flip_singleton_or_new_residual_overlap
      C a v c hsame hdata.1 hdata.2.1 with hone | ⟨w, hneA, hneV, hwcube, _⟩
  · omega
  · obtain ⟨haw, hwv, hres⟩ :=
      oriented_safe_flip_cube_partner_strictly_interior
        C hav hsame hdata.1 hdata.2.1 hneV hwcube
    have hcolour :=
      oriented_safe_flip_cube_partner_edgeColor_eq
        C hav hsame hdata.1 hdata.2.1 hneV hwcube
    exact ⟨w, haw, hwv, hres, hcolour, hwcube⟩

/-- Each globally tracked source is a pair (a,v) and a doubled
safe-flip colour c at that pair. -/
noncomputable def globalDoubledSafeFlips
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset ((V × V) × Fin n) := by
  classical
  exact Finset.univ.filter (fun x =>
    x.1.1 < x.1.2 ∧
    SameRetained C x.1.1 x.1.2 ∧
    x.2 ∈ doubleSafeFlipColors C x.1.1 x.1.2)

@[simp] theorem mem_globalDoubledSafeFlips
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : (V × V) × Fin n) :
    x ∈ globalDoubledSafeFlips C ↔
      x.1.1 < x.1.2 ∧
      SameRetained C x.1.1 x.1.2 ∧
      x.2 ∈ doubleSafeFlipColors C x.1.1 x.1.2 := by
  classical
  simp [globalDoubledSafeFlips]

/-- A canonical secondary cube-blocker chosen for each GLOBAL source. -/
noncomputable def globalDoubledSafeFlipBlocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {y : (V × V) × Fin n // y ∈ globalDoubledSafeFlips C}) :
    V := by
  classical
  have hd := (mem_globalDoubledSafeFlips C x.1).1 x.2
  exact Classical.choose
    (doubled_safe_flip_has_interior_overlap_edge
      C hd.1 hd.2.1 hd.2.2)

theorem globalDoubledSafeFlipBlocker_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {y : (V × V) × Fin n // y ∈ globalDoubledSafeFlips C}) :
    let w := globalDoubledSafeFlipBlocker C x
    x.1.1.1 < w ∧ w < x.1.1.2 ∧
      IsResidual C w x.1.1.2 ∧
      C.color x.1.1.1 w = x.1.2.castSucc ∧
      flippedRetainedCode C x.1.1.1 x.1.2 ∈
        retainedCompletionWords C w := by
  classical
  exact Classical.choose_spec
    (doubled_safe_flip_has_interior_overlap_edge
      C ((mem_globalDoubledSafeFlips C x.1).1 x.2).1
        ((mem_globalDoubledSafeFlips C x.1).1 x.2).2.1
        ((mem_globalDoubledSafeFlips C x.1).1 x.2).2.2)

/-- Every global doubled safe flip is routed to a GENUINELY OVERLAPPING
residual edge (w,v) determined by an interior blocker w. -/
noncomputable def globalDoubledSafeFlipOverlapEdge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    {x : (V × V) × Fin n // x ∈ globalDoubledSafeFlips C} →
      {e : V × V // e ∈ overlapCarrierPairs C} := by
  classical
  intro x
  let w := globalDoubledSafeFlipBlocker C x
  have h := globalDoubledSafeFlipBlocker_spec C x
  have hd := (mem_globalDoubledSafeFlips C x.1).1 x.2
  have hvCube :
      flippedRetainedCode C x.1.1.1 x.1.2 ∈
        retainedCompletionWords C x.1.1.2 :=
    sameRetained_flip_mem_inactive_upper_cube
      C x.1.1.1 x.1.1.2 x.1.2 hd.2.1
        ((mem_doubleSafeFlipColors C x.1.1.1 x.1.1.2 x.1.2).1 hd.2.2).2.1
  refine ⟨(w,x.1.1.2), ?_⟩
  apply (mem_overlapCarrierPairs C (w,x.1.1.2)).2
  constructor
  · exact (mem_residualCarrierPairs C w x.1.1.2).2
      ⟨h.2.1,h.2.2.1⟩
  · exact ⟨flippedRetainedCode C x.1.1.1 x.1.2,
      Finset.mem_inter.mpr ⟨h.2.2.2.2,hvCube⟩⟩

/-- All source edges from ALL same-retained pairs have distinct
target overlap-carrier edges. The upper endpoint fixes the source
lower endpoint, and the retained edge colour fixes the flip. -/
theorem globalDoubledSafeFlipOverlapEdge_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Function.Injective (globalDoubledSafeFlipOverlapEdge C) := by
  classical
  intro x y heq
  have hv : x.1.1.2 = y.1.1.2 := by
    exact congrArg (fun z :
      {e : V × V // e ∈ overlapCarrierPairs C} => z.1.2) heq
  have hw :
      globalDoubledSafeFlipBlocker C x =
      globalDoubledSafeFlipBlocker C y := by
    exact congrArg (fun z :
      {e : V × V // e ∈ overlapCarrierPairs C} => z.1.1) heq
  have hx := (mem_globalDoubledSafeFlips C x.1).1 x.2
  have hy := (mem_globalDoubledSafeFlips C y.1).1 y.2
  have hylt : y.1.1.1 < x.1.1.2 := by
    simpa only [hv] using hy.1
  have hysame : SameRetained C y.1.1.1 x.1.1.2 := by
    simpa only [hv] using hy.2.1
  have ha : x.1.1.1 = y.1.1.1 :=
    sameRetained_pairs_same_upper_unique_lower
      C hx.1 hylt hx.2.1 hysame
  have hcx := (globalDoubledSafeFlipBlocker_spec C x).2.2.2.1
  have hcy := (globalDoubledSafeFlipBlocker_spec C y).2.2.2.1
  have hc : x.1.2 = y.1.2 := by
    have hcast : (x.1.2.castSucc : Fin (n + 1)) = y.1.2.castSucc := by
      calc
        x.1.2.castSucc =
            C.color x.1.1.1 (globalDoubledSafeFlipBlocker C x) := hcx.symm
        _ = C.color y.1.1.1 (globalDoubledSafeFlipBlocker C y) := by
          rw [ha,hw]
        _ = y.1.2.castSucc := hcy
    apply Fin.ext
    simpa using congrArg Fin.val hcast
  apply Subtype.ext
  apply Prod.ext
  · exact Prod.ext ha hv
  · exact hc

/-- Hall-free GLOBAL bound across ALL same-retained pairs:
doubled safe flips consume distinct ACTUALLY OVERLAPPING residual
carrier edges, with no multiple allocation of a carrier. -/
theorem globalDoubledSafeFlips_card_le_overlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (globalDoubledSafeFlips C).card ≤
      (overlapCarrierPairs C).card := by
  classical
  have h := Fintype.card_le_of_injective
    (globalDoubledSafeFlipOverlapEdge C)
    (globalDoubledSafeFlipOverlapEdge_injective C)
  simpa only [Fintype.card_coe] using h

/-- Soft residual overlap-carriers: the two endpoint canonical
retained codes are different, even though their partial completion
cubes overlap. -/
noncomputable def softOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact (overlapCarrierPairs C).filter
    (fun p => ¬ SameRetained C p.1 p.2)

@[simp] theorem mem_softOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) :
    p ∈ softOverlapCarrierPairs C ↔
      p ∈ overlapCarrierPairs C ∧
      ¬ SameRetained C p.1 p.2 := by
  classical
  simp [softOverlapCarrierPairs]

/-- The upper endpoint's NEW overlapping residual neighbour can
never share the original retained canonical word: a second such
same-code neighbour would create three distinct vertices with the
same retained code, which is impossible in this completion family. -/
theorem global_doubled_safe_flip_target_is_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {y : (V × V) × Fin n // y ∈ globalDoubledSafeFlips C}) :
    ¬ SameRetained C
      (globalDoubledSafeFlipBlocker C x) x.1.1.2 := by
  intro hsoft
  have hsrc := (mem_globalDoubledSafeFlips C x.1).1 x.2
  have hblock := globalDoubledSafeFlipBlocker_spec C x
  have heq :=
    sameRetained_pairs_same_upper_unique_lower C
      hsrc.1 hblock.2.1 hsrc.2.1 hsoft
  exact (ne_of_lt hblock.1) heq

/-- Strengthened target type: the global injective matching lands
inside the SOFT (distinct-code) residual-overlap carrier set,
not merely among all residual overlap carriers. -/
noncomputable def globalDoubledSafeFlipSoftOverlapEdge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    {x : (V × V) × Fin n // x ∈ globalDoubledSafeFlips C} →
      {e : V × V // e ∈ softOverlapCarrierPairs C} := by
  classical
  intro x
  let y := globalDoubledSafeFlipOverlapEdge C x
  refine ⟨y.1, ?_⟩
  exact (mem_softOverlapCarrierPairs C y.1).2
    ⟨y.2, global_doubled_safe_flip_target_is_soft C x⟩

/-- The extra soft-carrier restriction preserves GLOBAL injectivity. -/
theorem globalDoubledSafeFlipSoftOverlapEdge_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Function.Injective (globalDoubledSafeFlipSoftOverlapEdge C) := by
  intro x y hxy
  apply globalDoubledSafeFlipOverlapEdge_injective C
  apply Subtype.ext
  exact congrArg Subtype.val hxy

/-- Full hard-to-soft injection inequality across all hard sources:
the number of doubled safe flips cannot exceed the number of
overlapping residual edges with DIFFERENT endpoint codes. -/
theorem globalDoubledSafeFlips_card_le_softOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (globalDoubledSafeFlips C).card ≤
      (softOverlapCarrierPairs C).card := by
  classical
  have h := Fintype.card_le_of_injective
    (globalDoubledSafeFlipSoftOverlapEdge C)
    (globalDoubledSafeFlipSoftOverlapEdge_injective C)
  simpa only [Fintype.card_coe] using h

#print axioms global_doubled_safe_flip_target_is_soft
#print axioms globalDoubledSafeFlipSoftOverlapEdge_injective
#print axioms globalDoubledSafeFlips_card_le_softOverlapCarrierPairs

#print axioms sameRetained_pairs_same_upper_unique_lower
#print axioms doubled_safe_flip_has_interior_overlap_edge
#print axioms globalDoubledSafeFlipOverlapEdge_injective
#print axioms globalDoubledSafeFlips_card_le_overlapCarrierPairs

end OrderedEdgeColoring
end JSP000404Research
