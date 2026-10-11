import JSP000404Research.ResidualCompletionOverlapRewire
import Mathlib.Tactic

/-!
# Injective interior blockers for doubly-covered oriented safe flips

For a fixed same-retained residual pair a<v, each outgoing colour at a
that is inactive at v gives a Boolean word inside Q_v and outside Q_a.
If this word is doubly covered, its unique second covering vertex w must
lie strictly inside (a,v), be residually connected to v, and have
colour(a,w) equal to the original flip colour.

Consequently different doubly-covered flip colours require DIFFERENT
interior residual vertices. This proves a genuine finite matching
bound without Hall subset expansion. If the safe-colour set is larger
than the number of interior residual vertices, at least one flip is
singly covered rather than doubly covered.

The conclusion does NOT say such a flip is a Boolean hole: its word
is still in Q_v. The missing global payment remains open.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Oriented safe colours whose flipped codes are covered twice. -/
noncomputable def doubleSafeFlipColors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c =>
    c ∈ outgoingRetained C a ∧
    c ∉ retainedActive C v ∧
    (completionFibre C (flippedRetainedCode C a c)).card = 2)

@[simp] theorem mem_doubleSafeFlipColors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n) :
    c ∈ doubleSafeFlipColors C a v ↔
      c ∈ outgoingRetained C a ∧
      c ∉ retainedActive C v ∧
      (completionFibre C (flippedRetainedCode C a c)).card = 2 := by
  classical
  simp [doubleSafeFlipColors]

/-- Available interior residual vertices for the upper endpoint v. -/
noncomputable def interiorResidualBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w =>
    a < w ∧ w < v ∧ IsResidual C w v)

@[simp] theorem mem_interiorResidualBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v w : V) :
    w ∈ interiorResidualBlockers C a v ↔
      a < w ∧ w < v ∧ IsResidual C w v := by
  classical
  simp [interiorResidualBlockers]

/-- Every doubly covered safe flip has a definite interior residual
blocker, joined to the lower endpoint a by the SAME retained colour. -/
theorem doubleSafeFlipColor_has_interior_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (hav : a < v)
    (hsame : SameRetained C a v)
    {c : Fin n}
    (hc : c ∈ doubleSafeFlipColors C a v) :
    ∃ w : V,
      a < w ∧ w < v ∧ IsResidual C w v ∧
      C.color a w = c.castSucc := by
  have hdata := (mem_doubleSafeFlipColors C a v c).1 hc
  obtain ⟨_hbase, hcase⟩ :=
    oriented_safe_flip_overlap_singleton_or_interior_rewire
      C c hav hsame hdata.1 hdata.2.1
  rcases hcase with hone | hrewire
  · omega
  · obtain ⟨w, haw, hwv, hres, hcol, _⟩ := hrewire
    exact ⟨w, haw, hwv, hres, hcol⟩

/-- All double-cover blockers can be chosen simultaneously, with no
choice function assumed at the global payment level. -/
noncomputable def doubleSafeFlipBlockerMap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (hav : a < v)
    (hsame : SameRetained C a v) :
    {c : Fin n // c ∈ doubleSafeFlipColors C a v} →
      {w : V // w ∈ interiorResidualBlockers C a v} := by
  classical
  intro c
  have h := doubleSafeFlipColor_has_interior_blocker
    C hav hsame c.2
  refine ⟨Classical.choose h, ?_⟩
  exact (mem_interiorResidualBlockers C a v _).2
    ⟨(Classical.choose_spec h).1,
      (Classical.choose_spec h).2.1,
      (Classical.choose_spec h).2.2.1⟩

/-- The chosen blocker still realizes exactly the source flip colour. -/
theorem doubleSafeFlipBlockerMap_color
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (hav : a < v)
    (hsame : SameRetained C a v)
    (c : {d : Fin n // d ∈ doubleSafeFlipColors C a v}) :
    C.color a (doubleSafeFlipBlockerMap C hav hsame c).1 =
      c.1.castSucc := by
  classical
  exact (Classical.choose_spec
    (doubleSafeFlipColor_has_interior_blocker
      C hav hsame c.2)).2.2.2

/-- Distinct doubly-covered flip coordinates have distinct
chosen interior residual blockers. The edge colour recovers c. -/
theorem doubleSafeFlipBlockerMap_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (hav : a < v)
    (hsame : SameRetained C a v) :
    Function.Injective
      (doubleSafeFlipBlockerMap C hav hsame) := by
  intro c d heq
  apply Subtype.ext
  have hc := doubleSafeFlipBlockerMap_color C hav hsame c
  have hd := doubleSafeFlipBlockerMap_color C hav hsame d
  have hcol : (c.1.castSucc : Fin (n + 1)) = d.1.castSucc := by
    calc
      c.1.castSucc =
          C.color a (doubleSafeFlipBlockerMap C hav hsame c).1 := hc.symm
      _ = C.color a (doubleSafeFlipBlockerMap C hav hsame d).1 := by
        rw [heq]
      _ = d.1.castSucc := hd
  apply Fin.ext
  simpa using congrArg Fin.val hcol

/-- Quantitative Hall-free injective charging of every doubly-covered
oriented safe flip to a DISTINCT interior residual vertex. -/
theorem doubleSafeFlipColors_card_le_interiorResidualBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (hav : a < v)
    (hsame : SameRetained C a v) :
    (doubleSafeFlipColors C a v).card ≤
      (interiorResidualBlockers C a v).card := by
  classical
  have hcard :=
    Fintype.card_le_of_injective
      (doubleSafeFlipBlockerMap C hav hsame)
      (doubleSafeFlipBlockerMap_injective C hav hsame)
  simpa only [Fintype.card_coe] using hcard

/-- All safe outward/inactive colours, regardless of the resulting
completion multiplicity. -/
noncomputable def orientedSafeFlipColors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun c => c ∈ outgoingRetained C a ∧
      c ∉ retainedActive C v)

@[simp] theorem mem_orientedSafeFlipColors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n) :
    c ∈ orientedSafeFlipColors C a v ↔
      c ∈ outgoingRetained C a ∧
      c ∉ retainedActive C v := by
  classical
  simp [orientedSafeFlipColors]

/-- Quantitative obstruction to ALL safe flips being doubly covered:
if there are more oriented safe flip colours than interior residual
vertices, then at least one flipped word is SINGLY covered.

The word is still covered by v; this does NOT manufacture a Boolean
hole or assert the missing global payment inequality. -/
theorem safe_flip_singly_covered_of_more_colors_than_blockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} (hav : a < v)
    (hsame : SameRetained C a v)
    (hlarge :
      (interiorResidualBlockers C a v).card <
        (orientedSafeFlipColors C a v).card) :
    ∃ c : Fin n,
      c ∈ outgoingRetained C a ∧
      c ∉ retainedActive C v ∧
      (completionFibre C (flippedRetainedCode C a c)).card = 1 := by
  classical
  by_contra hno
  have hsub :
      orientedSafeFlipColors C a v ⊆
        doubleSafeFlipColors C a v := by
    intro c hc
    obtain ⟨hout, hinactive⟩ :=
      (mem_orientedSafeFlipColors C a v c).1 hc
    have hupper : flippedRetainedCode C a c ∈
        retainedCompletionWords C v :=
      sameRetained_flip_mem_inactive_upper_cube
        C a v c hsame hinactive
    have hv : v ∈ completionFibre C
        (flippedRetainedCode C a c) :=
      (mem_completionFibre C _ v).2 hupper
    have hpos : 0 <
        (completionFibre C (flippedRetainedCode C a c)).card :=
      Finset.card_pos.mpr ⟨v, hv⟩
    have htwo :
        (completionFibre C (flippedRetainedCode C a c)).card ≤ 2 :=
      completionFibre_card_le_two C _
    have hnotOne :
        (completionFibre C (flippedRetainedCode C a c)).card ≠ 1 := by
      intro hone
      exact hno ⟨c, hout, hinactive, hone⟩
    have hcard : (completionFibre C
        (flippedRetainedCode C a c)).card = 2 := by
      omega
    exact (mem_doubleSafeFlipColors C a v c).2
      ⟨hout, hinactive, hcard⟩
  have hle :=
    Finset.card_le_card hsub
  have hblock :=
    doubleSafeFlipColors_card_le_interiorResidualBlockers
      C hav hsame
  omega

#print axioms safe_flip_singly_covered_of_more_colors_than_blockers

#print axioms doubleSafeFlipColor_has_interior_blocker
#print axioms doubleSafeFlipBlockerMap_color
#print axioms doubleSafeFlipBlockerMap_injective
#print axioms doubleSafeFlipColors_card_le_interiorResidualBlockers

end OrderedEdgeColoring
end JSP000404Research
