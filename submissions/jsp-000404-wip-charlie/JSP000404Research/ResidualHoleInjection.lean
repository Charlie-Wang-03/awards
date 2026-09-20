import JSP000404Research.ResidualCommonInactive
import Mathlib.Tactic

/-!
# Injecting hard residual duplicates into Boolean-code holes

Project the canonical `(n+1)`-bit code of an ordered edge colouring onto its
first `n` retained coordinates.  A collision of retained codes is necessarily
a residual edge.  If the two endpoints of every such collision share one
inactive retained coordinate, flip that coordinate for exactly the later
endpoint of the collision.

The local free-neighbour lemma says that the flipped code is absent from the
original retained-code image.  The key point proved here is global: two such
repairs cannot hit the same Boolean word.  A hypothetical collision would
force every edge of a three-vertex triangle to have the residual colour,
contradicting the no-monochromatic-two-path axiom.

Hence the repaired retained code is injective into `Fin n → Bool`, giving the
sharp cardinality bound `|V| ≤ 2^n`.

This removes the Hall-matching concern from the residual-colour route.  The
remaining geometric task is only to produce a common inactive retained
coordinate for each duplicated retained-code fibre.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Equality of all retained canonical Boolean coordinates. -/
def SameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) (u v : V) : Prop :=
  ∀ c : Fin n, retainedBit C u c = retainedBit C v c

theorem sameRetained_refl
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) (u : V) :
    SameRetained C u u := by
  intro c
  rfl

theorem sameRetained_symm
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)} {u v : V}
    (h : SameRetained C u v) :
    SameRetained C v u := by
  intro c
  exact (h c).symm

theorem sameRetained_trans
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)} {u v w : V}
    (huv : SameRetained C u v)
    (hvw : SameRetained C v w) :
    SameRetained C u w := by
  intro c
  exact (huv c).trans (hvw c)

/-- Flip one retained coordinate of the canonical retained code. -/
noncomputable def flippedRetainedCode
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    Fin n → Bool :=
  fun d =>
    if d = c then Bool.not (retainedBit C v d)
    else retainedBit C v d

theorem flippedRetainedCode_off
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c d : Fin n)
    (hdc : d ≠ c) :
    flippedRetainedCode C v c d = retainedBit C v d := by
  simp [flippedRetainedCode, hdc]

theorem flippedRetainedCode_at_ne
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    flippedRetainedCode C v c c ≠ retainedBit C v c := by
  cases h : retainedBit C v c <;>
    simp [flippedRetainedCode, h]

/-- Equality of two flipped codes forces equality of the original retained
bits away from the two flipped coordinates. -/
theorem retainedBit_eq_off_of_flippedCode_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {x y : V} {c d e : Fin n}
    (hflip :
      flippedRetainedCode C x c =
        flippedRetainedCode C y d)
    (hec : e ≠ c) (hed : e ≠ d) :
    retainedBit C x e = retainedBit C y e := by
  have he := congrFun hflip e
  simpa [flippedRetainedCode, hec, hed] using he

theorem castSucc_mem_active_iff_mem_retainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    c.castSucc ∈ active C v ↔ c ∈ retainedActive C v := by
  classical
  simp [active, retainedActive]

/-- The projected colour of a retained increasing edge is retained-active at
its lower endpoint. -/
theorem retainedColor_mem_retainedActive_left
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} (huv : u < v)
    (hret : (C.color u v).val < n) :
    retainedColor C u v hret ∈ retainedActive C u := by
  classical
  simp only [retainedActive, Finset.mem_filter, Finset.mem_univ, true_and]
  right
  refine ⟨v, huv, ?_⟩
  apply Fin.ext
  rfl

/-- The projected colour of a retained increasing edge is retained-active at
its upper endpoint. -/
theorem retainedColor_mem_retainedActive_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} (huv : u < v)
    (hret : (C.color u v).val < n) :
    retainedColor C u v hret ∈ retainedActive C v := by
  classical
  simp only [retainedActive, Finset.mem_filter, Finset.mem_univ, true_and]
  left
  refine ⟨u, huv, ?_⟩
  apply Fin.ext
  rfl

/-- Two distinct vertices with the same retained code are joined by the
residual colour. -/
theorem isResidual_of_sameRetained_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} (huv : u < v)
    (hsame : SameRetained C u v) :
    IsResidual C u v := by
  intro hret
  have hne :=
    retainedBit_ne_of_retained_edge C huv hret
  exact hne (hsame (retainedColor C u v hret))

/-- If two base codes have equal one-coordinate flips, then any increasing
edge between representatives of those bases is residual provided the
corresponding flipped coordinate is inactive at each representative.

This is the local collision mechanism used by the global hole injection. -/
theorem isResidual_of_flippedCode_collision_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a b x y : V} {c d : Fin n}
    (hab : a < b)
    (hax : SameRetained C a x)
    (hby : SameRetained C b y)
    (hc : c ∉ retainedActive C a)
    (hd : d ∉ retainedActive C b)
    (hflip :
      flippedRetainedCode C x c =
        flippedRetainedCode C y d) :
    IsResidual C a b := by
  intro hret
  let e : Fin n := retainedColor C a b hret
  have hne :
      retainedBit C a e ≠ retainedBit C b e :=
    retainedBit_ne_of_retained_edge C hab hret
  by_cases hec : e = c
  · subst e
    exact hc (retainedColor_mem_retainedActive_left C hab hret)
  · by_cases hed : e = d
    · subst e
      exact hd (retainedColor_mem_retainedActive_right C hab hret)
    · have hxy :
          retainedBit C x e = retainedBit C y e :=
        retainedBit_eq_off_of_flippedCode_eq
          C hflip hec hed
      have habEq :
          retainedBit C a e = retainedBit C b e :=
        (hax e).trans (hxy.trans (hby e).symm)
      exact hne habEq

/-- A common inactive coordinate produces a flipped retained code which is not
realized by any original vertex.  This is the function-valued form of
`no_vertex_realizes_flipped_common_inactive_code`. -/
theorem no_vertex_retainedCode_eq_flipped_common_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} (c : Fin n)
    (huv : u ≠ v)
    (hsame : SameRetained C u v)
    (hcu : c ∉ retainedActive C u)
    (hcv : c ∉ retainedActive C v) :
    ¬ ∃ w : V,
      (fun d => retainedBit C w d) =
        flippedRetainedCode C u c := by
  have hfree :=
    no_vertex_realizes_flipped_common_inactive_code
      C c huv hsame
      (by
        intro hc
        exact hcu ((castSucc_mem_active_iff_mem_retainedActive C u c).1 hc))
      (by
        intro hc
        exact hcv ((castSucc_mem_active_iff_mem_retainedActive C v c).1 hc))
  rintro ⟨w, hw⟩
  apply hfree
  refine ⟨w, ?_, ?_⟩
  · have hwc :
        retainedBit C w c =
          Bool.not (retainedBit C u c) := by
      have := congrFun hw c
      simpa [flippedRetainedCode] using this
    intro heq
    have hbad :
        retainedBit C u c =
          Bool.not (retainedBit C u c) :=
      heq.symm.trans hwc
    cases h : retainedBit C u c <;> simp [h] at hbad
  · intro d hdc
    have hwd := congrFun hw d
    simpa [flippedRetainedCode, hdc] using hwd

/-- Two different retained-code fibres cannot send a common-inactive repair
to the same Boolean word.

Indeed, take one vertical pair `u<v` and a representative `w` of another
retained fibre.  If the two flipped codes coincide, every cross edge from
`w` to `u,v` is forced to be residual.  Together with the residual edge
`u-v`, whichever of `u,v,w` is the middle point lies on a monochromatic
residual two-path. -/
theorem flipped_common_inactive_codes_ne
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hbase : ¬ SameRetained C v w)
    (hcu : c ∉ retainedActive C u)
    (hcv : c ∉ retainedActive C v)
    (hdw : d ∉ retainedActive C w) :
    flippedRetainedCode C v c ≠
      flippedRetainedCode C w d := by
  intro hflip
  have hresUV : IsResidual C u v :=
    isResidual_of_sameRetained_lt C huv hsame
  have hvwNe : v ≠ w := by
    intro h
    subst w
    exact hbase (sameRetained_refl C v)
  have huwNe : u ≠ w := by
    intro h
    subst w
    exact hbase (sameRetained_symm hsame)

  have hresUW_of_lt (huw : u < w) :
      IsResidual C u w := by
    exact isResidual_of_flippedCode_collision_lt
      C huw hsame (sameRetained_refl C w)
      hcu hdw hflip
  have hresWU_of_lt (hwu : w < u) :
      IsResidual C w u := by
    exact isResidual_of_flippedCode_collision_lt
      C hwu (sameRetained_refl C w) hsame
      hdw hcu hflip.symm
  have hresVW_of_lt (hvw : v < w) :
      IsResidual C v w := by
    exact isResidual_of_flippedCode_collision_lt
      C hvw (sameRetained_refl C v) (sameRetained_refl C w)
      hcv hdw hflip
  have hresWV_of_lt (hwv : w < v) :
      IsResidual C w v := by
    exact isResidual_of_flippedCode_collision_lt
      C hwv (sameRetained_refl C w) (sameRetained_refl C v)
      hdw hcv hflip.symm

  rcases lt_trichotomy w u with hwu | hwu | huw
  · have hresWU := hresWU_of_lt hwu
    apply C.noMonoTwoPath hwu huv
    apply Fin.ext
    rw [residual_val_eq C hresWU, residual_val_eq C hresUV]
  · exact huwNe hwu.symm
  · rcases lt_trichotomy w v with hwv | hwv | hvw
    · have hresUW := hresUW_of_lt huw
      have hresWV := hresWV_of_lt hwv
      apply C.noMonoTwoPath huw hwv
      apply Fin.ext
      rw [residual_val_eq C hresUW, residual_val_eq C hresWV]
    · exact hvwNe hwv.symm
    · have hresVW := hresVW_of_lt hvw
      apply C.noMonoTwoPath huv hvw
      apply Fin.ext
      rw [residual_val_eq C hresUV, residual_val_eq C hresVW]

/-- A retained-code fibre has an earlier representative. -/
def HasEarlierSame
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) (v : V) : Prop :=
  ∃ u, u < v ∧ SameRetained C u v

noncomputable def earlierSameVertex
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (h : HasEarlierSame C v) : V :=
  Classical.choose h

theorem earlierSameVertex_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (h : HasEarlierSame C v) :
    earlierSameVertex C v h < v :=
  (Classical.choose_spec h).1

theorem earlierSameVertex_same
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (h : HasEarlierSame C v) :
    SameRetained C (earlierSameVertex C v h) v :=
  (Classical.choose_spec h).2

/-- The exact local hypothesis needed by the global repair: every duplicated
retained-code fibre has one retained coordinate inactive at both endpoints. -/
def DuplicateCommonInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) : Prop :=
  ∀ {u v : V}, u < v → SameRetained C u v →
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧ c ∉ retainedActive C v

noncomputable def repairCoord
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C)
    (v : V) (h : HasEarlierSame C v) : Fin n :=
  Classical.choose
    (hrepair (earlierSameVertex_lt C v h)
      (earlierSameVertex_same C v h))

theorem repairCoord_not_mem_earlier
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C)
    (v : V) (h : HasEarlierSame C v) :
    repairCoord C hrepair v h ∉
      retainedActive C (earlierSameVertex C v h) :=
  (Classical.choose_spec
    (hrepair (earlierSameVertex_lt C v h)
      (earlierSameVertex_same C v h))).1

theorem repairCoord_not_mem_self
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C)
    (v : V) (h : HasEarlierSame C v) :
    repairCoord C hrepair v h ∉ retainedActive C v :=
  (Classical.choose_spec
    (hrepair (earlierSameVertex_lt C v h)
      (earlierSameVertex_same C v h))).2

/-- Keep the first vertex of every retained-code fibre at its old code and
move every later duplicate to its certified free neighbouring code. -/
noncomputable def repairedRetainedCode
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C) :
    V → (Fin n → Bool) :=
  fun v =>
    if h : HasEarlierSame C v then
      flippedRetainedCode C v (repairCoord C hrepair v h)
    else
      fun c => retainedBit C v c

/-- A moved duplicate lands outside the complete original retained-code image. -/
theorem repairedRetainedCode_of_duplicate_is_hole
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C)
    (v : V) (h : HasEarlierSame C v) :
    ¬ ∃ w : V,
      (fun c => retainedBit C w c) =
        repairedRetainedCode C hrepair v := by
  let u := earlierSameVertex C v h
  let c := repairCoord C hrepair v h
  have huv : u ≠ v := ne_of_lt (earlierSameVertex_lt C v h)
  have hsameVU : SameRetained C v u :=
    sameRetained_symm (earlierSameVertex_same C v h)
  have hcv : c ∉ retainedActive C v := by
    exact repairCoord_not_mem_self C hrepair v h
  have hcu : c ∉ retainedActive C u := by
    exact repairCoord_not_mem_earlier C hrepair v h
  have hhole :=
    no_vertex_retainedCode_eq_flipped_common_inactive
      C c huv.symm hsameVU hcv hcu
  simpa [repairedRetainedCode, h, u, c] using hhole

/-- Two vertices which both have earlier representatives cannot be distinct
members of the same retained-code fibre. -/
theorem sameRetained_of_two_hasEarlierSame
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V}
    (hv : HasEarlierSame C v)
    (hw : HasEarlierSame C w)
    (hsame : SameRetained C v w) :
    v = w := by
  by_contra hvw
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · let u := earlierSameVertex C v hv
    have huv : u < v := earlierSameVertex_lt C v hv
    have huw : u ≠ w := ne_of_lt (huv.trans hvwlt)
    have huvNe : u ≠ v := ne_of_lt huv
    have hUV := earlierSameVertex_same C v hv
    have hUW := sameRetained_trans hUV hsame
    exact hvw
      (retainedFiber_other_unique C huvNe huw hUV hUW)
  · let u := earlierSameVertex C w hw
    have huw : u < w := earlierSameVertex_lt C w hw
    have huv : u ≠ v := ne_of_lt (huw.trans hwvlt)
    have huwNe : u ≠ w := ne_of_lt huw
    have hUW := earlierSameVertex_same C w hw
    have hUV := sameRetained_trans hUW (sameRetained_symm hsame)
    exact hvw.symm
      (retainedFiber_other_unique C huwNe huv hUW hUV)

/-- Repairs attached to two distinct duplicated fibres are distinct. -/
theorem repaired_flips_ne_of_distinct_duplicates
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C)
    {v w : V}
    (hv : HasEarlierSame C v)
    (hw : HasEarlierSame C w)
    (hvw : v ≠ w) :
    flippedRetainedCode C v (repairCoord C hrepair v hv) ≠
      flippedRetainedCode C w (repairCoord C hrepair w hw) := by
  have hbase : ¬ SameRetained C v w := by
    intro hsame
    exact hvw (sameRetained_of_two_hasEarlierSame C hv hw hsame)
  let u := earlierSameVertex C v hv
  have huv : u < v := earlierSameVertex_lt C v hv
  have hsameUV := earlierSameVertex_same C v hv
  exact flipped_common_inactive_codes_ne
    C huv hsameUV hbase
    (repairCoord_not_mem_earlier C hrepair v hv)
    (repairCoord_not_mem_self C hrepair v hv)
    (repairCoord_not_mem_self C hrepair w hw)

/-- The repaired n-bit code is globally injective. -/
theorem repairedRetainedCode_injective
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C) :
    Function.Injective (repairedRetainedCode C hrepair) := by
  intro v w heq
  by_cases hv : HasEarlierSame C v
  · by_cases hw : HasEarlierSame C w
    · by_contra hvw
      have hne :=
        repaired_flips_ne_of_distinct_duplicates
          C hrepair hv hw hvw
      apply hne
      simpa [repairedRetainedCode, hv, hw] using heq
    · exfalso
      have hhole :=
        repairedRetainedCode_of_duplicate_is_hole
          C hrepair v hv
      apply hhole
      refine ⟨w, ?_⟩
      simpa [repairedRetainedCode, hv, hw] using heq.symm
  · by_cases hw : HasEarlierSame C w
    · exfalso
      have hhole :=
        repairedRetainedCode_of_duplicate_is_hole
          C hrepair w hw
      apply hhole
      refine ⟨v, ?_⟩
      simpa [repairedRetainedCode, hv, hw] using heq
    · have hsame : SameRetained C v w := by
        intro c
        have hc := congrFun heq c
        simpa [repairedRetainedCode, hv, hw] using hc
      by_contra hvw
      rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
      · exact hw ⟨v, hvwlt, hsame⟩
      · exact hv ⟨w, hwvlt, sameRetained_symm hsame⟩

/-- Sharp residual-colour elimination at the cardinality level. -/
theorem card_le_two_pow_of_duplicate_common_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hrepair : DuplicateCommonInactive C) :
    Fintype.card V ≤ 2 ^ n := by
  have hcard :
      Fintype.card V ≤ Fintype.card (Fin n → Bool) :=
    Fintype.card_le_of_injective
      (repairedRetainedCode C hrepair)
      (repairedRetainedCode_injective C hrepair)
  simpa [Fintype.card_fun] using hcard

/-- A directly checkable sufficient condition: every duplicated retained fibre
has combined retained activity strictly below n. -/
theorem card_le_two_pow_of_duplicate_active_sum_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hcard : ∀ {u v : V}, u < v → SameRetained C u v →
      (retainedActive C u).card +
        (retainedActive C v).card < n) :
    Fintype.card V ≤ 2 ^ n := by
  apply card_le_two_pow_of_duplicate_common_inactive C
  intro u v huv hsame
  exact exists_common_inactive_of_retained_card_add_lt
    C (hcard huv hsame)

#print axioms castSucc_mem_active_iff_mem_retainedActive
#print axioms isResidual_of_flippedCode_collision_lt
#print axioms no_vertex_retainedCode_eq_flipped_common_inactive
#print axioms flipped_common_inactive_codes_ne
#print axioms repairedRetainedCode_injective
#print axioms card_le_two_pow_of_duplicate_common_inactive
#print axioms card_le_two_pow_of_duplicate_active_sum_lt

end OrderedEdgeColoring
end JSP000404Research
