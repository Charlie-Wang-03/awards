import Probe.ComponentInsertion

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (a : G.Dart) (v : V)
  (hv : v ∉ G.support)

include hv in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isolated_ne_source : a.fst ≠ v := by
  intro h
  exact hv (h ▸ a.adj.mem_support_left)

include hv in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isolated_missing : ¬G.Adj a.fst v := fun h => hv h.mem_support_right

/-- Insert the old-source dart and give the isolated endpoint a singleton rotation. -/
def pendantRotation : Equiv.Perm (Option (Option G.Dart)) :=
  (insertAfter R.rotate a).optionCongr

theorem pendant_cycles (x y : Option (Option G.Dart)) :
    (pendantRotation G R a).SameCycle x y ↔
      (embedDart G a.fst v (isolated_ne_source G a v hv) x).fst =
      (embedDart G a.fst v (isolated_ne_source G a v hv) y).fst := by
  have h₁ := insertAfter_fiber_cycles R.rotate (fun d : G.Dart => d.fst)
    R.sameCycle_iff_source a
  have hn : ∀ x, insertedLabel (fun d : G.Dart => d.fst) a x ≠ v := by
    intro x
    cases x with
    | none => exact isolated_ne_source G a v hv
    | some d => exact isolated_ne_source G d v hv
  have hh := fresh_source_fiber_cycles (insertAfter R.rotate a)
    (insertedLabel (fun d : G.Dart => d.fst) a) h₁ v hn x y
  have hl : ∀ z : Option (Option G.Dart),
      z.elim v (insertedLabel (fun d : G.Dart => d.fst) a) =
      (embedDart G a.fst v (isolated_ne_source G a v hv) z).fst := by
    intro z
    cases z with
    | none => rfl
    | some z => cases z <;> rfl
  rw [hl, hl] at hh
  exact hh

noncomputable def addPendant :
    RotationSystem (addedGraph G a.fst v (isolated_ne_source G a v hv)) := by
  let e := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
  let σ : Equiv.Perm (addedGraph G a.fst v (isolated_ne_source G a v hv)).Dart :=
    (e.symm.trans (pendantRotation G R a)).trans e
  have hc : ∀ x y, σ.SameCycle x y ↔ x.fst = y.fst := by
    intro x y
    have ht := transport_cycles e.symm (pendantRotation G R a) x y
    simp only [Equiv.symm_symm] at ht
    rw [ht, pendant_cycles G R a v hv]
    change (e (e.symm x)).fst = (e (e.symm y)).fst ↔ _
    rw [e.apply_symm_apply, e.apply_symm_apply]
  exact ⟨σ, fun x => (hc _ _).mp Equiv.Perm.SameCycle.rfl.apply_left,
    fun x y h => (hc x y).mpr h⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem pendant_face_formula :
    pendantRotation G R a * extendedReverse G =
      insertAfter (insertAfter R.face a.symm) none := by
  apply Equiv.ext
  intro x
  cases x with
  | none => simp [pendantRotation, extendedReverse, Equiv.Perm.mul_apply,
      RotationSystem.face, RotationSystem.reverseDart, SimpleGraph.Dart.symm_symm]
  | some x =>
    cases x with
    | none =>
      simp [pendantRotation, extendedReverse, Equiv.Perm.mul_apply,
        RotationSystem.face, RotationSystem.reverseDart]
    | some d =>
      by_cases hd : d = a.symm
      · subst d
        simp [pendantRotation, extendedReverse, Equiv.Perm.mul_apply,
          SimpleGraph.Dart.symm_symm, insertAfter_old]
      · have hs : d.symm ≠ a := fun h => hd (by simpa using congrArg SimpleGraph.Dart.symm h)
        simp [pendantRotation, extendedReverse, Equiv.Perm.mul_apply,
          insertAfter_old, hd, hs, RotationSystem.face, RotationSystem.reverseDart]

theorem pendant_face_count : (addPendant G R a v hv).faceCount = R.faceCount := by
  classical
  let e := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
  let τ := pendantRotation G R a * extendedReverse G
  let F := (addPendant G R a v hv).face
  have hc : ∀ x, e (τ x) = F (e x) := by
    intro x
    change e (pendantRotation G R a (extendedReverse G x)) =
      e (pendantRotation G R a (e.symm ((e x).symm)))
    have hr : e (extendedReverse G x) = (e x).symm := embed_reverse G _ _ _ x
    rw [← hr, e.symm_apply_apply]
  let qe : Quotient (Equiv.Perm.SameCycle.setoid τ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid F) :=
    Quotient.congr e (fun x y => (sameCycle_embedding τ F e e.injective hc x y).symm)
  have hh := Nat.card_congr qe
  change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid τ)) =
    (addPendant G R a v hv).faceCount at hh
  rw [← hh]
  change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
    (pendantRotation G R a * extendedReverse G))) = _
  rw [pendant_face_formula, insertAfter_orbit_count, insertAfter_orbit_count]
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The new pendant edge is the only edge removed. -/
theorem delete_pendant_edge :
    (addedGraph G a.fst v (isolated_ne_source G a v hv)).deleteEdges {s(a.fst,v)} = G := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  change ((G.Adj x y ∨ (x = a.fst ∧ y = v) ∨ (x = v ∧ y = a.fst)) ∧
    s(x,y) ≠ s(a.fst,v)) ↔ G.Adj x y
  simp only [ne_eq, Sym2.eq_iff]
  constructor
  · tauto
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact hv h.mem_support_right
    · exact hv h.mem_support_left

/-- Adding a pendant edge at a previously isolated vertex preserves Euler defect. -/
theorem pendant_defect : (addPendant G R a v hv).eulerDefect = R.eulerDefect := by
  classical
  let S := addPendant G R a v hv
  let d : (addedGraph G a.fst v (isolated_ne_source G a v hv)).Dart :=
    embedDart G a.fst v (isolated_ne_source G a v hv) (some none)
  have hd : DeletedGraph d = G := delete_pendant_edge G a v hv
  have hb : (addedGraph G a.fst v (isolated_ne_source G a v hv)).IsBridge d.edge := by
    change ¬(DeletedGraph d).Reachable a.fst v
    rw [hd]
    intro hr
    exact hv (SimpleGraph.mem_support_of_reachable (isolated_ne_source G a v hv).symm hr.symm)
  have hc := bridge_component_count d hb
  rw [hd] at hc
  have he := edge_count_delete d
  rw [hd] at he
  have hs := S.supportSize_delete d
  have hsource : S.rotate d ≠ d := by
    apply (S.source_survives_iff d).mp
    change a.fst ∈ (DeletedGraph d).support
    rw [hd]
    exact a.adj.mem_support_left
  have htarget : S.rotate d.symm = d.symm := by
    by_contra h
    have hh := (S.target_survives_iff d).mpr h
    change v ∈ (DeletedGraph d).support at hh
    rw [hd] at hh
    exact hv hh
  simp only [hsource, htarget, ite_false, ite_true, add_zero] at hs
  rw [hd] at hs
  have hf := pendant_face_count G R a v hv
  change S.faceCount = R.faceCount at hf
  change S.eulerDefect = R.eulerDefect
  unfold eulerDefect
  omega

theorem pendant_genusZero (hz : R.HasGenusZero) :
    (addPendant G R a v hv).HasGenusZero := by
  unfold HasGenusZero at hz ⊢
  rw [pendant_defect G R a v hv, hz]

end JSP512Probe.EdgeInsertion

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- A maximal genus-zero graph containing an edge has no isolated vertices. -/
theorem maximal_support_univ (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (a : G.Dart) : G.support = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro v
  by_contra hv
  let H := EdgeInsertion.addedGraph G a.fst v (EdgeInsertion.isolated_ne_source G a v hv)
  have hHG := maximal_supergraph_eq hmax H (fun _ _ h => Or.inl h)
    ⟨_, EdgeInsertion.pendant_genusZero G R a v hv hz⟩
  have ha : H.Adj a.fst v := Or.inr (Or.inl ⟨rfl,rfl⟩)
  rw [hHG] at ha
  exact hv ha.mem_support_right

/-- With at least one edge, maximal genus-zero extensions are connected. -/
theorem maximal_connected_of_dart (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (a : G.Dart) : G.Connected := by
  have hs := R.maximal_support_univ hz hmax a
  have : Nonempty V := ⟨a.fst⟩
  constructor
  intro u v
  apply R.maximal_support_reachable hz hmax <;> rw [hs] <;> trivial

end JSP512Probe.RotationSystem
