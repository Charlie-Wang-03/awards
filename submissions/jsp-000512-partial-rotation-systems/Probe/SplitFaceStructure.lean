import Probe.SplitSeparation
import Probe.CofacialInsertion
import Probe.ComponentRotation
import Probe.SplitSideRotation

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- Splitting one permutation cycle partitions it into the two marked cycles. -/
theorem split_cycle_partition (σ : Equiv.Perm α) (a b d : α) (hne : a ≠ b)
    (hab : σ.SameCycle a b) :
    σ.SameCycle d a ↔ (Equiv.swap a b * σ).SameCycle d a ∨
      (Equiv.swap a b * σ).SameCycle d b := by
  let τ := Equiv.swap a b * σ
  have hsep : ¬τ.SameCycle a b := swap_splits σ a b hne hab
  constructor
  · intro hd
    have hh := (swap_cycles_label τ a b hsep d a).mp (by
      simpa only [τ, ← mul_assoc, Equiv.swap_mul_self, one_mul] using hd)
    have hn : (Quotient.mk (Equiv.Perm.SameCycle.setoid τ) a) ≠ Quotient.mk _ b :=
      fun h => hsep (Quotient.exact h)
    unfold joinedLabel at hh
    rw [ite_eq_right hn] at hh
    split_ifs at hh with hd'
    · exact Or.inr (Quotient.exact hd')
    · exact Or.inl (Quotient.exact hh)
  · rintro (hd | hd)
    · have hh := swap_preserves_old_cycles τ a b hsep hd
      simpa only [τ, ← mul_assoc, Equiv.swap_mul_self, one_mul] using hh
    · have hh := swap_preserves_old_cycles τ a b hsep hd
      have hdb : σ.SameCycle d b := by
        simpa only [τ, ← mul_assoc, Equiv.swap_mul_self, one_mul] using hh
      exact hdb.trans hab.symm
end JSP512Probe.CycleSurgery

namespace JSP512Probe.RefinedRotation
open RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart)
  (hs : ∀ d, (σ d).fst = d.fst)

omit [DecidableEq V] in
/-- Exact facial step for the actual graph realizing split rotation fibers. -/
theorem face_dart (d : G.Dart) :
    (rotation G σ hs).face (dartEquiv G σ hs d) = dartEquiv G σ hs (σ d.symm) := by
  change dartEquiv G σ hs (σ ((dartEquiv G σ hs).symm (dartEquiv G σ hs d).symm)) = _
  rw [← dart_reverse, Equiv.symm_apply_apply]
end JSP512Probe.RefinedRotation

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- Actual split facial cycles are conjugate to swapping the two old face targets. -/
theorem split_face_cycles (d e : G.Dart) :
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    S.face.SameCycle (E d) (E e) ↔ (Equiv.swap a b * R.face).SameCycle d e := by
  classical
  dsimp only
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  let : Fintype (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Dart :=
    Fintype.ofEquiv G.Dart E
  apply sameCycle_embedding _ _ E E.injective
  intro d
  exact (RefinedRotation.face_dart G (R.splitRotation a b) (R.split_source a b hab) d).symm

/-- The modified old outer face becomes exactly the two split outer faces. -/
theorem split_outer_partition (hne : a ≠ b) (hf : R.face.SameCycle a b) (d : G.Dart) :
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    R.face.SameCycle d a ↔ S.face.SameCycle (E d) (E a) ∨ S.face.SameCycle (E d) (E b) := by
  dsimp only
  have ha := R.split_face_cycles a b hab d a
  have hb := R.split_face_cycles a b hab d b
  dsimp only at ha hb
  rw [ha, hb]
  exact split_cycle_partition R.face a b d hne hf

/-- Every face outside the modified old outer face keeps its triangular return
in the actual split graph. -/
theorem split_preserves_inner_triangle (hf : R.face.SameCycle a b) (d : G.Dart)
    (hd : ¬R.face.SameCycle a d) (ht : R.face (R.face (R.face d)) = d) :
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    S.face (S.face (S.face (E d))) = E d := by
  dsimp only
  have step : ∀ x, R.face.SameCycle d x →
      (R.splitRotation a b) x.symm = R.face x := by
    intro x hx
    have ha : R.face x ≠ a := fun he => hd (he ▸ hx.apply_right).symm
    have hb : R.face x ≠ b := fun he => hd (hf.trans (he ▸ hx.apply_right).symm)
    exact Equiv.swap_apply_of_ne_of_ne ha hb
  rw [RefinedRotation.face_dart, step d Equiv.Perm.SameCycle.rfl,
    RefinedRotation.face_dart, step (R.face d) Equiv.Perm.SameCycle.rfl.apply_right,
    RefinedRotation.face_dart, step (R.face (R.face d)) Equiv.Perm.SameCycle.rfl.apply_right.apply_right, ht]

/-- Outside the two split outer faces, every actual refined face is triangular. -/
theorem split_inner_faces (hne : a ≠ b) (hf : R.face.SameCycle a b)
    (hi : ∀ d, ¬R.face.SameCycle a d → R.face (R.face (R.face d)) = d) :
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    ∀ x, ¬S.face.SameCycle (E a) x → ¬S.face.SameCycle (E b) x →
      S.face (S.face (S.face x)) = x := by
  dsimp only
  intro x hxa hxb
  obtain ⟨d, rfl⟩ := (RefinedRotation.dartEquiv G (R.splitRotation a b)
    (R.split_source a b hab)).surjective x
  have hd : ¬R.face.SameCycle a d := by
    intro hh
    rcases (R.split_outer_partition a b hab hne hf d).mp hh.symm with hh | hh
    · exact hxa hh.symm
    · exact hxb hh.symm
  exact R.split_preserves_inner_triangle a b hab hf d hd (hi d hd)

/-- In the component of the first split copy, only its own marked outer face
can be nontriangular: the second outer face lies in the other component. -/
theorem split_component_inner (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (hi : ∀ d, ¬R.face.SameCycle a d → R.face (R.face (R.face d)) = d) :
    let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    ∀ x, H.Reachable (E a).fst x.fst → ¬S.face.SameCycle (E a) x →
      S.face (S.face (S.face x)) = x := by
  classical
  dsimp only
  let : Fintype (RefinedRotation.Vertex G (R.splitRotation a b)) := Fintype.ofFinite _
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  intro x hx hnot
  apply R.split_inner_faces a b hab hne hf hi x hnot
  intro hb
  have hr : H.Reachable (E b).fst x.fst := EdgeInsertion.face_reachable H S (E b) x hb
  exact R.split_copies_not_reachable a b hab hne hc hz hf (hx.trans hr.symm)

/-- The actual restricted rotation of the first split component has a marked
outer face and triangular returns on every other face. -/
theorem split_restricted_inner (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (hi : ∀ d, ¬R.face.SameCycle a d → R.face (R.face (R.face d)) = d) :
    let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
    letI : DecidableRel H.Adj := Classical.decRel _
    let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
    let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
    let C := H.connectedComponentMk (E a).fst
    ∃ root : C.toSimpleGraph.Dart, ∀ x, ¬(S.componentRotation C).face.SameCycle root x →
      (S.componentRotation C).face ((S.componentRotation C).face
        ((S.componentRotation C).face x)) = x := by
  classical
  let : Fintype (RefinedRotation.Vertex G (R.splitRotation a b)) := Fintype.ofFinite _
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  let C := H.connectedComponentMk (E a).fst
  let hclosed := fun u (hu : u ∈ C.supp) v (huv : H.Adj u v) =>
    C.mem_supp_of_adj_mem_supp hu huv
  let F := closedDartEquiv C.supp hclosed
  let root := F.symm ⟨E a, rfl⟩
  have hroot : (F root).val = E a := by
    simp only [root, Equiv.apply_symm_apply]
  refine ⟨root, ?_⟩
  intro x hx
  apply S.restrictClosed_triangle C.supp hclosed x
  apply R.split_component_inner a b hab hne hc hz hf hi (F x).val
  · exact C.reachable_of_mem_supp rfl (F x).property
  · intro hh
    apply hx
    apply (S.restrictClosed_face_cycles C.supp hclosed root x).mpr
    rwa [hroot]

/-- The induced original-vertex side inherits the actual component's marked
outer face and triangular inner faces through the proved graph isomorphism. -/
theorem splitSideRotation_inner (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (hi : ∀ d, ¬R.face.SameCycle a d → R.face (R.face (R.face d)) = d) :
    let T := R.splitSideRotation a b hab hne hc hz hf a
    ∃ root, ∀ x, ¬T.face.SameCycle root x → T.face (T.face (T.face x)) = x := by
  classical
  let σ := R.splitRotation a b
  let : Fintype (RefinedRotation.Vertex G σ) := Fintype.ofFinite _
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let S := RefinedRotation.rotation G σ (R.split_source a b hab)
  let C := H.connectedComponentMk (RefinedRotation.vertex G σ a)
  let : Fintype C := Fintype.ofFinite _
  let : Fintype (R.splitSide a b hab a) := Fintype.ofFinite _
  let e := R.split_component_iso a b hab hne hc hz hf a
  obtain ⟨root, hroot⟩ := R.split_restricted_inner a b hab hne hc hz hf hi
  refine ⟨isoDarts e root, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := (isoDarts e).surjective x
  apply (S.componentRotation C).mapIso_triangle e y
  apply hroot y
  intro hy
  apply hx
  exact ((S.componentRotation C).mapIso_face_cycles e root y).mpr hy

end JSP512Probe.RotationSystem
