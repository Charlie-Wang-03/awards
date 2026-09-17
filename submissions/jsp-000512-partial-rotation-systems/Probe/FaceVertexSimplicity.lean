import Probe.VertexSplitModel

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

def splitRotation := Equiv.swap a b * R.rotate

include hab in
omit [Fintype V] [DecidableRel G.Adj] in
theorem split_source (d : G.Dart) : (R.splitRotation a b d).fst = d.fst := by
  change (Equiv.swap a b (R.rotate d)).fst = d.fst
  by_cases ha : R.rotate d = a
  · rw [ha, Equiv.swap_apply_left, ← hab, ← ha, R.source]
  · by_cases hb : R.rotate d = b
    · rw [hb, Equiv.swap_apply_right, hab, ← hb, R.source]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb, R.source]

include hab in
/-- Away from the split vertex, rotation fibers remain single cycles. -/
theorem split_cycles_away (hne : a ≠ b) (d e : G.Dart)
    (hd : d.fst ≠ a.fst) (hde : d.fst = e.fst) :
    (R.splitRotation a b).SameCycle d e := by
  let σ := R.splitRotation a b
  have hsep : ¬σ.SameCycle a b := swap_splits R.rotate a b hne (R.local_cycle a b hab)
  have hh := (swap_cycles_label σ a b hsep d e).mp (by
    simpa only [σ, splitRotation, ← mul_assoc, Equiv.swap_mul_self, one_mul]
      using R.local_cycle d e hde)
  have hd' : (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) d) ≠ Quotient.mk _ b := by
    intro h
    have hs := RefinedRotation.cycle_source G σ (R.split_source a b hab) (Quotient.exact h)
    exact hd (hs.trans hab.symm)
  have he' : (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) e) ≠ Quotient.mk _ b := by
    intro h
    have hs := RefinedRotation.cycle_source G σ (R.split_source a b hab) (Quotient.exact h)
    exact hd (hde.trans (hs.trans hab.symm))
  simp only [joinedLabel, ite_eq_right hd', ite_eq_right he'] at hh
  exact Quotient.exact hh

include hab in
/-- Splitting a vertex preserves connectivity when deleting that vertex was connected. -/
theorem split_graph_connected (hne : a ≠ b)
    (hsupport : G.support = Set.univ)
    (hdel : (G.induce {v | v ≠ a.fst}).Preconnected) :
    (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Connected := by
  classical
  let σ := R.splitRotation a b
  let S := RefinedRotation.graph G σ (R.split_source a b hab)
  let K := G.induce {v | v ≠ a.fst}
  let q := RefinedRotation.vertex G σ
  have hex : ∀ v : V, ∃ d : G.Dart, d.fst = v := by
    intro v
    have hv : v ∈ G.support := by rw [hsupport]; trivial
    obtain ⟨w,hw⟩ := G.mem_support.mp hv
    exact ⟨⟨(v,w),hw⟩,rfl⟩
  choose rep hrep using hex
  let f : {v | v ≠ a.fst} → RefinedRotation.Vertex G σ := fun v => q (rep v.val)
  have lift_eq : ∀ (d : G.Dart) (hd : d.fst ≠ a.fst), q d = f ⟨d.fst,hd⟩ := by
    intro d hd
    exact Quotient.sound (R.split_cycles_away a b hab hne d (rep d.fst) hd (hrep _).symm)
  let j : K →g S := ⟨f, by
    intro x y hxy
    let d : G.Dart := ⟨(x.val,y.val),hxy⟩
    exact ⟨d,lift_eq d x.property,lift_eq d.symm y.property⟩⟩
  have away : ∀ (d e : G.Dart), d.fst ≠ a.fst → e.fst ≠ a.fst → S.Reachable (q d) (q e) := by
    intro d e hd he
    rw [lift_eq d hd, lift_eq e he]
    exact (hdel ⟨d.fst,hd⟩ ⟨e.fst,he⟩).map j
  have reach : ∀ d : G.Dart, S.Reachable (q d) (q a.symm) := by
    intro d
    by_cases hd : d.fst = a.fst
    · have hn : d.symm.fst ≠ a.fst := by
        change d.snd ≠ a.fst
        rw [← hd]
        exact d.snd_ne_fst
      exact (show S.Adj (q d) (q d.symm) from ⟨d,rfl,rfl⟩).reachable.trans
        (away d.symm a.symm hn a.snd_ne_fst)
    · exact away d a.symm hd a.snd_ne_fst
  have : Nonempty (RefinedRotation.Vertex G σ) := ⟨q a⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | h d =>
    induction y using Quotient.inductionOn with
    | h e => exact (reach d).trans (reach e).symm

/-- Connected graphs have precisely one connected component. -/
theorem component_card_of_connected {W : Type*} (H : SimpleGraph W) (hc : H.Connected) :
    Nat.card H.ConnectedComponent = 1 := by
  have := hc.nonempty
  have := hc.preconnected.subsingleton_connectedComponent
  obtain ⟨w⟩ := hc.nonempty
  let : Unique H.ConnectedComponent := ⟨⟨H.connectedComponentMk w⟩, fun _ => Subsingleton.elim _ _⟩
  exact Nat.card_unique

/-- In a maximal genus-zero graph, a facial orbit visits each vertex at most once. -/
theorem maximal_face_vertex_injective (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hf : R.face.SameCycle a b)
    (hv : a.fst = b.fst) : a = b := by
  classical
  by_contra hne
  let σ := R.splitRotation a b
  let Q := RefinedRotation.Vertex G σ
  let : Fintype Q := Fintype.ofFinite _
  let H := RefinedRotation.graph G σ (R.split_source a b hv)
  let S := RefinedRotation.rotation G σ (R.split_source a b hv)
  have hsupp := R.maximal_support_univ hz hmax a
  have hconn := R.split_graph_connected a b hv hne hsupp
    (R.maximal_vertex_deleted_preconnected hz hmax a.fst)
  have hcomp : Nat.card H.ConnectedComponent = 1 := component_card_of_connected H hconn
  have holdcomp := component_card_of_connected G (R.maximal_connected_of_dart hz hmax a)
  have he : Nat.card H.edgeSet = Nat.card G.edgeSet :=
    RefinedRotation.edge_count G σ (R.split_source a b hv)
  have hvertices : Fintype.card Q = Fintype.card V + 1 := by
    have hh := swap_split_count R.rotate a b hne (R.local_cycle a b hv)
    have ho := R.vertexOrbit_card
    rw [hsupp] at ho
    have ho' : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid R.rotate)) =
        Fintype.card V := by
      simpa only [VertexOrbit, Nat.card_eq_fintype_card, Fintype.card_setUniv] using ho
    rw [ho'] at hh
    change Nat.card Q = Fintype.card V + 1 at hh
    simpa only [Nat.card_eq_fintype_card] using hh
  have hfaces : S.faceCount = R.faceCount + 1 := by
    rw [RefinedRotation.face_count]
    have hh := swap_split_count R.face a b hne hf
    simpa only [σ, splitRotation, mul_assoc, face, faceCount, FaceOrbit] using hh
  have hsupport : supportSize (G := H) = (Fintype.card Q : ℤ) := by
    unfold supportSize
    rw [RefinedRotation.full_support]
    simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv]
    rfl
  have holdsupport : supportSize (G := G) = (Fintype.card V : ℤ) := by
    unfold supportSize
    rw [hsupp]
    simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv]
  have hnonneg := defect_nonnegative H S
  change R.eulerDefect = 0 at hz
  unfold eulerDefect at hz hnonneg
  change 0 ≤ 2 * (Nat.card H.ConnectedComponent : ℤ) - 2 * Fintype.card Q +
    supportSize (G := H) + Nat.card H.edgeSet - S.faceCount at hnonneg
  rw [hcomp, hsupport, he, hfaces] at hnonneg
  rw [holdcomp, holdsupport] at hz
  omega

/-- The source map is injective on the darts of each facial orbit. -/
theorem maximal_face_source_injOn (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (root : G.Dart) :
    Set.InjOn (fun d : G.Dart => d.fst) {d | R.face.SameCycle root d} := by
  intro d hd e he hsource
  exact R.maximal_face_vertex_injective d e hz hmax (hd.symm.trans he) hsource

/-- A simple facial boundary has no more darts than the graph has vertices. -/
theorem maximal_face_size_le (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (root : G.Dart) :
    Nat.card {d : G.Dart // R.face.SameCycle root d} ≤ Fintype.card V := by
  classical
  let : Fintype {d : G.Dart // R.face.SameCycle root d} := Fintype.ofFinite _
  have hi : Function.Injective (fun d : {d : G.Dart // R.face.SameCycle root d} => d.val.fst) := by
    intro d e h
    apply Subtype.ext
    exact R.maximal_face_source_injOn hz hmax root d.property e.property h
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective _ hi

end JSP512Probe.RotationSystem
