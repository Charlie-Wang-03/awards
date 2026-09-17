import Probe.FaceVertexSimplicity

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

include hab in
/-- The split source fiber consists of exactly the two marked rotation cycles. -/
theorem split_cycles_at (hne : a ≠ b) (d : G.Dart) (hd : d.fst = a.fst) :
    (R.splitRotation a b).SameCycle d a ∨ (R.splitRotation a b).SameCycle d b := by
  classical
  let σ := R.splitRotation a b
  have hsep : ¬σ.SameCycle a b := swap_splits R.rotate a b hne (R.local_cycle a b hab)
  have hh := (swap_cycles_label σ a b hsep d a).mp (by
    simpa only [σ,splitRotation,← mul_assoc,Equiv.swap_mul_self,one_mul]
      using R.local_cycle d a hd)
  have hn : (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) a) ≠ Quotient.mk _ b :=
    fun h => hsep (Quotient.exact h)
  unfold joinedLabel at hh
  rw [ite_eq_right hn] at hh
  split_ifs at hh with hd'
  · exact Or.inr (Quotient.exact hd')
  · exact Or.inl (Quotient.exact hh)

/-- Every refined vertex can reach at least one of the two copies of the split vertex. -/
theorem split_reaches_copies (hne : a ≠ b) (hc : G.Preconnected) :
    ∀ d : G.Dart,
      (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
        (RefinedRotation.vertex G (R.splitRotation a b) d)
        (RefinedRotation.vertex G (R.splitRotation a b) a) ∨
      (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
        (RefinedRotation.vertex G (R.splitRotation a b) d)
        (RefinedRotation.vertex G (R.splitRotation a b) b) := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  have along : ∀ {x y}, G.Walk x y → y = a.fst → ∀ d : G.Dart, d.fst = x →
      H.Reachable (q d) (q a) ∨ H.Reachable (q d) (q b) := by
    intro x y p
    induction p with
    | nil =>
      intro hy d hd
      rcases R.split_cycles_at a b hab hne d (hd.trans hy) with h | h
      · rw [show q d = q a from Quotient.sound h]; exact Or.inl SimpleGraph.Reachable.rfl
      · rw [show q d = q b from Quotient.sound h]; exact Or.inr SimpleGraph.Reachable.rfl
    | @cons x z y hxz p ih =>
      intro hy d hd
      by_cases ha : d.fst = a.fst
      · rcases R.split_cycles_at a b hab hne d ha with h | h
        · rw [show q d = q a from Quotient.sound h]; exact Or.inl SimpleGraph.Reachable.rfl
        · rw [show q d = q b from Quotient.sound h]; exact Or.inr SimpleGraph.Reachable.rfl
      · let e : G.Dart := ⟨(x,z),hxz⟩
        have he : q d = q e := Quotient.sound (R.split_cycles_away a b hab hne d e ha hd)
        have edge : H.Reachable (q d) (q e.symm) := by
          rw [he]
          exact (show H.Adj (q e) (q e.symm) from ⟨e,rfl,rfl⟩).reachable
        exact (ih hy e.symm rfl).elim (fun h => Or.inl (edge.trans h))
          (fun h => Or.inr (edge.trans h))
  intro d
  obtain ⟨p⟩ := hc d.fst a.fst
  exact along p rfl d rfl

/-- Splitting one vertex of a connected graph creates at most two components. -/
theorem split_component_count_le_two (hne : a ≠ b) (hc : G.Preconnected) :
    Nat.card (RefinedRotation.graph G (R.splitRotation a b)
      (R.split_source a b hab)).ConnectedComponent ≤ 2 := by
  classical
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  let f : Bool → H.ConnectedComponent := fun z => if z then H.connectedComponentMk (q a)
    else H.connectedComponentMk (q b)
  have hf : Function.Surjective f := by
    intro c
    induction c using Quot.inductionOn with
    | h v =>
      induction v using Quotient.inductionOn with
      | h d =>
        rcases R.split_reaches_copies a b hab hne hc d with ha | hb
        · exact ⟨true,(SimpleGraph.ConnectedComponent.eq.mpr ha).symm⟩
        · exact ⟨false,(SimpleGraph.ConnectedComponent.eq.mpr hb).symm⟩
  have := Fintype.ofFinite H.ConnectedComponent
  have hh := Fintype.card_le_of_surjective f hf
  simp only [Fintype.card_bool] at hh
  simpa only [← Nat.card_eq_fintype_card] using hh
/-- A same-face split of a zero-genus connected rotation separates into exactly
two components, and its actual refined rotation still has zero genus. -/
theorem split_separates_genusZero (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hface : R.face.SameCycle a b) :
    letI : Fintype (RefinedRotation.Vertex G (R.splitRotation a b)) := Fintype.ofFinite _
    Nat.card (RefinedRotation.graph G (R.splitRotation a b)
      (R.split_source a b hab)).ConnectedComponent = 2 ∧
    (RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)).HasGenusZero := by
  classical
  let σ := R.splitRotation a b
  let Q := RefinedRotation.Vertex G σ
  let : Fintype Q := Fintype.ofFinite _
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let S := RefinedRotation.rotation G σ (R.split_source a b hab)
  have : Nontrivial V := ⟨⟨a.fst,a.snd,a.adj.ne⟩⟩
  have hsupp := hc.support_eq_univ
  have holdcomp := component_card_of_connected G (show G.Connected from ⟨hc⟩)
  have he : Nat.card H.edgeSet = Nat.card G.edgeSet :=
    RefinedRotation.edge_count G σ (R.split_source a b hab)
  have hvertices : Fintype.card Q = Fintype.card V + 1 := by
    have hh := swap_split_count R.rotate a b hne (R.local_cycle a b hab)
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
    have hh := swap_split_count R.face a b hne hface
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
  have hu : Nat.card H.ConnectedComponent ≤ 2 := R.split_component_count_le_two a b hab hne hc
  change R.eulerDefect = 0 at hz
  unfold eulerDefect at hz hnonneg
  change 0 ≤ 2 * (Nat.card H.ConnectedComponent : ℤ) - 2 * Fintype.card Q +
    supportSize (G := H) + Nat.card H.edgeSet - S.faceCount at hnonneg
  rw [hsupport, he, hfaces] at hnonneg
  rw [holdcomp, holdsupport] at hz
  have hcount : Nat.card H.ConnectedComponent = 2 := by omega
  refine ⟨hcount,?_⟩
  change S.eulerDefect = 0
  unfold eulerDefect
  change 2 * (Nat.card H.ConnectedComponent : ℤ) - 2 * Fintype.card Q +
    supportSize (G := H) + Nat.card H.edgeSet - S.faceCount = 0
  rw [hcount,hsupport,he,hfaces]
  omega

/-- The two marked copies lie in different components after a same-face split. -/
theorem split_copies_not_reachable (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hface : R.face.SameCycle a b) :
    ¬(RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) a)
      (RefinedRotation.vertex G (R.splitRotation a b) b) := by
  classical
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  intro h
  have reach : ∀ d : G.Dart, H.Reachable (q d) (q a) := by
    intro d
    exact (R.split_reaches_copies a b hab hne hc d).elim id (fun hb => hb.trans h.symm)
  have : Nonempty (RefinedRotation.Vertex G (R.splitRotation a b)) := ⟨q a⟩
  have conn : H.Connected := by
    constructor
    intro x y
    induction x using Quotient.inductionOn with
    | h d =>
      induction y using Quotient.inductionOn with
      | h e => exact (reach d).trans (reach e).symm
  have h1 := component_card_of_connected H conn
  have h2 := (R.split_separates_genusZero a b hab hne hc hz hface).1
  change Nat.card H.ConnectedComponent = 2 at h2
  omega

end JSP512Probe.RotationSystem
