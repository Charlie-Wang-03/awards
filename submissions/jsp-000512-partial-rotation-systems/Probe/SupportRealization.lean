import Probe.FaceVertexSimplicity

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- If the supported vertices form one component, every other component is
exactly one isolated vertex. -/
theorem component_support_count (a : V) (ha : a ∈ G.support)
    (hc : ∀ x ∈ G.support, G.Reachable a x) :
    Nat.card G.ConnectedComponent + Nat.card G.support = Fintype.card V + 1 := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let A := {v : V // v ∉ G.support}
  have hcount := quotient_card_remove_class ((⊥ : Setoid A)) G.reachableSetoid a
    (fun x : A => x.val) (by
      intro x y
      constructor
      · intro h
        apply Subtype.ext
        by_contra hn
        exact x.property (SimpleGraph.mem_support_of_reachable hn h)
      · intro h
        change x = y at h
        subst y
        exact SimpleGraph.Reachable.rfl) (by
      intro y
      constructor
      · rintro ⟨x,rfl⟩ h
        by_cases hh : x.val = a
        · exact x.property (hh ▸ ha)
        · exact x.property (SimpleGraph.mem_support_of_reachable hh h.symm)
      · intro h
        have hy : y ∉ G.support := fun hy => h (hc y hy)
        exact ⟨⟨y,hy⟩,rfl⟩)
  let eqv : Quotient (⊥ : Setoid A) ≃ A :=
    ⟨Quotient.lift id (fun _ _ h => h), Quotient.mk _, by
      intro q
      induction q using Quotient.inductionOn with
      | h x => rfl, fun _ => rfl⟩
  have heq : Nat.card (Quotient ((⊥ : Setoid A))) = Nat.card A :=
    Nat.card_congr eqv
  rw [heq] at hcount
  have hcomp := Fintype.card_subtype_compl (fun v : V => v ∈ G.support)
  have hle := Fintype.card_subtype_le (fun v : V => v ∈ G.support)
  change Nat.card G.ConnectedComponent = Nat.card A + 1 at hcount
  simp only [Nat.card_eq_fintype_card] at hcount ⊢
  have hs' : Fintype.card {x : V // x ∈ G.support} = Fintype.card G.support :=
    Fintype.card_congr (show {x : V // x ∈ G.support} ≃ G.support from Equiv.refl _)
  have ha' : Fintype.card {x : V // x ∉ G.support} = Fintype.card A :=
    Fintype.card_congr (show {x : V // x ∉ G.support} ≃ A from Equiv.refl _)
  rw [hs', ha'] at hcomp
  rw [hs'] at hle
  omega

omit [DecidableEq V] in
/-- Removing isolated vertices by realizing rotation orbits preserves genus zero
when the supported graph and its realization are connected. -/
theorem realized_genusZero (hz : R.HasGenusZero)
    (hc : Nat.card G.ConnectedComponent + Nat.card G.support = Fintype.card V + 1)
    (hconn : (RefinedRotation.graph G R.rotate R.source).Connected) :
    letI : Fintype (RefinedRotation.Vertex G R.rotate) := Fintype.ofFinite _
    (RefinedRotation.rotation G R.rotate R.source).HasGenusZero := by
  classical
  let : Fintype (RefinedRotation.Vertex G R.rotate) := Fintype.ofFinite _
  let H := RefinedRotation.graph G R.rotate R.source
  let S := RefinedRotation.rotation G R.rotate R.source
  have hvertices := R.vertexOrbit_card
  have hcomp := component_card_of_connected H hconn
  have he := RefinedRotation.edge_count G R.rotate R.source
  have hf := RefinedRotation.face_count G R.rotate R.source
  have hsupport : supportSize (G := H) =
      (Fintype.card (RefinedRotation.Vertex G R.rotate) : ℤ) := by
    unfold supportSize
    rw [RefinedRotation.full_support]
    simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv]
  change S.eulerDefect = 0
  change R.eulerDefect = 0 at hz
  unfold eulerDefect
  change 2 * (Nat.card H.ConnectedComponent : ℤ) -
    2 * Fintype.card (RefinedRotation.Vertex G R.rotate) +
    supportSize (G := H) + Nat.card H.edgeSet - S.faceCount = 0
  rw [hcomp, hsupport, he, hf]
  change 2 * (1 : ℤ) - 2 * Fintype.card (RefinedRotation.Vertex G R.rotate) +
    Fintype.card (RefinedRotation.Vertex G R.rotate) + Nat.card G.edgeSet - R.faceCount = 0
  unfold eulerDefect supportSize at hz
  simp only [Nat.card_eq_fintype_card] at hvertices hc hz ⊢
  change Fintype.card (RefinedRotation.Vertex G R.rotate) = Fintype.card G.support at hvertices
  omega

end JSP512Probe.RotationSystem
