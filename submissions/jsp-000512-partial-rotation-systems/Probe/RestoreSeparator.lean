import Probe.SplitSides
import Probe.ChordExposesCut

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Add the deleted vertex back to a projected side. -/
def restoreSide (v : V) (A : Set {u : V | u ≠ v}) : Set V :=
  {u | u = v ∨ ∃ x ∈ A, x.val = u}

omit [Fintype V] [DecidableEq V] in
theorem survivor_mem_restoreSide (v : V) (A : Set {u : V | u ≠ v}) (x : {u : V | u ≠ v}) :
    x.val ∈ restoreSide v A ↔ x ∈ A := by
  constructor
  · rintro (h | ⟨y,hy,he⟩)
    · exact False.elim (x.property h)
    · have hh : y = x := Subtype.ext he
      exact hh ▸ hy
  · intro h
    exact Or.inr ⟨x,h,rfl⟩

/-- Restore one endpoint to two smaller sides of its deleted graph. Coverage,
edge containment and endpoint-only overlap hold in the original graph. -/
theorem restore_separator {G : SimpleGraph V} (v : V)
    (A B : Set {u : V | u ≠ v}) (w : {u : V | u ≠ v})
    (cover : ∀ x, x ∈ A ∨ x ∈ B)
    (edges : ∀ x y : {u : V | u ≠ v}, G.Adj x.val y.val →
      (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (inter : ∀ x, (x ∈ A ∧ x ∈ B) ↔ x = w)
    (properA : ∃ x, x ∉ A) (properB : ∃ x, x ∉ B) :
    (∀ u, u ∈ restoreSide v A ∨ u ∈ restoreSide v B) ∧
    (∀ u z, G.Adj u z →
      (u ∈ restoreSide v A ∧ z ∈ restoreSide v A) ∨
      (u ∈ restoreSide v B ∧ z ∈ restoreSide v B)) ∧
    (∀ u, (u ∈ restoreSide v A ∧ u ∈ restoreSide v B) ↔ u = v ∨ u = w.val) ∧
    Nat.card (restoreSide v A) < Fintype.card V ∧
    Nat.card (restoreSide v B) < Fintype.card V := by
  classical
  have cov : ∀ u, u ∈ restoreSide v A ∨ u ∈ restoreSide v B := by
    intro u
    by_cases hu : u = v
    · exact Or.inl (Or.inl hu)
    · exact (cover ⟨u,hu⟩).elim
        (fun h => Or.inl ((survivor_mem_restoreSide v A ⟨u,hu⟩).mpr h))
        (fun h => Or.inr ((survivor_mem_restoreSide v B ⟨u,hu⟩).mpr h))
  refine ⟨cov,?_,?_,?_,?_⟩
  · intro u z huz
    by_cases hu : u = v
    · exact (cov z).elim (fun h => Or.inl ⟨Or.inl hu,h⟩) (fun h => Or.inr ⟨Or.inl hu,h⟩)
    · by_cases hz : z = v
      · exact (cov u).elim (fun h => Or.inl ⟨h,Or.inl hz⟩) (fun h => Or.inr ⟨h,Or.inl hz⟩)
      · rcases edges ⟨u,hu⟩ ⟨z,hz⟩ huz with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact Or.inl ⟨(survivor_mem_restoreSide v A ⟨u,hu⟩).mpr ha,
            (survivor_mem_restoreSide v A ⟨z,hz⟩).mpr hb⟩
        · exact Or.inr ⟨(survivor_mem_restoreSide v B ⟨u,hu⟩).mpr ha,
            (survivor_mem_restoreSide v B ⟨z,hz⟩).mpr hb⟩
  · intro u
    by_cases hu : u = v
    · subst u
      exact ⟨fun _ => Or.inl rfl,fun _ => ⟨Or.inl rfl,Or.inl rfl⟩⟩
    · have hh := inter ⟨u,hu⟩
      constructor
      · rintro ⟨ha,hb⟩
        exact Or.inr (congrArg Subtype.val (hh.mp
          ⟨(survivor_mem_restoreSide v A ⟨u,hu⟩).mp ha,
           (survivor_mem_restoreSide v B ⟨u,hu⟩).mp hb⟩))
      · rintro (hv | hw)
        · exact False.elim (hu hv)
        · have he : (⟨u,hu⟩ : {u : V | u ≠ v}) = w := Subtype.ext hw
          exact ⟨(survivor_mem_restoreSide v A ⟨u,hu⟩).mpr (hh.mpr he).1,
            (survivor_mem_restoreSide v B ⟨u,hu⟩).mpr (hh.mpr he).2⟩
  · obtain ⟨x,hx⟩ := properA
    have hn : x.val ∉ restoreSide v A := fun h => hx ((survivor_mem_restoreSide v A x).mp h)
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hn
  · obtain ⟨x,hx⟩ := properB
    have hn : x.val ∉ restoreSide v B := fun h => hx ((survivor_mem_restoreSide v B x).mp h)
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hn
/-- An actual boundary chord separates the original graph into two strictly
smaller induced vertex sets covering every edge, with exactly its endpoints
in their intersection. Facial disk data on the two induced graphs is separate. -/
theorem chord_vertex_separator {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (outer : G.Dart) (hz : R.HasGenusZero) (hc : G.Preconnected)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ A B : Set V,
      (∀ u, u ∈ A ∨ u ∈ B) ∧
      (∀ u z, G.Adj u z → (u ∈ A ∧ z ∈ A) ∨ (u ∈ B ∧ z ∈ B)) ∧
      (∀ u, (u ∈ A ∧ u ∈ B) ↔ u = outer.snd ∨ u = a.fst) ∧
      Nat.card A < Fintype.card V ∧ Nat.card B < Fintype.card V := by
  classical
  obtain ⟨root,hr⟩ := R.outer_region_single_orbit outer hsimple hinner hcorner
  obtain ⟨x,y,hx,hy,hne,hxy,hu⟩ :=
    R.chord_exposes_repeated_vertex outer hsimple hinner root hr a ha hadj hleft hright
  let S := R.deleteVertex outer.snd
  have hs := R.boundary_deleteVertex_genusZero outer hz hc hsimple hinner hcorner
  have hconn := R.outer_vertex_deleted_connected outer hc hsimple hinner
  let A := S.splitSide x y hxy x
  let B := S.splitSide x y hxy y
  have hf := hx.symm.trans hy
  have hp := S.split_sides_proper x y hxy hne hconn.preconnected hs hf
  have result := restore_separator (G := G) outer.snd A B x.fst
    (S.split_sides_cover x y hxy hne hconn.preconnected)
    (S.split_sides_edges x y hxy hne hconn.preconnected)
    (S.split_sides_inter x y hxy hne hconn.preconnected hs hf)
    ⟨y.snd,hp.2.2⟩ ⟨x.snd,hp.1.2⟩
  refine ⟨restoreSide outer.snd A,restoreSide outer.snd B,?_⟩
  simpa only [hu] using result

end JSP512Probe.RotationSystem
