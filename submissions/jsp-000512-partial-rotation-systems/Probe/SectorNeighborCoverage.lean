import Probe.ComplementarySectorSide

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

omit [DecidableEq V] in
/-- Two concrete inverse-rotation paths joined at the exceptional dart cover
all outgoing darts. This applies to the existing interval witnesses directly;
no identification with separately chosen first-hit witnesses is required. -/
theorem sector_paths_cover (stop : G.Dart) (hs : stop.fst = v)
    (n m : ℕ) (d : Fin (n+1) → G.Dart) (e : Fin (m+1) → G.Dart)
    (hd : ∀ i, (d i).fst = v) (he : ∀ j, (e j).fst = v)
    (hds : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hes : ∀ j : Fin m, R.rotate (e j.succ) = e j.castSucc)
    (hstop : R.rotate stop = d (Fin.last n))
    (he0 : R.rotate (e 0) = stop) (hd0 : R.rotate (d 0) = e (Fin.last m)) :
    ∀ x : G.Dart, x.fst = v ↔ x = stop ∨ (∃ i, x = d i) ∨ (∃ j, x = e j) := by
  let P := fun x : G.Dart => x = stop ∨ (∃ i, x = d i) ∨ (∃ j, x = e j)
  have hclosed : ∀ x, P x → P (R.rotate x) := by
    intro x hx
    rcases hx with rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact Or.inr (Or.inl ⟨Fin.last n,hstop⟩)
    · induction i using Fin.cases with
      | zero => exact Or.inr (Or.inr ⟨Fin.last m,hd0⟩)
      | succ i => exact Or.inr (Or.inl ⟨i.castSucc,hds i⟩)
    · induction j using Fin.cases with
      | zero => exact Or.inl he0
      | succ j => exact Or.inr (Or.inr ⟨j.castSucc,hes j⟩)
  intro x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := (R.local_cycle stop x (hs.trans hx.symm)).exists_nat_pow_eq
    have hp : ∀ k : ℕ, P ((R.rotate ^ k) stop) := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hclosed _ ih
    exact hk ▸ hp k
  · rintro (rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩)
    · exact hs
    · exact hd i
    · exact he j

omit [DecidableEq V] in
/-- Exact neighbor coverage for the two already-constructed sector paths. -/
theorem sector_paths_neighbors (stop : G.Dart) (hs : stop.fst = v)
    (n m : ℕ) (d : Fin (n+1) → G.Dart) (e : Fin (m+1) → G.Dart)
    (hd : ∀ i, (d i).fst = v) (he : ∀ j, (e j).fst = v)
    (hds : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hes : ∀ j : Fin m, R.rotate (e j.succ) = e j.castSucc)
    (hstop : R.rotate stop = d (Fin.last n))
    (he0 : R.rotate (e 0) = stop) (hd0 : R.rotate (d 0) = e (Fin.last m)) :
    ∀ u, G.Adj v u ↔ u = stop.snd ∨ (∃ i, u = (d i).snd) ∨ (∃ j, u = (e j).snd) := by
  intro u
  constructor
  · intro hu
    let x : G.Dart := ⟨(v,u),hu⟩
    rcases (R.sector_paths_cover v stop hs n m d e hd he hds hes hstop he0 hd0 x).mp rfl with
      hx | ⟨i,hx⟩ | ⟨j,hx⟩
    · exact Or.inl (congrArg (fun z : G.Dart => z.snd) hx)
    · exact Or.inr (Or.inl ⟨i,congrArg (fun z : G.Dart => z.snd) hx⟩)
    · exact Or.inr (Or.inr ⟨j,congrArg (fun z : G.Dart => z.snd) hx⟩)
  · rintro (rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩)
    · exact hs ▸ stop.adj
    · exact hd i ▸ (d i).adj
    · exact he j ▸ (e j).adj

/-- A global neighbor cover becomes an exact cover on each actual split
side. Cross-side candidates can only be the shared chord endpoint. -/
theorem split_side_neighbor_coverage
    (x y : (VertexDeletedGraph (G := G) v).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) v).Preconnected)
    (hz : (R.deleteVertex v).HasGenusZero)
    (hf : (R.deleteVertex v).face.SameCycle x y)
    {I J : Type*} (a : I → {u : V // u ≠ v}) (b : J → {u : V // u ≠ v})
    (t : {u : V // u ≠ v})
    (hcover : ∀ u : {u : V // u ≠ v}, G.Adj v u.val ↔
      u = t ∨ (∃ i, u = a i) ∨ (∃ j, u = b j))
    (ht : t ∈ (R.deleteVertex v).splitSide x y hxy x)
    (ha : ∀ i, a i ∈ (R.deleteVertex v).splitSide x y hxy y)
    (hb : ∀ j, b j ∈ (R.deleteVertex v).splitSide x y hxy x)
    (hw : ∃ j, x.fst = b j) :
    (∀ u ∈ (R.deleteVertex v).splitSide x y hxy x,
      G.Adj v u.val ↔ u = t ∨ ∃ j, u = b j) ∧
    (∀ u ∈ (R.deleteVertex v).splitSide x y hxy y,
      G.Adj v u.val ↔ u = x.fst ∨ ∃ i, u = a i) := by
  have hinter := (R.deleteVertex v).split_sides_inter x y hxy hne hc hz hf
  have hwadj : G.Adj v x.fst.val := by
    obtain ⟨j,hj⟩ := hw
    exact (hcover x.fst).mpr (Or.inr (Or.inr ⟨j,hj⟩))
  constructor
  · intro u hu
    constructor
    · intro hn
      rcases (hcover u).mp hn with h | ⟨i,h⟩ | h
      · exact Or.inl h
      · have he : u = x.fst := (hinter u).mp ⟨hu,h ▸ ha i⟩
        obtain ⟨j,hj⟩ := hw
        exact Or.inr ⟨j,he.trans hj⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact (hcover u).mpr (Or.inl h)
      · exact (hcover u).mpr (Or.inr (Or.inr h))
  · intro u hu
    constructor
    · intro hn
      rcases (hcover u).mp hn with h | h | ⟨j,h⟩
      · exact Or.inl ((hinter u).mp ⟨h ▸ ht,hu⟩)
      · exact Or.inr h
      · exact Or.inl ((hinter u).mp ⟨h ▸ hb j,hu⟩)
    · rintro (rfl | ⟨i,rfl⟩)
      · exact hwadj
      · exact (hcover (a i)).mpr (Or.inr (Or.inl ⟨i,rfl⟩))

end JSP512Probe.RotationSystem
