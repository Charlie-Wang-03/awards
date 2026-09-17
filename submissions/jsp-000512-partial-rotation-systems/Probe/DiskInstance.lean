import Probe.DiskDeletionGenus

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Combinatorial disk data for induction. A two-dart outer face is allowed
so that deletion of a triangular disk can reach its base case. -/
structure IsTriangulatedDisk (R : RotationSystem G) (outer : G.Dart) : Prop where
  zero : R.HasGenusZero
  connected : G.Connected
  simple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b
  inner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a

/-- Vertices visited by a specified face. -/
def facialVertices (R : RotationSystem G) (outer : G.Dart) : Set V :=
  {u | ∃ a, R.face.SameCycle outer a ∧ a.fst = u}

variable (R : RotationSystem G)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Choosing another dart on the same outer face preserves all disk data. -/
theorem IsTriangulatedDisk.reroot {outer next : G.Dart}
    (hD : R.IsTriangulatedDisk outer) (hn : R.face.SameCycle outer next) :
    R.IsTriangulatedDisk next := by
  refine ⟨hD.zero,hD.connected,?_,?_⟩
  · intro a b ha hb he
    exact hD.simple a b (hn.trans ha) (hn.trans hb) he
  · intro a ha
    exact hD.inner a (fun h => ha (hn.symm.trans h))

/-- Disk data and the exact new orbit survive a chordless boundary deletion. -/
theorem disk_delete_instance (outer : G.Dart) (hD : R.IsTriangulatedDisk outer)
    (hcorner : R.face outer ≠ outer.symm)
    (hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd) :
    ∃ root : (VertexDeletedGraph (G := G) outer.snd).Dart,
      (R.deleteVertex outer.snd).IsTriangulatedDisk root ∧
      (∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x) ∧
      (∀ u : {u : V | u ≠ outer.snd},
        u ∈ (R.deleteVertex outer.snd).facialVertices root ↔
          u.val ∈ R.facialVertices outer ∨ G.Adj outer.snd u.val) := by
  obtain ⟨root,hr⟩ := R.outer_region_single_orbit outer hD.simple hD.inner hcorner
  refine ⟨root,⟨R.disk_deleteVertex_genusZero outer hD.zero hD.connected.preconnected
      hD.simple hD.inner hcorner hchord,
    R.outer_vertex_deleted_connected outer hD.connected.preconnected hD.simple hD.inner,
    ?_,?_⟩,hr,?_⟩
  · intro x y hx hy he
    exact R.outer_region_source_injective outer hD.simple hD.inner hchord x y
      ((hr x).mp hx) ((hr y).mp hy) he
  · intro x hx
    exact R.outside_outer_region_triangular outer hD.inner x (fun h => hx ((hr x).mpr h))
  · intro u
    have h := R.outer_region_vertices outer hD.simple hD.inner hcorner u.val
    constructor
    · rintro ⟨x,hx,he⟩
      exact ((h.mp ⟨x,(hr x).mp hx,congrArg Subtype.val he⟩).2)
    · intro hu
      obtain ⟨x,hx,he⟩ := h.mpr ⟨u.property,hu⟩
      exact ⟨x,(hr x).mpr hx,Subtype.ext he⟩

/-- A surviving old boundary edge is an actual edge on the new outer face. -/
theorem deleted_outer_edge (outer : G.Dart)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hr : ∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x)
    (pre : G.Dart) (hp : R.face.SameCycle outer pre)
    (hs : pre.fst ≠ outer.snd) (ht : pre.snd ≠ outer.snd) :
    (R.deleteVertex outer.snd).face.SameCycle root
      ((vertexDeletedDartEquiv outer.snd).symm ⟨pre,hs,ht⟩) := by
  apply (hr _).mpr
  left
  rw [Equiv.apply_symm_apply]
  exact hp
end JSP512Probe.RotationSystem
