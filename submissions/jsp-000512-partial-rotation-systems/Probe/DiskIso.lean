import Probe.RotationIso
import Probe.DiskInstance

namespace JSP512Probe.RotationSystem
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
  (R : RotationSystem G) (e : G ≃g H)

omit [DecidableEq V] [DecidableEq W] in
/-- Graph isomorphism transports all four triangulated-disk conditions. -/
theorem mapIso_disk (root : G.Dart) (hD : R.IsTriangulatedDisk root) :
    (R.mapIso e).IsTriangulatedDisk (isoDarts e root) := by
  refine ⟨R.mapIso_genusZero e hD.zero,?_,?_,?_⟩
  · exact hD.connected.map e.toHom e.surjective
  · intro x y hx hy hxy
    obtain ⟨d,rfl⟩ := (isoDarts e).surjective x
    obtain ⟨f,rfl⟩ := (isoDarts e).surjective y
    apply congrArg (isoDarts e)
    exact hD.simple d f ((R.mapIso_face_cycles e root d).mp hx)
      ((R.mapIso_face_cycles e root f).mp hy) (e.injective hxy)
  · intro x hx
    obtain ⟨d,rfl⟩ := (isoDarts e).surjective x
    exact R.mapIso_triangle e d (hD.inner d (fun h => hx ((R.mapIso_face_cycles e root d).mpr h)))

omit [DecidableEq V] [DecidableEq W] in
/-- Boundary vertices are carried exactly by the vertex isomorphism. -/
theorem mapIso_facialVertices (root : G.Dart) (v : V) :
    e v ∈ (R.mapIso e).facialVertices (isoDarts e root) ↔ v ∈ R.facialVertices root := by
  constructor
  · rintro ⟨x,hx,hv⟩
    obtain ⟨d,rfl⟩ := (isoDarts e).surjective x
    exact ⟨d,(R.mapIso_face_cycles e root d).mp hx,e.injective hv⟩
  · rintro ⟨d,hd,rfl⟩
    exact ⟨isoDarts e d,(R.mapIso_face_cycles e root d).mpr hd,rfl⟩

end JSP512Probe.RotationSystem
