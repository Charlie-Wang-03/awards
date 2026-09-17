import Probe.RestoredFanIso
import Probe.DiskIso
import Mathlib.Data.List.OfFn

namespace JSP512Probe.RotationSystem
variable {V : Type*} (G : SimpleGraph V) (v : V) (A : Set {u : V // u ≠ v})
  (T : RotationSystem ((VertexDeletedGraph (G := G) v).induce A))
  (r : ((VertexDeletedGraph (G := G) v).induce A).Dart)
  (n : ℕ) (p : Fin n → ((VertexDeletedGraph (G := G) v).induce A).Dart)
  (K : SimpleGraph (Option A))

/-- Convert the exact fan-route adjacency formula into the original graph's
center adjacency using the proved side-neighbor characterization. -/
theorem restored_route_center
    (hK : ∀ u, K.Adj none (some u) ↔
      u = (T.face.symm r).symm.fst ∨ ∃ d ∈ List.ofFn p, d.snd = u)
    (hcover : ∀ u : A, G.Adj v u.val.val ↔
      u.val = r.fst.val ∨ ∃ i, u.val = (p i).snd.val) :
    ∀ u : A, K.Adj none (some u) ↔ G.Adj v u.val.val := by
  intro u
  have ha : (T.face.symm r).symm.fst = r.fst := T.face_inverse_target r
  rw [hK,ha]
  constructor
  · rintro (rfl | ⟨d,hd,he⟩)
    · exact (hcover _).mpr (Or.inl rfl)
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
      exact (hcover u).mpr (Or.inr ⟨i,congrArg Subtype.val he.symm⟩)
  · intro hu
    rcases (hcover u).mp hu with he | ⟨i,he⟩
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr ⟨p i,List.mem_ofFn.mpr ⟨i,rfl⟩,Subtype.ext he.symm⟩

/-- The graph produced by route restoration is the restored original induced
side, using its exact old-edge and route-center formulas. -/
noncomputable def restoredRouteIso
    (hold : ∀ u w : A, K.Adj (some u) (some w) ↔ G.Adj u.val.val w.val.val)
    (hK : ∀ u, K.Adj none (some u) ↔
      u = (T.face.symm r).symm.fst ∨ ∃ d ∈ List.ofFn p, d.snd = u)
    (hcover : ∀ u : A, G.Adj v u.val.val ↔
      u.val = r.fst.val ∨ ∃ i, u.val = (p i).snd.val) :
    K ≃g G.induce (restoreSide v A) :=
  restoredFanIso G v A K hold (restored_route_center G v A T r n p K hK hcover)

end JSP512Probe.RotationSystem
