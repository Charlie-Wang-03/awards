import Probe.OuterFaceOrbit
import Probe.DeletionFaceCounting

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Exact facial count with one arbitrary outer face and triangular inner faces. -/
theorem disk_face_count (outer : G.Dart)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a) :
    3 * R.faceCount + R.faceLength outer = 2 * Nat.card G.edgeSet + 3 := by
  classical
  have hq : ∀ q : Orbit R.face, q ≠ Quotient.mk _ outer → orbitSize R.face q = 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      apply orbitSize_eq_three R.face x (R.face_ne_self x)
      exact hinner x (fun hc => hx (Quotient.sound hc.symm))
  have hh := orbit_size_exact R.face (Quotient.mk _ outer) hq
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hh
  simpa only [faceCount, FaceOrbit, faceLength, Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card] using hh
end JSP512Probe.RotationSystem
