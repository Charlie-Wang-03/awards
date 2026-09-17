import Probe.IsolateExtension
import Probe.PendantFaceSteps
import Probe.RestoreSeparator

namespace JSP512Probe.RotationSystem
variable {V : Type*} (G : SimpleGraph V)

/-- The first fan edge joins the new center to the chosen old boundary vertex. -/
def fanStartGraph (a : G.Dart) : SimpleGraph (Option V) :=
  EdgeInsertion.addedGraph (withIsolate G) (some a.fst) none (Option.some_ne_none _)

theorem fanStartGraph_center_adj (a : G.Dart) (u : V) :
    (fanStartGraph G a).Adj none (some u) ↔ u = a.fst := by
  change (False ∨ (none = some a.fst ∧ some u = none) ∨ (none = none ∧ some u = some a.fst)) ↔ _
  simp

/-- The first attachment gives a connected graph whenever the old side was connected. -/
theorem fanStartGraph_connected (a : G.Dart) (hc : G.Connected) : (fanStartGraph G a).Connected := by
  let H := fanStartGraph G a
  let inc : G →g H := ⟨some,fun h => Or.inl h⟩
  have reach : ∀ x : Option V, H.Reachable x (some a.fst) := by
    intro x
    cases x with
    | none => exact (show H.Adj none (some a.fst) from (fanStartGraph_center_adj G a a.fst).mpr rfl).reachable
    | some u => exact (hc.preconnected u a.fst).map inc
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (R : RotationSystem G)

/-- Actual rotation after creating the new center and attaching its first edge. -/
noncomputable def startFan (a : G.Dart) : RotationSystem (fanStartGraph G a) := by
  classical
  exact EdgeInsertion.addPendant (withIsolate G) (R.addIsolate) (isolateDarts G a) none
    (withIsolate_none_support G)

theorem startFan_genusZero (a : G.Dart) (hz : R.HasGenusZero) : (startFan G R a).HasGenusZero := by
  classical
  exact EdgeInsertion.pendant_genusZero (withIsolate G) (R.addIsolate) (isolateDarts G a) none
    (withIsolate_none_support G) (addIsolate_genusZero G R hz)

end JSP512Probe.RotationSystem

namespace JSP512Probe.RotationSystem
variable {V : Type*} (v : V) (A : Set {u : V | u ≠ v})

/-- The temporary optional carrier is exactly the desired restored side carrier. -/
noncomputable def restoredVertexEquiv : Option A ≃ restoreSide v A := by
  classical
  let f : Option A → restoreSide v A := fun x => match x with
    | none => ⟨v,Or.inl rfl⟩
    | some u => ⟨u.val.val,Or.inr ⟨u.val,u.property,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hh := congrArg Subtype.val h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact False.elim (y.val.property hh.symm)
    | some x =>
      cases y with
      | none => exact False.elim (x.val.property hh)
      | some y => exact congrArg some (Subtype.ext (Subtype.ext hh))
  · rintro ⟨u,hu⟩
    rcases hu with rfl | ⟨w,hw,rfl⟩
    · exact ⟨none,rfl⟩
    · exact ⟨some ⟨w,hw⟩,rfl⟩
end JSP512Probe.RotationSystem
