import Probe.RotationIso

namespace JSP512Probe
variable {V : Type*} (G : SimpleGraph V)

/-- Add a fresh isolated vertex `none`, retaining the old graph on `some`. -/
def withIsolate : SimpleGraph (Option V) where
  Adj x y := match x,y with | some u,some v => G.Adj u v | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

namespace RotationSystem
open CycleSurgery

/-- The fresh isolate contributes no dart. -/
noncomputable def isolateDarts : G.Dart ≃ (withIsolate G).Dart := by
  let f : G.Dart → (withIsolate G).Dart := fun d => ⟨(some d.fst,some d.snd),d.adj⟩
  apply Equiv.ofBijective f
  constructor
  · intro d e h
    have hf := Option.some.inj (congrArg (fun d : (withIsolate G).Dart => d.fst) h)
    have ht := Option.some.inj (congrArg (fun d : (withIsolate G).Dart => d.snd) h)
    exact SimpleGraph.Dart.ext _ _ (Prod.ext hf ht)
  · rintro ⟨⟨x,y⟩,h⟩
    cases x with
    | none => exact False.elim h
    | some x =>
      cases y with
      | none => exact False.elim h
      | some y => exact ⟨⟨(x,y),h⟩,rfl⟩

theorem isolateDarts_reverse (d : G.Dart) : isolateDarts G d.symm = (isolateDarts G d).symm := rfl

theorem withIsolate_none_support : none ∉ (withIsolate G).support := by
  rintro ⟨x,hx⟩
  cases x <;> exact hx

theorem withIsolate_reachable (u v : V) :
    (withIsolate G).Reachable (some u) (some v) ↔ G.Reachable u v := by
  let inc : G →g withIsolate G := ⟨some,fun h => h⟩
  let proj : withIsolate G →g G := ⟨fun x => x.getD u,by
    intro x y h
    cases x <;> cases y <;> first | exact False.elim h | exact h⟩
  exact ⟨fun h => h.map proj,fun h => h.map inc⟩

theorem withIsolate_none_reachable (x : Option V) :
    (withIsolate G).Reachable none x ↔ x = none := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h _ => exact False.elim h
  · rintro rfl
    exact SimpleGraph.Reachable.rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (R : RotationSystem G)

/-- Conjugate the original rotation to the enlarged carrier with an isolated center. -/
noncomputable def addIsolate : RotationSystem (withIsolate G) := by
  let E := isolateDarts G
  let σ : Equiv.Perm (withIsolate G).Dart := (E.symm.trans R.rotate).trans E
  have step : ∀ d, σ (E d) = E (R.rotate d) := by
    intro d
    change E (R.rotate (E.symm (E d))) = E (R.rotate d)
    rw [E.symm_apply_apply]
  refine ⟨σ,?_,?_⟩
  · intro x
    obtain ⟨d,rfl⟩ := E.surjective x
    rw [step]
    exact congrArg some (R.source d)
  · intro x y h
    obtain ⟨d,rfl⟩ := E.surjective x
    obtain ⟨e,rfl⟩ := E.surjective y
    apply (transport_cycles E.symm R.rotate (E d) (E e)).mpr
    simp only [Equiv.symm_apply_apply]
    exact R.local_cycle d e (Option.some.inj h)

omit [DecidableEq V] in
theorem addIsolate_face (d : G.Dart) :
    (R.addIsolate).face (isolateDarts G d) = isolateDarts G (R.face d) := by
  change isolateDarts G (R.rotate ((isolateDarts G).symm (isolateDarts G d).symm)) = _
  rw [← isolateDarts_reverse,Equiv.symm_apply_apply]
  rfl

omit [DecidableEq V] in
theorem addIsolate_faceCount : (R.addIsolate).faceCount = R.faceCount := by
  classical
  let E : R.FaceOrbit ≃ (R.addIsolate).FaceOrbit := Quotient.congr (isolateDarts G)
    (fun d e => (sameCycle_embedding R.face (R.addIsolate).face (isolateDarts G)
      (isolateDarts G).injective (fun d => (addIsolate_face G R d).symm) d e).symm)
  exact (Nat.card_congr E).symm

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem withIsolate_component_count :
    Nat.card (withIsolate G).ConnectedComponent = Nat.card G.ConnectedComponent + 1 := by
  classical
  exact quotient_card_remove_class G.reachableSetoid (withIsolate G).reachableSetoid none some
    (fun x y => withIsolate_reachable G x y) (by
      intro y
      change (∃ x, some x = y) ↔ ¬(withIsolate G).Reachable none y
      rw [withIsolate_none_reachable]
      cases y <;> simp)

omit [DecidableEq V] in
/-- Adding an isolated vertex leaves the exact Euler defect unchanged. -/
theorem addIsolate_eulerDefect : (R.addIsolate).eulerDefect = R.eulerDefect := by
  classical
  have hc := withIsolate_component_count G
  have hd := Fintype.card_congr (isolateDarts G)
  rw [SimpleGraph.dart_card_eq_twice_card_edges,SimpleGraph.dart_card_eq_twice_card_edges] at hd
  have he : Nat.card (withIsolate G).edgeSet = Nat.card G.edgeSet := by
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hd
    omega
  let S : G.support ≃ (withIsolate G).support := {
    toFun := fun x => ⟨some x.val,by
      obtain ⟨w,hw⟩ := G.mem_support.mp x.property
      exact (withIsolate G).mem_support.mpr ⟨some w,hw⟩⟩
    invFun := fun x => by
      obtain ⟨x,hx⟩ := x
      cases x with
      | none => exact False.elim (withIsolate_none_support G hx)
      | some u =>
        refine ⟨u,?_⟩
        obtain ⟨w,hw⟩ := (withIsolate G).mem_support.mp hx
        cases w with
        | none => exact False.elim hw
        | some w => exact G.mem_support.mpr ⟨w,hw⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨x,hx⟩
      cases x with
      | none => exact False.elim (withIsolate_none_support G hx)
      | some u => rfl }
  have hs := Nat.card_congr S
  simp only [eulerDefect,supportSize,addIsolate_faceCount G R,hc,he,← hs,Fintype.card_option]
  omega

omit [DecidableEq V] in
theorem addIsolate_genusZero (hz : R.HasGenusZero) : (R.addIsolate).HasGenusZero :=
  (addIsolate_eulerDefect G R).trans hz
end RotationSystem
end JSP512Probe
