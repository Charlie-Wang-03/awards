import Probe.SplitSideDartTransport
import Probe.ResidualFanBoundary

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)
  (hne : a ≠ b) (hc : G.Preconnected) (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
  (mark root : G.Dart) (hr)
  (hroot : R.face.SameCycle a root)
  (n : ℕ) (p : Fin n → G.Dart)
  (hp : ∀ i, (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
    (RefinedRotation.vertex G (R.splitRotation a b) (p i))
    (RefinedRotation.vertex G (R.splitRotation a b) mark))

include hroot in
/-- Lift an arbitrary retained side-boundary dart, retaining its component,
old outer-orbit membership, and exclusion from the original sector path. -/
theorem splitSideDart_residual_lift :
    let T := R.splitSideRotation a b hab hne hc hz hf mark
    let r := R.splitSideDart a b hab mark root hr
    let anchor := (T.face.symm r).symm
    let ds := List.ofFn (fun i => R.splitSideDart a b hab mark (p i) (hp i))
    ∀ z, T.face.SameCycle anchor.symm z → z ∉ ds →
      ∃ (d : G.Dart) (hd :
        (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
          (RefinedRotation.vertex G (R.splitRotation a b) d)
          (RefinedRotation.vertex G (R.splitRotation a b) mark)),
        R.splitSideDart a b hab mark d hd = z ∧ R.face.SameCycle a d ∧ ∀ i, d ≠ p i := by
  dsimp only
  intro z hzface hn
  have hzroot : (R.splitSideRotation a b hab hne hc hz hf mark).face.SameCycle
      (R.splitSideDart a b hab mark root hr) z := by
    simpa only [SimpleGraph.Dart.symm_symm, Equiv.apply_symm_apply] using hzface.apply_left
  obtain ⟨d,hd,rfl,ho⟩ := R.splitSideDart_outer_lift a b hab hne hc hz hf mark root hr hroot z hzroot
  refine ⟨d,hd,rfl,ho,?_⟩
  intro i he
  apply hn
  apply List.mem_ofFn.mpr
  refine ⟨i,?_⟩
  subst d
  rfl

include hroot in
/-- Source simplicity and attachment exclusion established on retained old
darts imply exactly the two boundary premises of actual side fan restoration. -/
theorem splitSideDart_residual_conditions
    (P : G.Dart → Prop)
    (hretain : ∀ d,
      (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
        (RefinedRotation.vertex G (R.splitRotation a b) d)
        (RefinedRotation.vertex G (R.splitRotation a b) mark) →
      R.face.SameCycle a d → (∀ i, d ≠ p i) → P d)
    (hsimple : ∀ d e, P d → P e → d.fst = e.fst → d = e)
    (hattach : ∀ d, P d → d.fst ≠ root.fst) :
    let T := R.splitSideRotation a b hab hne hc hz hf mark
    let r := R.splitSideDart a b hab mark root hr
    let anchor := (T.face.symm r).symm
    let ds := List.ofFn (fun i => R.splitSideDart a b hab mark (p i) (hp i))
    ResidualBoundarySimple (G.induce (R.splitSide a b hab mark)) T anchor ds ∧
      ∀ z, T.face.SameCycle anchor.symm z → z ∉ ds → z.fst ≠ anchor.fst := by
  dsimp only
  have lift := R.splitSideDart_residual_lift a b hab hne hc hz hf mark root hr hroot n p hp
  dsimp only at lift
  constructor
  · intro x y hx hy hnx hny hxy
    obtain ⟨d,hd,rfl,ho,hn⟩ := lift x hx hnx
    obtain ⟨e,he,rfl,heo,hen⟩ := lift y hy hny
    have hde := hsimple d e (hretain d hd ho hn) (hretain e he heo hen)
      (congrArg Subtype.val hxy)
    subst e
    rfl
  · intro z hzface hn heq
    obtain ⟨d,hd,rfl,ho,hnot⟩ := lift z hzface hn
    apply hattach d (hretain d hd ho hnot)
    have hv := congrArg Subtype.val heq
    change d.fst = ((R.splitSideRotation a b hab hne hc hz hf mark).face.symm
      (R.splitSideDart a b hab mark root hr)).snd.val at hv
    rw [face_inverse_target] at hv
    exact hv

end JSP512Probe.RotationSystem
