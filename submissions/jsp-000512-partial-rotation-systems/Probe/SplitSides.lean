import Probe.SplitSeparation

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- Projection to old vertices of a specified component of the split graph. -/
def splitSide (mark : G.Dart) : Set V := {u | ∃ d : G.Dart, d.fst = u ∧
  (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
    (RefinedRotation.vertex G (R.splitRotation a b) d)
    (RefinedRotation.vertex G (R.splitRotation a b) mark)}

/-- The two projected components cover all old vertices. -/
theorem split_sides_cover (hne : a ≠ b) (hc : G.Preconnected) (u : V) :
    u ∈ R.splitSide a b hab a ∨ u ∈ R.splitSide a b hab b := by
  have : Nontrivial V := ⟨⟨a.fst,a.snd,a.adj.ne⟩⟩
  have hu : u ∈ G.support := by rw [hc.support_eq_univ]; trivial
  obtain ⟨w,hw⟩ := G.mem_support.mp hu
  let d : G.Dart := ⟨(u,w),hw⟩
  exact (R.split_reaches_copies a b hab hne hc d).elim
    (fun h => Or.inl ⟨d,rfl,h⟩) (fun h => Or.inr ⟨d,rfl,h⟩)

/-- Every old edge lies entirely in at least one projected component. -/
theorem split_sides_edges (hne : a ≠ b) (hc : G.Preconnected)
    (u v : V) (huv : G.Adj u v) :
    (u ∈ R.splitSide a b hab a ∧ v ∈ R.splitSide a b hab a) ∨
    (u ∈ R.splitSide a b hab b ∧ v ∈ R.splitSide a b hab b) := by
  let d : G.Dart := ⟨(u,v),huv⟩
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  have he : H.Reachable (q d.symm) (q d) :=
    (show H.Adj (q d) (q d.symm) from ⟨d,rfl,rfl⟩).reachable.symm
  exact (R.split_reaches_copies a b hab hne hc d).elim
    (fun h => Or.inl ⟨⟨d,rfl,h⟩,⟨d.symm,rfl,he.trans h⟩⟩)
    (fun h => Or.inr ⟨⟨d,rfl,h⟩,⟨d.symm,rfl,he.trans h⟩⟩)

/-- The projected sides meet precisely at the split vertex. -/
theorem split_sides_inter (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (u : V) :
    (u ∈ R.splitSide a b hab a ∧ u ∈ R.splitSide a b hab b) ↔ u = a.fst := by
  constructor
  · rintro ⟨⟨d,hd,hda⟩,⟨e,he,heb⟩⟩
    by_contra hn
    have hde := R.split_cycles_away a b hab hne d e (hd ▸ hn) (hd.trans he.symm)
    have hq : RefinedRotation.vertex G (R.splitRotation a b) d =
        RefinedRotation.vertex G (R.splitRotation a b) e := Quotient.sound hde
    have hab' := hda.symm.trans (hq.symm ▸ heb)
    exact R.split_copies_not_reachable a b hab hne hc hz hf hab'
  · rintro rfl
    exact ⟨⟨a,rfl,SimpleGraph.Reachable.rfl⟩,⟨b,hab.symm,SimpleGraph.Reachable.rfl⟩⟩

/-- Both sides have an explicit vertex outside the other side. -/
theorem split_sides_proper (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) :
    (a.snd ∈ R.splitSide a b hab a ∧ a.snd ∉ R.splitSide a b hab b) ∧
    (b.snd ∈ R.splitSide a b hab b ∧ b.snd ∉ R.splitSide a b hab a) := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  have ha : a.snd ∈ R.splitSide a b hab a := ⟨a.symm,rfl,
    (show H.Adj (q a) (q a.symm) from ⟨a,rfl,rfl⟩).reachable.symm⟩
  have hb : b.snd ∈ R.splitSide a b hab b := ⟨b.symm,rfl,
    (show H.Adj (q b) (q b.symm) from ⟨b,rfl,rfl⟩).reachable.symm⟩
  refine ⟨⟨ha,fun h => a.snd_ne_fst ((R.split_sides_inter a b hab hne hc hz hf _).mp ⟨ha,h⟩)⟩,
    ⟨hb,?_⟩⟩
  intro h
  exact b.snd_ne_fst (((R.split_sides_inter a b hab hne hc hz hf _).mp ⟨h,hb⟩).trans hab)

/-- Each projected side is strictly smaller than the old vertex carrier. -/
theorem split_sides_card_lt (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) :
    Nat.card (R.splitSide a b hab a) < Fintype.card V ∧
    Nat.card (R.splitSide a b hab b) < Fintype.card V := by
  classical
  have hp := R.split_sides_proper a b hab hne hc hz hf
  constructor
  · simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hp.2.2
  · simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hp.1.2
end JSP512Probe.RotationSystem
