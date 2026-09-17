import Probe.DeletionConnectivity

namespace JSP512Probe.RotationSystem
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (d : G.Dart)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem source_survives_iff : d.fst ∈ (DeletedGraph d).support ↔ R.rotate d ≠ d := by
  constructor
  · intro h hf
    obtain ⟨w, hw⟩ := (DeletedGraph d).mem_support.mp h
    let e : G.Dart := ⟨(d.fst,w), (SimpleGraph.deleteEdges_adj.mp hw).1⟩
    have he : e = d := (R.rotate_fixed_iff_unique d).mp hf e rfl
    have hn := (SimpleGraph.deleteEdges_adj.mp hw).2
    change ¬e.edge = d.edge at hn
    exact hn (congrArg SimpleGraph.Dart.edge he)
  · intro h
    apply (DeletedGraph d).mem_support.mpr
    refine ⟨(R.rotate d).snd, ?_⟩
    apply SimpleGraph.deleteEdges_adj.mpr
    have hs := R.source d
    have ha := (R.rotate d).adj
    rw [hs] at ha
    refine ⟨ha, ?_⟩
    have hn : (R.rotate d).edge ≠ d.edge := by
      change ¬(R.rotate d).edge = d.edge
      rw [SimpleGraph.dart_edge_eq_iff (R.rotate d) d]
      apply not_or.mpr
      refine ⟨h, ?_⟩
      intro he
      have hx := congrArg (fun x : G.Dart => x.fst) he
      rw [R.source] at hx
      exact d.fst_ne_snd hx
    change ¬s(d.fst, (R.rotate d).snd) = d.edge
    simpa only [SimpleGraph.Dart.edge, hs] using hn

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem target_survives_iff : d.snd ∈ (DeletedGraph d).support ↔ R.rotate d.symm ≠ d.symm := by
  have h := R.source_survives_iff d.symm
  change d.snd ∈ (DeletedGraph d.symm).support ↔ R.rotate d.symm ≠ d.symm at h
  simpa only [DeletedGraph, SimpleGraph.Dart.edge_symm] using h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Only the endpoints of the deleted edge can become isolated. -/
theorem other_survives_iff (v : V) (hs : v ≠ d.fst) (ht : v ≠ d.snd) :
    v ∈ (DeletedGraph d).support ↔ v ∈ G.support := by
  constructor
  · rintro h
    obtain ⟨w, hw⟩ := (DeletedGraph d).mem_support.mp h
    exact G.mem_support.mpr ⟨w, (SimpleGraph.deleteEdges_adj.mp hw).1⟩
  · intro h
    obtain ⟨w, hw⟩ := G.mem_support.mp h
    apply (DeletedGraph d).mem_support.mpr
    refine ⟨w, SimpleGraph.deleteEdges_adj.mpr ⟨hw, ?_⟩⟩
    let e : G.Dart := ⟨(v,w),hw⟩
    change ¬e.edge = d.edge
    rw [SimpleGraph.dart_edge_eq_iff e d]
    rintro (he | he)
    · exact hs (congrArg (fun x : G.Dart => x.fst) he)
    · exact ht (congrArg (fun x : G.Dart => x.fst) he)

/-- Number of nonisolated vertices, with integer values for Euler arithmetic. -/
noncomputable def supportSize : ℤ := Nat.card G.support

theorem supportSize_delete :
    supportSize (G := DeletedGraph d) + (if R.rotate d = d then 1 else 0) +
      (if R.rotate d.symm = d.symm then 1 else 0) = supportSize (G := G) := by
  classical
  have hp : ∀ v : V,
      (if v ∈ (DeletedGraph d).support then (1 : ℤ) else 0) +
      (if v = d.fst ∧ R.rotate d = d then 1 else 0) +
      (if v = d.snd ∧ R.rotate d.symm = d.symm then 1 else 0) =
      (if v ∈ G.support then 1 else 0) := by
    intro v
    by_cases hs : v = d.fst
    · subst v
      simp only [R.source_survives_iff d]
      have hg := d.adj.mem_support_left
      by_cases hr : R.rotate d = d <;> simp [hr, hg, d.fst_ne_snd]
    · by_cases ht : v = d.snd
      · subst v
        simp only [R.target_survives_iff d]
        have hg := d.adj.mem_support_right
        by_cases hr : R.rotate d.symm = d.symm <;> simp [hr, hg, d.snd_ne_fst]
      · simp only [other_survives_iff d v hs ht]
        simp [hs, ht]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => hp v)
  simp only [Finset.sum_add_distrib] at hh
  by_cases hs : R.rotate d = d <;> by_cases ht : R.rotate d.symm = d.symm <;>
    simpa [supportSize, Nat.card_eq_fintype_card, Fintype.card_subtype, hs, ht] using hh

end JSP512Probe.RotationSystem
