import Probe.OuterFaceRegion

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- All nonexceptional sectors lie on the face of the last sector of the fan. -/
theorem outer_fan_single_orbit (outer : G.Dart)
    (hfan : ∀ d : G.Dart, d.fst = outer.snd → d ≠ outer.symm →
      R.face (R.face (R.face d.symm)) = d.symm)
    (p : G.Dart) (hp : p.fst = outer.snd) (hpn : p ≠ outer.symm)
    (hpred : R.rotate p = outer.symm) :
    ∀ (d : G.Dart) (hd : d.fst = outer.snd) (hn : d ≠ outer.symm),
      (R.deleteVertex outer.snd).face.SameCycle
        (R.sectorDeletedDart outer.snd d hd (hfan d hd hn))
        (R.sectorDeletedDart outer.snd p hp (hfan p hp hpn)) := by
  have reach : ∀ n : ℕ, ∀ (d : G.Dart) (hd : d.fst = outer.snd)
      (hn : d ≠ outer.symm), (R.rotate ^ n) d = outer.symm →
      (R.deleteVertex outer.snd).face.SameCycle
        (R.sectorDeletedDart outer.snd d hd (hfan d hd hn))
        (R.sectorDeletedDart outer.snd p hp (hfan p hp hpn)) := by
    intro n
    induction n with
    | zero =>
      intro d hd hn he
      exact False.elim (hn he)
    | succ n ih =>
      intro d hd hn he
      by_cases hr : R.rotate d = outer.symm
      · have heq : d = p := R.rotate.injective (hr.trans hpred.symm)
        subst d
        exact Equiv.Perm.SameCycle.rfl
      · have hs : (R.rotate d).fst = outer.snd := (R.source d).trans hd
        have hi := ih (R.rotate d) hs hr (by
          simpa only [pow_succ, Equiv.Perm.mul_apply] using he)
        have hstep := R.sector_predecessor_step outer.snd (R.rotate d) d hs hd rfl
          (hfan _ hs hr) (hfan _ hd hn)
        rw [← hstep]
        exact hi.apply_left
  intro d hd hn
  obtain ⟨n,he⟩ := (R.local_cycle d outer.symm hd).exists_nat_pow_eq
  exact reach n d hd hn he

/-- Every surviving old outer dart reaches the fan through the incoming junction. -/
theorem old_outer_reaches_fan (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (p : G.Dart) (hp : p.fst = outer.snd)
    (hpred : R.rotate p = outer.symm)
    (ht : R.face (R.face (R.face p.symm)) = p.symm)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val) :
    (R.deleteVertex outer.snd).face.SameCycle x
      (R.sectorDeletedDart outer.snd p hp ht) := by
  have reach : ∀ n : ℕ, ∀ x : (VertexDeletedGraph (G := G) outer.snd).Dart,
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val →
      (R.face ^ n) ((vertexDeletedDartEquiv outer.snd) x).val = outer →
      (R.deleteVertex outer.snd).face.SameCycle x
        (R.sectorDeletedDart outer.snd p hp ht) := by
    intro n
    induction n with
    | zero =>
      intro x hx he
      exact False.elim (((vertexDeletedDartEquiv outer.snd) x).property.2
        (congrArg (fun a : G.Dart => a.snd) he))
    | succ n ih =>
      intro x hx he
      let a := ((vertexDeletedDartEquiv outer.snd) x).val
      by_cases ha : R.face a = outer
      · have hs := R.outer_splice_entry outer p hp hpred ht x ha
        rw [← hs]
        exact Equiv.Perm.SameCycle.rfl.apply_right
      · have hn : (R.face a).snd ≠ outer.snd := by
          intro hv
          have hh := hsimple (R.face (R.face a)) (R.face outer)
            hx.apply_right.apply_right Equiv.Perm.SameCycle.rfl.apply_right
            (by rw [R.face_source, R.face_source, hv])
          exact ha (R.face.injective hh)
        have hstep := R.vertex_deleted_face_formula outer.snd x
        rw [ite_eq_right hn] at hstep
        have hi := ih ((R.deleteVertex outer.snd).face x)
          (by rw [hstep]; exact hx.apply_right)
          (by rw [hstep]; simpa only [pow_succ, Equiv.Perm.mul_apply] using he)
        exact hi.of_apply_left
  obtain ⟨n,hn⟩ := hx.symm.exists_nat_pow_eq
  exact reach n x hx hn
/-- The entire candidate outer region is exactly one nonempty facial orbit. -/
theorem outer_region_single_orbit (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm) :
    ∃ root : (VertexDeletedGraph (G := G) outer.snd).Dart, ∀ x,
      (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x := by
  let p := R.rotate.symm outer.symm
  have hpred : R.rotate p = outer.symm := R.rotate.apply_symm_apply _
  have hp : p.fst = outer.snd := by
    have hh := R.source p
    rw [hpred] at hh
    exact hh.symm
  have hpn : p ≠ outer.symm := by
    intro he
    have hh : R.rotate outer.symm = outer.symm := by rwa [he] at hpred
    exact hcorner hh
  have fan := R.outer_face_fan outer hsimple hinner
  let root := R.sectorDeletedDart outer.snd p hp (fan p hp hpn)
  have hr : R.outerDeletionRegion outer root := by
    right
    change (R.face (R.face (R.rotate p))).snd = outer.snd
    have ht := fan p hp hpn
    have he : R.face p.symm = R.rotate p := by
      change R.rotate p.symm.symm = R.rotate p
      rw [SimpleGraph.Dart.symm_symm]
    rw [he] at ht
    rw [ht]
    exact hp
  refine ⟨root,fun x => ⟨fun hx => R.outer_region_sameCycle outer hinner root x hx hr,?_⟩⟩
  intro hx
  by_cases ho : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val
  · exact (R.old_outer_reaches_fan outer hsimple p hp hpred (fan p hp hpn) x ho).symm
  · obtain ⟨d,hd,ht,hn,he⟩ := R.outer_region_sector outer hinner x ho (hx.resolve_left ho)
    have hne : d ≠ outer.symm := by
      intro heq
      apply hn
      rw [heq, SimpleGraph.Dart.symm_symm]
    subst x
    exact (R.outer_fan_single_orbit outer fan p hp hpn hpred d hd hne).symm

/-- Actual disk-boundary deletion: one simple enlarged outer face and
triangular remaining faces, under the explicit no-chord condition. -/
theorem outer_deleted_boundary (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm)
    (hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd) :
    ∃ root : (VertexDeletedGraph (G := G) outer.snd).Dart,
      (∀ x y, (R.deleteVertex outer.snd).face.SameCycle root x →
        (R.deleteVertex outer.snd).face.SameCycle root y → x.fst = y.fst → x = y) ∧
      (∀ x, ¬(R.deleteVertex outer.snd).face.SameCycle root x →
        (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
          ((R.deleteVertex outer.snd).face x)) = x) ∧
      (∀ u, (∃ x, (R.deleteVertex outer.snd).face.SameCycle root x ∧ x.fst.val = u) ↔
        u ≠ outer.snd ∧ ((∃ a, R.face.SameCycle outer a ∧ a.fst = u) ∨ G.Adj outer.snd u)) := by
  obtain ⟨root,hr⟩ := R.outer_region_single_orbit outer hsimple hinner hcorner
  refine ⟨root,?_,?_,?_⟩
  · intro x y hx hy he
    exact R.outer_region_source_injective outer hsimple hinner hchord x y
      ((hr x).mp hx) ((hr y).mp hy) he
  · intro x hx
    exact R.outside_outer_region_triangular outer hinner x (fun h => hx ((hr x).mpr h))
  · intro u
    simp only [hr]
    exact R.outer_region_vertices outer hsimple hinner hcorner u

end JSP512Probe.RotationSystem
