import Probe.OuterBoundaryLength

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Counting darts rather than boundary vertices removes the no-chord
hypothesis from the outer-length change formula. -/
theorem outer_deleted_dart_length (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hr : ∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x) :
    (R.deleteVertex outer.snd).faceLength root + 3 = R.faceLength outer + G.degree outer.snd := by
  classical
  let B : Finset G.Dart := Finset.univ.filter (R.face.SameCycle outer)
  let N : Finset G.Dart := Finset.univ.filter (fun d => d.fst = outer.snd)
  let T := (B.erase outer).erase (R.face outer)
  let D := N.erase outer.symm
  let f := fun d : G.Dart => R.face (R.rotate d)
  let U := T ∪ D.image f
  have hB : ∀ a, a ∈ B ↔ R.face.SameCycle outer a := by simp [B]
  have hN : ∀ a, a ∈ N ↔ a.fst = outer.snd := by simp [N]
  have fan := R.outer_face_fan outer hsimple hinner
  have inner : ∀ d ∈ D, ¬R.face.SameCycle outer d.symm := by
    intro d hd hc
    have hd' := Finset.mem_erase.mp hd
    have he := hsimple (R.face d.symm) (R.face outer) hc.apply_right
      Equiv.Perm.SameCycle.rfl.apply_right (by
        rw [R.face_source,R.face_source]; exact (hN d).mp hd'.2)
    have hh := congrArg SimpleGraph.Dart.symm (R.face.injective he)
    exact hd'.1 (by simpa only [SimpleGraph.Dart.symm_symm] using hh)
  have survives : ∀ a ∈ T, a.fst ≠ outer.snd ∧ a.snd ≠ outer.snd := by
    intro a ha
    obtain ⟨hn,hn',ho⟩ := (by simpa only [T,Finset.mem_erase,hB] using ha :
      a ≠ R.face outer ∧ a ≠ outer ∧ R.face.SameCycle outer a)
    constructor
    · intro h
      exact hn (hsimple a (R.face outer) ho Equiv.Perm.SameCycle.rfl.apply_right
        (h.trans (R.face_source outer).symm))
    · intro h
      exact hn' (R.face.injective (hsimple (R.face a) (R.face outer)
        ho.apply_right Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source,R.face_source,h])))
  have hu : ∀ a, a ∈ U ↔ ∃ x,
      (R.deleteVertex outer.snd).face.SameCycle root x ∧
        ((vertexDeletedDartEquiv outer.snd) x).val = a := by
    intro a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with ht | hd
      · let x := (vertexDeletedDartEquiv outer.snd).symm ⟨a,survives a ht⟩
        have he : ((vertexDeletedDartEquiv outer.snd) x).val = a := by
          change ((vertexDeletedDartEquiv outer.snd) ((vertexDeletedDartEquiv outer.snd).symm _)).val = a
          rw [Equiv.apply_symm_apply]
        refine ⟨x,(hr x).mpr (Or.inl ?_),he⟩
        rw [he]
        exact (hB a).mp (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).2
      · obtain ⟨d,hdmem,rfl⟩ := Finset.mem_image.mp hd
        have hs := (hN d).mp (Finset.mem_erase.mp hdmem).2
        have hn := (Finset.mem_erase.mp hdmem).1
        let x := R.sectorDeletedDart outer.snd d hs (fan d hs hn)
        refine ⟨x,(hr x).mpr (Or.inr ?_),?_⟩
        · change (R.face (R.face (R.rotate d))).snd = outer.snd
          have ht := fan d hs hn
          have he : R.face d.symm = R.rotate d := by
            change R.rotate d.symm.symm = R.rotate d
            rw [SimpleGraph.Dart.symm_symm]
          rw [he] at ht
          rw [ht]
          exact hs
        · change ((vertexDeletedDartEquiv outer.snd)
            ((vertexDeletedDartEquiv outer.snd).symm _)).val = f d
          rw [Equiv.apply_symm_apply]
    · rintro ⟨x,hx,rfl⟩
      have hm := (hr x).mp hx
      by_cases ho : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val
      · apply Finset.mem_union_left
        apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_erase.mpr ⟨?_,(hB _).mpr ho⟩⟩
        · intro he
          have hh := congrArg (fun d : G.Dart => d.fst) he
          rw [R.face_source] at hh
          exact ((vertexDeletedDartEquiv outer.snd) x).property.1 hh
        · intro he
          exact ((vertexDeletedDartEquiv outer.snd) x).property.2
            (congrArg (fun d : G.Dart => d.snd) he)
      · obtain ⟨d,hd,ht,hn,he⟩ := R.outer_region_sector outer hinner x ho (hm.resolve_left ho)
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        have hne : d ≠ outer.symm := by
          intro he
          apply hn
          rw [he,SimpleGraph.Dart.symm_symm]
        refine ⟨d,Finset.mem_erase.mpr ⟨hne,(hN d).mpr hd⟩,?_⟩
        rw [← he]
        change f d = ((vertexDeletedDartEquiv outer.snd)
          ((vertexDeletedDartEquiv outer.snd).symm _)).val
        rw [Equiv.apply_symm_apply]
  have hucard := (R.deleteVertex outer.snd).faceLength_eq_label_card root
    (fun x => ((vertexDeletedDartEquiv outer.snd) x).val) U
    (fun x y _ _ he => (vertexDeletedDartEquiv outer.snd).injective (Subtype.ext he)) hu
  have hbcard := R.faceLength_eq_label_card outer id B
    (fun _ _ _ _ he => he) (fun a => by
      rw [hB]; exact ⟨fun h => ⟨a,h,rfl⟩,fun ⟨x,h,he⟩ => he ▸ h⟩)
  have hncard : N.card = G.degree outer.snd := by
    have he : N ≃ {d : G.Dart // d.fst = outer.snd} := Equiv.subtypeEquivRight hN
    have hh := Fintype.card_congr (he.trans (neighborDartEquiv (G := G) outer.snd))
    simpa only [Fintype.card_coe,SimpleGraph.card_neighborSet_eq_degree] using hh
  have hdis : Disjoint T (D.image f) := by
    apply Finset.disjoint_left.mpr
    intro a ha hd
    obtain ⟨d,hdmem,rfl⟩ := Finset.mem_image.mp hd
    exact R.inner_sector_not_outer outer d (inner d hdmem)
      ((hB _).mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2)
  have hi : Function.Injective f := R.face.injective.comp R.rotate.injective
  have hc : U.card = T.card + D.card := by
    rw [Finset.card_union_of_disjoint hdis,Finset.card_image_of_injective _ hi]
  have ht1 := Finset.card_erase_add_one ((hB outer).mpr Equiv.Perm.SameCycle.rfl)
  have ht2 := Finset.card_erase_add_one (Finset.mem_erase.mpr
    ⟨R.face_ne_self outer,(hB _).mpr Equiv.Perm.SameCycle.rfl.apply_right⟩)
  have hd := Finset.card_erase_add_one ((hN outer.symm).mpr rfl)
  change T.card + 1 = (B.erase outer).card at ht2
  change D.card + 1 = N.card at hd
  omega
end JSP512Probe.RotationSystem
