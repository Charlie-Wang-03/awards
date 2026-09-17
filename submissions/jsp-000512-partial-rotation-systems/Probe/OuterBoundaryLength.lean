import Probe.DiskFaceCounting

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Count a facial orbit through any injective labeling of its darts. -/
theorem faceLength_eq_label_card {A : Type*} [DecidableEq A] (root : G.Dart)
    (f : G.Dart → A) (s : Finset A)
    (hi : ∀ x y, R.face.SameCycle root x → R.face.SameCycle root y → f x = f y → x = y)
    (hs : ∀ a, a ∈ s ↔ ∃ x, R.face.SameCycle root x ∧ f x = a) :
    R.faceLength root = s.card := by
  classical
  let g : {x : G.Dart // R.face.SameCycle root x} → s :=
    fun x => ⟨f x.val,(hs _).mpr ⟨x.val,x.property,rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      exact Subtype.ext (hi x.val y.val x.property y.property (congrArg Subtype.val h))
    · intro a
      obtain ⟨x,hx,he⟩ := (hs a.val).mp a.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  rw [R.faceLength_eq_card, Nat.card_congr (Equiv.ofBijective g hg)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

omit [DecidableRel G.Adj] in
/-- A nonbacktracking corner has three distinct incident vertices. -/
theorem nonbacktracking_corner_card (outer : G.Dart)
    (hcorner : R.face outer ≠ outer.symm) : 3 ≤ Fintype.card V := by
  classical
  have hts : outer.fst ≠ (R.face outer).snd := by
    intro h
    exact hcorner (SimpleGraph.Dart.ext _ _ (Prod.ext (R.face_source outer) h.symm))
  have hvs : outer.snd ≠ (R.face outer).snd := by
    have h := (R.face outer).adj.ne
    rwa [R.face_source] at h
  have hcard : ({outer.fst,outer.snd,(R.face outer).snd} : Finset V).card = 3 := by
    simp [outer.adj.ne, hts, hvs]
  have h := Finset.card_le_univ ({outer.fst,outer.snd,(R.face outer).snd} : Finset V)
  rwa [hcard] at h

/-- Exact length change of the simple outer face under chordless boundary deletion. -/
theorem outer_deleted_length (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm)
    (hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hr : ∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔
      R.outerDeletionRegion outer x) :
    (R.deleteVertex outer.snd).faceLength root + 3 = R.faceLength outer + G.degree outer.snd := by
  classical
  let B : Finset V := Finset.univ.filter (fun u => ∃ a, R.face.SameCycle outer a ∧ a.fst = u)
  let N := G.neighborFinset outer.snd
  have hB : ∀ u, u ∈ B ↔ ∃ a, R.face.SameCycle outer a ∧ a.fst = u := by simp [B]
  have hN : ∀ u, u ∈ N ↔ G.Adj outer.snd u := by simp [N]
  have hbcard := R.faceLength_eq_label_card outer (fun a => a.fst) B hsimple hB
  have hncard : N.card = G.degree outer.snd := G.card_neighborFinset_eq_degree outer.snd
  have hvB : outer.snd ∈ B := (hB _).mpr
    ⟨R.face outer,Equiv.Perm.SameCycle.rfl.apply_right,R.face_source outer⟩
  have htB : outer.fst ∈ B := (hB _).mpr ⟨outer,Equiv.Perm.SameCycle.rfl,rfl⟩
  have hsB : (R.face outer).snd ∈ B := (hB _).mpr
    ⟨R.face (R.face outer),Equiv.Perm.SameCycle.rfl.apply_right.apply_right,R.face_source _⟩
  have htN : outer.fst ∈ N := (hN _).mpr outer.adj.symm
  have hsN : (R.face outer).snd ∈ N := (hN _).mpr (by
    have h := (R.face outer).adj
    rwa [R.face_source] at h)
  have hne : outer.fst ≠ (R.face outer).snd := by
    intro h
    apply hcorner
    exact SimpleGraph.Dart.ext _ _ (Prod.ext (R.face_source outer) h.symm)
  have hinter : B ∩ N = {outer.fst,(R.face outer).snd} := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨huB,huN⟩
      obtain ⟨a,ha,he⟩ := (hB _).mp huB
      have hh := hchord a ha (he ▸ (hN _).mp huN)
      simpa only [he] using hh
    · rintro (rfl | rfl)
      · exact ⟨htB,htN⟩
      · exact ⟨hsB,hsN⟩
  have hintercard : (B ∩ N).card = 2 := by rw [hinter]; simp [hne]
  let T := (B ∪ N).erase outer.snd
  have htmem : ∀ u, u ∈ T ↔ ∃ x,
      (R.deleteVertex outer.snd).face.SameCycle root x ∧ x.fst.val = u := by
    intro u
    simp only [T,Finset.mem_erase,Finset.mem_union,hB,hN,hr]
    exact (R.outer_region_vertices outer hsimple hinner hcorner u).symm
  have htcard := (R.deleteVertex outer.snd).faceLength_eq_label_card root
    (fun x => x.fst.val) T (fun x y hx hy he =>
      R.outer_region_source_injective outer hsimple hinner hchord x y
        ((hr x).mp hx) ((hr y).mp hy) (Subtype.ext he)) htmem
  have hc := Finset.card_union_add_card_inter B N
  have he : T.card + 1 = (B ∪ N).card := by
    exact Finset.card_erase_add_one (Finset.mem_union_left N hvB)
  omega
end JSP512Probe.RotationSystem
