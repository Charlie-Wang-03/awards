import Probe.CompleteFaceBound
import Probe.PreserveFace
import Probe.SupportRealization

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Every facial orbit in an edge-maximal genus-zero graph has at most three darts. -/
theorem maximal_faceLength_le_three (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (root : G.Dart) : R.faceLength root ≤ 3 := by
  classical
  let A := {d : G.Dart // R.face.SameCycle root d}
  let : Fintype A := Fintype.ofFinite _
  let r : A := ⟨root,Equiv.Perm.SameCycle.rfl⟩
  have hp : ∀ d, R.face.SameCycle root d ↔ R.face.SameCycle root (R.face d) := by
    intro d
    constructor
    · exact fun h => h.apply_right
    · intro h
      simpa only [Equiv.symm_apply_apply] using h.symm_apply_right
  let π : Equiv.Perm A := R.face.subtypeEquiv hp
  have hcyc : ∀ x y : A, π.SameCycle x y := by
    intro x y
    exact (subtype_cycles R.face _ hp x y).mpr (x.property.symm.trans y.property)
  have hsrc : Function.Injective (fun d : A => d.val.fst) := by
    intro x y h
    exact Subtype.ext (R.maximal_face_source_injOn hz hmax root x.property y.property h)
  let L : SimpleGraph V := {
    Adj := fun u v => ∃ x y : A, x.val.fst = u ∧ y.val.fst = v ∧ u ≠ v
    symm := ⟨by rintro u v ⟨x,y,hx,hy,hn⟩; exact ⟨y,x,hy,hx,hn.symm⟩⟩
    loopless := ⟨by rintro u ⟨x,y,hx,hy,hn⟩; exact hn rfl⟩ }
  have hLG : L ≤ G := by
    rintro u v ⟨x,y,rfl,rfl,hne⟩
    exact R.maximal_face_vertices_adj hz hmax x.val y.val hne (x.property.symm.trans y.property)
  have hkeep : ∀ x : A, L.Adj x.val.fst x.val.snd := by
    intro x
    exact ⟨x,π x,rfl,R.face_source x.val,x.val.fst_ne_snd⟩
  obtain ⟨T,hT,g,hg,hstep⟩ := R.genusZero_subgraph_preserving_steps π L hz hLG
    (fun x : A => x.val) (fun _ => rfl) hkeep
  have hfst : ∀ x, (g x).fst = x.val.fst := fun x => congrArg Prod.fst (hg x)
  let Q := RefinedRotation.Vertex L T.rotate
  let : Fintype Q := Fintype.ofFinite _
  let J := RefinedRotation.graph L T.rotate T.source
  let S := RefinedRotation.rotation L T.rotate T.source
  let q := RefinedRotation.vertex L T.rotate
  let e := RefinedRotation.dartEquiv L T.rotate T.source
  have hbijection : Function.Bijective (fun x : A => q (g x)) := by
    constructor
    · intro x y h
      apply hsrc
      have hh := (T.sameCycle_iff_source _ _).mp (Quotient.exact h)
      simpa only [hfst] using hh
    · intro p
      induction p using Quotient.inductionOn with
      | h d =>
        obtain ⟨x,y,hx,hy,hn⟩ := d.adj
        exact ⟨x,Quotient.sound (T.local_cycle _ _ ((hfst x).trans hx))⟩
  have hcard : Fintype.card Q = Fintype.card A :=
    (Fintype.card_congr (Equiv.ofBijective _ hbijection)).symm
  have htop : J = ⊤ := by
    apply le_antisymm le_top
    intro p q' hpq
    obtain ⟨x,rfl⟩ := hbijection.2 p
    obtain ⟨y,rfl⟩ := hbijection.2 q'
    have hne : x.val.fst ≠ y.val.fst := by
      intro h
      exact hpq (congrArg (fun x : A => q (g x)) (hsrc h))
    let d : L.Dart := ⟨(x.val.fst,y.val.fst),⟨x,y,rfl,rfl,hne⟩⟩
    exact ⟨d,Quotient.sound (T.local_cycle _ _ (hfst x).symm),
      Quotient.sound (T.local_cycle _ _ (hfst y).symm)⟩
  have : Nonempty Q := ⟨q (g r)⟩
  have hJconn : J.Connected := by rw [htop]; exact SimpleGraph.connected_top
  have hcomp : Nat.card L.ConnectedComponent + Nat.card L.support = Fintype.card V + 1 := by
    apply component_support_count root.fst (hkeep r).mem_support_left
    intro v hv
    obtain ⟨w,hw⟩ := L.mem_support.mp hv
    obtain ⟨x,y,hx,hy,hn⟩ := hw
    by_cases he : root.fst = v
    · exact he ▸ SimpleGraph.Reachable.rfl
    · exact (show L.Adj root.fst v from ⟨r,x,rfl,hx,he⟩).reachable
  have hzero : S.HasGenusZero := T.realized_genusZero hT hcomp hJconn
  let f : A → J.Dart := fun x => e (g x)
  have hfi : Function.Injective f := by
    intro x y h
    apply hbijection.1
    exact congrArg q (e.injective h)
  have hfstep : ∀ x, f (π x) = S.face (f x) := by
    intro x
    change e (g (π x)) = e (T.rotate (e.symm ((e (g x)).symm)))
    rw [← RefinedRotation.dart_reverse, e.symm_apply_apply, hstep x]
    rfl
  have hfcycle : ∀ x, S.face.SameCycle (f r) (f x) := by
    intro x
    exact (sameCycle_embedding π S.face f hfi hfstep r x).mpr (hcyc r x)
  have hlong : Fintype.card Q ≤ S.faceLength (f r) := by
    rw [hcard, S.faceLength_eq_card]
    let i : A → {d : J.Dart // S.face.SameCycle (f r) d} := fun x => ⟨f x,hfcycle x⟩
    have hi : Function.Injective i := fun x y h => hfi (congrArg Subtype.val h)
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective i hi
  have hlen : R.faceLength root = Fintype.card A := by
    rw [R.faceLength_eq_card]
    exact Nat.card_eq_fintype_card
  by_contra hn
  have hn' : 4 ≤ Fintype.card Q := by omega
  exact S.complete_spanning_face_impossible hzero htop hn' (f r) hlong

/-- With at least three vertices, maximal genus-zero faces have exactly three darts. -/
theorem maximal_faceLength_eq_three (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (root : G.Dart) :
    R.faceLength root = 3 := by
  have hu := R.maximal_faceLength_le_three hz hmax root
  have hl := orbitSize_three_le R.face R.face_ne_self
    (R.maximal_face_two_steps_ne hz hmax hn) (Quotient.mk _ root)
  change 3 ≤ R.faceLength root at hl
  omega

omit [DecidableRel G.Adj] in
/-- Every finite genus-zero graph on at least three vertices has a spanning
connected genus-zero extension whose every facial orbit has length three. -/
theorem exists_triangular_augmentation (hz : R.HasGenusZero)
    (hn : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ∃ S : RotationSystem H,
      S.HasGenusZero ∧ H.Connected ∧ ∀ d : H.Dart, S.faceLength d = 3 := by
  classical
  obtain ⟨H,hGH,S,hS,hmax⟩ := exists_maximal_augmentation G R hz
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  exact ⟨H,hGH,S,hS,S.maximal_connected hS hmax,
    S.maximal_faceLength_eq_three hS hmax hn⟩

/-- The three darts exhaust their facial orbit, with no hidden repetitions. -/
theorem maximal_face_darts_iff (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (root e : G.Dart) :
    R.face.SameCycle root e ↔
      e = root ∨ e = R.face root ∨ e = R.face (R.face root) := by
  classical
  let A := {d : G.Dart // R.face.SameCycle root d}
  let : Fintype A := Fintype.ofFinite _
  let a : A := ⟨root,Equiv.Perm.SameCycle.rfl⟩
  let b : A := ⟨R.face root,Equiv.Perm.SameCycle.rfl.apply_right⟩
  let c : A := ⟨R.face (R.face root),Equiv.Perm.SameCycle.rfl.apply_right.apply_right⟩
  have hab : a ≠ b := fun h => R.face_ne_self root (congrArg Subtype.val h).symm
  have hac : a ≠ c := fun h =>
    R.maximal_face_two_steps_ne hz hmax hn root (congrArg Subtype.val h).symm
  have hbc : b ≠ c := fun h =>
    R.face_ne_self root (R.face.injective (congrArg Subtype.val h).symm)
  have hc : Fintype.card A = 3 := by
    have hh := R.maximal_faceLength_eq_three hz hmax hn root
    rw [R.faceLength_eq_card] at hh
    simpa only [Nat.card_eq_fintype_card] using hh
  have hu : ({a,b,c} : Finset A) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hc,hab,hac,hbc]
  constructor
  · intro h
    have hm : (⟨e,h⟩ : A) ∈ ({a,b,c} : Finset A) := by rw [hu]; exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  · rintro (rfl | rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.SameCycle.rfl.apply_right
    · exact Equiv.Perm.SameCycle.rfl.apply_right.apply_right

/-- The facial successor closes after exactly three steps. -/
theorem maximal_face_three_steps (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (d : G.Dart) :
    R.face (R.face (R.face d)) = d := by
  have hh := (R.maximal_face_darts_iff hz hmax hn d _).mp
    Equiv.Perm.SameCycle.rfl.apply_right.apply_right.apply_right
  rcases hh with h | h | h
  · exact h
  · exact False.elim (R.maximal_face_two_steps_ne hz hmax hn d (R.face.injective h))
  · exact False.elim (R.face_ne_self d (R.face.injective (R.face.injective h)))

end JSP512Probe.RotationSystem
