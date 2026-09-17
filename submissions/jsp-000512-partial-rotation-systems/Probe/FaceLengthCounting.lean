import Probe.FaceVertexSimplicity

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

abbrev Orbit := Quotient (Equiv.Perm.SameCycle.setoid σ)
noncomputable instance orbitFintype : Fintype (Orbit σ) := Fintype.ofFinite _

noncomputable def orbitSize (q : Orbit σ) : ℕ :=
  Nat.card {x : α // Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x = q}

/-- The permutation orbits partition the underlying finite carrier. -/
theorem sum_orbitSize : ∑ q : Orbit σ, orbitSize σ q = Fintype.card α := by
  classical
  let f : α → Orbit σ := Quotient.mk _
  have hc := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, orbitSize, Nat.card_eq_fintype_card] using hc

/-- Without one- or two-step returns, every orbit contains at least three elements. -/
theorem orbitSize_three_le (h₁ : ∀ x, σ x ≠ x) (h₂ : ∀ x, σ (σ x) ≠ x)
    (q : Orbit σ) : 3 ≤ orbitSize σ q := by
  classical
  induction q using Quotient.inductionOn with
  | h x =>
    let A := {y : α // Quotient.mk (Equiv.Perm.SameCycle.setoid σ) y = Quotient.mk _ x}
    let a : A := ⟨x,rfl⟩
    let b : A := ⟨σ x,Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left⟩
    let c : A := ⟨σ (σ x),Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left.apply_left⟩
    have hab : a ≠ b := fun h => h₁ x (congrArg Subtype.val h).symm
    have hac : a ≠ c := fun h => h₂ x (congrArg Subtype.val h).symm
    have hbc : b ≠ c := fun h => h₁ x (σ.injective (congrArg Subtype.val h).symm)
    have hc : ({a,b,c} : Finset A).card = 3 := by simp [hab,hac,hbc]
    have hh := Finset.card_le_univ ({a,b,c} : Finset A)
    rw [hc] at hh
    simpa only [orbitSize, Nat.card_eq_fintype_card] using hh

/-- A distinguished long orbit uses carrier elements beyond the three-per-orbit minimum. -/
theorem orbit_size_budget (h₁ : ∀ x, σ x ≠ x) (h₂ : ∀ x, σ (σ x) ≠ x)
    (root : Orbit σ) :
    3 * Fintype.card (Orbit σ) + orbitSize σ root ≤ Fintype.card α + 3 := by
  classical
  have hmin : ∀ q, 3 ≤ orbitSize σ q := orbitSize_three_le σ h₁ h₂
  have hl := Finset.sum_le_sum (s := Finset.univ.erase root)
    (f := fun _ : Orbit σ => 3) (g := orbitSize σ) (fun q _ => hmin q)
  have he := Finset.sum_erase_add (s := Finset.univ) (f := orbitSize σ) (Finset.mem_univ root)
  rw [sum_orbitSize] at he
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ root),
    Finset.card_univ] at hl
  have hp : 0 < Fintype.card (Orbit σ) := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

end JSP512Probe.CycleSurgery

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

noncomputable def faceLength (d : G.Dart) : ℕ := orbitSize R.face (Quotient.mk _ d)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Facial length is the number of darts in the orbit of its chosen root. -/
theorem faceLength_eq_card (d : G.Dart) :
    R.faceLength d = Nat.card {e : G.Dart // R.face.SameCycle d e} := by
  classical
  let e : {x : G.Dart // Quotient.mk (Equiv.Perm.SameCycle.setoid R.face) x = Quotient.mk _ d} ≃
      {x : G.Dart // R.face.SameCycle d x} :=
    Equiv.subtypeEquivRight (fun x => ⟨fun h => (Quotient.exact h).symm,
      fun h => Quotient.sound h.symm⟩)
  exact Nat.card_congr e

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A two-step facial return forces a singleton rotation at its source. -/
theorem rotate_fixed_of_face_two_steps (d : G.Dart) (h : R.face (R.face d) = d) :
    R.rotate d = d := by
  have ht : (R.face d).snd = d.fst := by rw [← R.face_source (R.face d), h]
  have he : R.face d = d.symm := SimpleGraph.Dart.ext _ _ (Prod.ext (R.face_source d) ht)
  rw [he] at h
  change R.rotate d.symm.symm = d at h
  simpa only [SimpleGraph.Dart.symm_symm] using h

omit [DecidableEq V] in
/-- Exact facial budget, including the excess length of any chosen face. -/
theorem face_length_budget (hn : ∀ d, R.rotate d ≠ d) (d : G.Dart) :
    3 * R.faceCount + R.faceLength d ≤ 2 * Nat.card G.edgeSet + 3 := by
  have h₂ : ∀ d, R.face (R.face d) ≠ d :=
    fun d h => hn d (R.rotate_fixed_of_face_two_steps d h)
  have hh := orbit_size_budget R.face R.face_ne_self h₂ (Quotient.mk _ d)
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hh
  simpa only [faceCount, FaceOrbit, faceLength, Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card] using hh

omit [DecidableEq V] in
/-- The usual planar edge bound, sharpened by the length of a chosen face. -/
theorem genusZero_edge_face_bound (hz : R.HasGenusZero) (hc : G.Connected)
    (hs : G.support = Set.univ) (hn : ∀ d, R.rotate d ≠ d) (d : G.Dart) :
    (Nat.card G.edgeSet : ℤ) + R.faceLength d ≤ 3 * Fintype.card V - 3 := by
  have hb := R.face_length_budget hn d
  have hcomp := component_card_of_connected G hc
  have hsupport : supportSize (G := G) = (Fintype.card V : ℤ) := by
    unfold supportSize
    rw [hs]
    simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv]
  change R.eulerDefect = 0 at hz
  unfold eulerDefect at hz
  rw [hcomp, hsupport] at hz
  omega

theorem maximal_edge_face_bound (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (d : G.Dart) :
    (Nat.card G.edgeSet : ℤ) + R.faceLength d ≤ 3 * Fintype.card V - 3 :=
  R.genusZero_edge_face_bound hz (R.maximal_connected_of_dart hz hmax d)
    (R.maximal_support_univ hz hmax d)
    (fun e => (R.maximal_rotations_nonfixed hz hmax hn e).1) d

end JSP512Probe.RotationSystem
