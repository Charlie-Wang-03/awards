import Probe.DeletedNeighborBoundary

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

/-- A nonfixed orbit with a three-step return has exactly three elements. -/
theorem orbitSize_eq_three (x : α) (hn : σ x ≠ x)
    (ht : σ (σ (σ x)) = x) : orbitSize σ (Quotient.mk _ x) = 3 := by
  classical
  have htwo : σ (σ x) ≠ x := by
    intro h
    rw [h] at ht
    exact hn ht
  have horbit : ∀ y, σ.SameCycle y x ↔ y ∈ ({x, σ x, σ (σ x)} : Finset α) := by
    intro y
    constructor
    · intro h
      obtain ⟨n, rfl⟩ := h.symm.exists_nat_pow_eq
      clear h
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
        rcases ih with h | h | h
        · exact Or.inr (Or.inl (congrArg σ h))
        · exact Or.inr (Or.inr (congrArg σ h))
        · exact Or.inl ((congrArg σ h).trans ht)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl)
      · exact Equiv.Perm.SameCycle.rfl
      · exact Equiv.Perm.SameCycle.rfl.apply_left
      · exact Equiv.Perm.SameCycle.rfl.apply_left.apply_left
  let e := Equiv.subtypeEquivRight (fun y =>
    (show Quotient.mk (Equiv.Perm.SameCycle.setoid σ) y = Quotient.mk _ x ↔
      y ∈ ({x, σ x, σ (σ x)} : Finset α) from Quotient.eq.trans (horbit y)))
  have hlast : σ x ≠ σ (σ x) := fun h => hn (σ.injective h).symm
  unfold orbitSize
  rw [Nat.card_congr e]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simp [hn.symm, htwo.symm, hlast]

/-- Exact counting when every orbit except one has size three. -/
theorem orbit_size_exact (root : Orbit σ)
    (h : ∀ q, q ≠ root → orbitSize σ q = 3) :
    3 * Fintype.card (Orbit σ) + orbitSize σ root = Fintype.card α + 3 := by
  classical
  have he := Finset.sum_erase_add (s := Finset.univ) (f := orbitSize σ)
    (Finset.mem_univ root)
  have hs : ∑ q ∈ Finset.univ.erase root, orbitSize σ q =
      ∑ _q ∈ Finset.univ.erase root, 3 :=
    Finset.sum_congr rfl (fun q hq => h q (Finset.mem_erase.mp hq).1)
  rw [hs, sum_orbitSize] at he
  simp only [Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ root), Finset.card_univ] at he
  have hp := Fintype.card_pos_iff.mpr (show Nonempty (Orbit σ) from ⟨root⟩)
  omega
end JSP512Probe.CycleSurgery

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Exact face count for the actual rotation obtained by deleting a vertex. -/
theorem deleted_face_count (v : V)
    (htri : ∀ d, R.face (R.face (R.face d)) = d)
    (root : {d : G.Dart // d.fst = v}) :
    3 * (R.deleteVertex v).faceCount + G.degree v =
      2 * Nat.card (VertexDeletedGraph (G := G) v).edgeSet + 3 := by
  classical
  let S := R.deleteVertex v
  let b := R.boundarySector v htri root
  have hq : ∀ q : Orbit S.face, q ≠ Quotient.mk _ b → orbitSize S.face q = 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      apply orbitSize_eq_three S.face x (S.face_ne_self x)
      apply R.deleted_nonboundary_triangular v htri root x
      intro hc
      exact hx (Quotient.sound hc.symm)
  have hh := orbit_size_exact S.face (Quotient.mk _ b) hq
  have hb := R.deleted_boundary_length v htri root
  change orbitSize S.face (Quotient.mk _ b) = G.degree v at hb
  rw [hb, SimpleGraph.dart_card_eq_twice_card_edges] at hh
  simpa only [faceCount, FaceOrbit, Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card] using hh
omit [DecidableEq V] in
/-- A triangular rotation has three darts per face. -/
theorem triangular_face_count
    (htri : ∀ d, R.face (R.face (R.face d)) = d) :
    3 * R.faceCount = 2 * Nat.card G.edgeSet := by
  classical
  have hq : ∀ q : Orbit R.face, orbitSize R.face q = 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact orbitSize_eq_three R.face x (R.face_ne_self x) (htri x)
  have hh := sum_orbitSize R.face
  simp only [hq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hh
  simpa only [faceCount, FaceOrbit, Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card, Nat.mul_comm] using hh

end JSP512Probe.RotationSystem
