import Probe.FaceLengthCounting
import Mathlib.Tactic.Linarith

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [DecidableRel G.Adj] in
/-- In a complete graph on at least three vertices, no rotation can be a singleton. -/
theorem complete_rotations_nonfixed (htop : G = ⊤) (hn : 3 ≤ Fintype.card V)
    (d : G.Dart) : R.rotate d ≠ d := by
  intro hf
  have hall : ∀ v : V, v = d.fst ∨ v = d.snd := by
    intro v
    by_cases hv : v = d.fst
    · exact Or.inl hv
    · have ha : G.Adj d.fst v := by simpa only [htop, SimpleGraph.top_adj] using (Ne.symm hv)
      have he := (R.rotate_fixed_iff_unique d).mp hf ⟨(d.fst,v),ha⟩ rfl
      exact Or.inr (congrArg (fun e : G.Dart => e.snd) he)
  have hu : (Finset.univ : Finset V) = {d.fst,d.snd} := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall v
  have hc := congrArg Finset.card hu
  simp only [Finset.card_univ, Finset.card_pair d.fst_ne_snd] at hc
  omega

/-- A complete genus-zero graph with a face visiting every vertex has at most
three vertices. This is the counting obstruction for a large facial clique. -/
theorem complete_spanning_face_impossible (hz : R.HasGenusZero) (htop : G = ⊤)
    (hn : 4 ≤ Fintype.card V) (d : G.Dart) (hl : Fintype.card V ≤ R.faceLength d) : False := by
  have : Nonempty V := ⟨d.fst⟩
  have hc : G.Connected := by rw [htop]; exact SimpleGraph.connected_top
  have hs : G.support = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    by_cases hv : v = d.fst
    · exact hv ▸ d.adj.mem_support_left
    · exact SimpleGraph.mem_support_of_reachable hv (hc v d.fst)
  have hb := R.genusZero_edge_face_bound hz hc hs
    (R.complete_rotations_nonfixed htop (by omega)) d
  have he := (⊤ : SimpleGraph V).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.complete_graph_degree, Finset.sum_const, Finset.card_univ, smul_eq_mul] at he
  have hedge : 2 * Nat.card G.edgeSet = Fintype.card V * (Fintype.card V - 1) := by
    rw [htop]
    simpa only [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card] using he.symm
  have hzedge : 2 * (Nat.card G.edgeSet : ℤ) =
      (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 1) := by
    have hh := congrArg (fun x : ℕ => (x : ℤ)) hedge
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one] using hh
  have hlarge : (4 : ℤ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlong : (Fintype.card V : ℤ) ≤ R.faceLength d := by exact_mod_cast hl
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ Fintype.card V - 4)
    (by omega : (0 : ℤ) ≤ Fintype.card V - 1)]

end JSP512Probe.RotationSystem
