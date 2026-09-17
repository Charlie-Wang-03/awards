import Probe.CofacialInsertion
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Maximality is about actual supergraphs admitting genus-zero rotations,
not about a supplied face list or a coloring certificate. -/
def EdgeMaximalGenusZero (G : SimpleGraph V) : Prop :=
  ∀ H : SimpleGraph V, G ≤ H → (∃ S : RotationSystem H, S.HasGenusZero) →
    Nat.card H.edgeSet ≤ Nat.card G.edgeSet

/-- Every finite genus-zero rotation graph has a spanning genus-zero extension
with a maximal edge count. No triangulation conclusion is assumed. -/
theorem exists_maximal_augmentation (G : SimpleGraph V) (R : RotationSystem G)
    (hz : R.HasGenusZero) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ∃ S : RotationSystem H,
      S.HasGenusZero ∧ EdgeMaximalGenusZero H := by
  classical
  let candidates : Finset (SimpleGraph V) := Finset.univ.filter
    (fun H => G ≤ H ∧ ∃ S : RotationSystem H, S.HasGenusZero)
  have hn : candidates.Nonempty := ⟨G, by simp [candidates, show ∃ S : RotationSystem G,
    S.HasGenusZero from ⟨R,hz⟩]⟩
  obtain ⟨H, hH, hmax⟩ := candidates.exists_max_image (fun H => Nat.card H.edgeSet) hn
  have hh : G ≤ H ∧ ∃ S : RotationSystem H, S.HasGenusZero := (Finset.mem_filter.mp hH).2
  obtain ⟨S, hS⟩ := hh.2
  refine ⟨H, hh.1, S, hS, ?_⟩
  intro K hHK hK
  apply hmax K
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨le_trans hh.1 hHK, hK⟩

/-- In a maximal genus-zero supergraph, distinct source corners on a common
face must already be joined by an edge. -/
theorem maximal_cofacial_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (hz : R.HasGenusZero) (hmax : EdgeMaximalGenusZero G)
    (a b : G.Dart) (hne : a.fst ≠ b.fst) (hf : R.face.SameCycle a.symm b.symm) :
    G.Adj a.fst b.fst := by
  by_contra hm
  let H := EdgeInsertion.addedGraph G a.fst b.fst hne
  have hGH : G ≤ H := fun _ _ h => Or.inl h
  have hzero := EdgeInsertion.cofacial_genusZero G R a b hne hm hf hz
  have hle := hmax H hGH ⟨EdgeInsertion.addEdge G R a b hne hm,hzero⟩
  have hcard := EdgeInsertion.added_edge_count G a b hne hm
  change Nat.card H.edgeSet = Nat.card G.edgeSet + 1 at hcard
  omega

/-- Consequently the distinct source vertices encountered on any face are
pairwise adjacent. This does not yet show that a face has three darts. -/
theorem maximal_face_vertices_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (hz : R.HasGenusZero) (hmax : EdgeMaximalGenusZero G)
    (x y : G.Dart) (hne : x.fst ≠ y.fst) (hf : R.face.SameCycle x y) :
    G.Adj x.fst y.fst := by
  let a := (R.face.symm x).symm
  let b := (R.face.symm y).symm
  have ha : a.fst = x.fst := R.face_inverse_target x
  have hb : b.fst = y.fst := R.face_inverse_target y
  have hn : a.fst ≠ b.fst := by simpa only [ha,hb] using hne
  have hc : R.face.SameCycle a.symm b.symm := by
    change R.face.SameCycle (R.face.symm x).symm.symm (R.face.symm y).symm.symm
    simpa only [SimpleGraph.Dart.symm_symm] using hf.symm_apply_left.symm_apply_right
  have h := R.maximal_cofacial_adj hz hmax a b hn hc
  simpa only [ha,hb] using h

omit [DecidableEq V] in
/-- The edge-count formulation rules out every proper genus-zero supergraph. -/
theorem maximal_supergraph_eq {G : SimpleGraph V} (hmax : EdgeMaximalGenusZero G)
    (H : SimpleGraph V) (hGH : G ≤ H) (hH : ∃ S : RotationSystem H, S.HasGenusZero) : H = G := by
  classical
  have hc : H.edgeFinset.card ≤ G.edgeFinset.card := by
    simpa only [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card] using hmax H hGH hH
  have he := Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hGH) hc
  exact (SimpleGraph.edgeFinset_inj.mp he).symm

/-- The vertex set of every facial orbit in an edge-maximal genus-zero graph
is a clique. Repeated vertices and facial walk lengths are not resolved here. -/
theorem maximal_face_isClique {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (hz : R.HasGenusZero) (hmax : EdgeMaximalGenusZero G) (root : G.Dart) :
    G.IsClique {v | ∃ d : G.Dart, R.face.SameCycle root d ∧ d.fst = v} := by
  intro x hx y hy hne
  obtain ⟨dx, hx, rfl⟩ := hx
  obtain ⟨dy, hy, rfl⟩ := hy
  exact R.maximal_face_vertices_adj hz hmax dx dy hne (hx.symm.trans hy)

end JSP512Probe.RotationSystem
