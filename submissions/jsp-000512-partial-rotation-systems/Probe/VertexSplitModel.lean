import Probe.MaximalLinks
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace JSP512Probe.RefinedRotation
open RotationSystem CycleSurgery
variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart)
  (hs : ∀ d, (σ d).fst = d.fst)

abbrev Vertex := Quotient (Equiv.Perm.SameCycle.setoid σ)
abbrev vertex (d : G.Dart) : Vertex G σ := Quotient.mk _ d

include hs in
omit [DecidableEq V] in
theorem cycle_source {d e : G.Dart} (h : σ.SameCycle d e) : d.fst = e.fst := by
  obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hs]; exact ih

def project : Vertex G σ → V :=
  Quotient.lift (fun d : G.Dart => d.fst) (fun _ _ h => cycle_source G σ hs h)

/-- Realize each rotation cycle as a separate vertex, without changing the edges. -/
def graph : SimpleGraph (Vertex G σ) where
  Adj x y := ∃ d : G.Dart, vertex G σ d = x ∧ vertex G σ d.symm = y
  symm := ⟨by
    rintro x y ⟨d,rfl,rfl⟩
    exact ⟨d.symm,rfl,by simp [SimpleGraph.Dart.symm_symm]⟩⟩
  loopless := ⟨by
    rintro x ⟨d,hd,he⟩
    have h := congrArg (project G σ hs) (hd.trans he.symm)
    exact d.fst_ne_snd h⟩

def dart (d : G.Dart) : (graph G σ hs).Dart :=
  ⟨(vertex G σ d, vertex G σ d.symm), ⟨d,rfl,rfl⟩⟩

omit [DecidableEq V] in
theorem dart_bijective : Function.Bijective (dart G σ hs) := by
  constructor
  · intro d e h
    have hf := congrArg (fun a : (graph G σ hs).Dart => project G σ hs a.fst) h
    have ht := congrArg (fun a : (graph G σ hs).Dart => project G σ hs a.snd) h
    exact SimpleGraph.Dart.ext _ _ (Prod.ext hf ht)
  · intro e
    obtain ⟨d,hd,he⟩ := e.adj
    exact ⟨d,SimpleGraph.Dart.ext _ _ (Prod.ext hd he)⟩

noncomputable def dartEquiv : G.Dart ≃ (graph G σ hs).Dart :=
  Equiv.ofBijective (dart G σ hs) (dart_bijective G σ hs)

omit [DecidableEq V] in
theorem dart_reverse (d : G.Dart) :
    dartEquiv G σ hs d.symm = (dartEquiv G σ hs d).symm := by
  apply SimpleGraph.Dart.ext
  exact Prod.ext rfl (by simp [dartEquiv, dart, SimpleGraph.Dart.symm_symm])

noncomputable def rotation : RotationSystem (graph G σ hs) := by
  classical
  let e := dartEquiv G σ hs
  let τ : Equiv.Perm (graph G σ hs).Dart := (e.symm.trans σ).trans e
  have hc : ∀ x y, τ.SameCycle x y ↔ x.fst = y.fst := by
    intro x y
    obtain ⟨d,rfl⟩ := e.surjective x
    obtain ⟨f,rfl⟩ := e.surjective y
    have hh := transport_cycles e.symm σ (e d) (e f)
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at hh
    rw [hh]
    change σ.SameCycle d f ↔ vertex G σ d = vertex G σ f
    exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩
  exact ⟨τ,fun _ => (hc _ _).mp Equiv.Perm.SameCycle.rfl.apply_left,
    fun _ _ h => (hc _ _).mpr h⟩

omit [DecidableEq V] in
theorem face_count : (rotation G σ hs).faceCount =
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (σ * (reverseDart : Equiv.Perm G.Dart)))) := by
  classical
  let e := dartEquiv G σ hs
  let τ := σ * (reverseDart : Equiv.Perm G.Dart)
  let F := (rotation G σ hs).face
  have hc : ∀ x, e (τ x) = F (e x) := by
    intro x
    change e (σ x.symm) = e (σ (e.symm ((e x).symm)))
    rw [← dart_reverse, e.symm_apply_apply]
  let qe : Quotient (Equiv.Perm.SameCycle.setoid τ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid F) := Quotient.congr e (fun x y => (sameCycle_embedding τ F e e.injective hc x y).symm)
  exact (Nat.card_congr qe).symm

omit [DecidableEq V] in
theorem full_support : (graph G σ hs).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | h d => exact (dart G σ hs d).adj.mem_support_left

omit [DecidableEq V] in
theorem edge_count : Nat.card (graph G σ hs).edgeSet = Nat.card G.edgeSet := by
  classical
  let : Fintype (Vertex G σ) := Fintype.ofFinite _
  have hd := Fintype.card_congr (dartEquiv G σ hs)
  rw [SimpleGraph.dart_card_eq_twice_card_edges,
    SimpleGraph.dart_card_eq_twice_card_edges] at hd
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using (Nat.mul_left_cancel (by omega : 0 < 2) hd).symm

end JSP512Probe.RefinedRotation
