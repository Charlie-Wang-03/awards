import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
A rotation system must have ONE cyclic orbit of outgoing darts at each
nonisolated vertex. Merely preserving the source of a dart is insufficient.
No recursive coloring certificate or coloring conclusion occurs in this model.
-/
namespace JSP512Probe

variable {V : Type*} (G : SimpleGraph V)

structure RotationSystem where
  rotate : Equiv.Perm G.Dart
  source : ∀ d, (rotate d).fst = d.fst
  local_cycle : ∀ d e, d.fst = e.fst → rotate.SameCycle d e

namespace RotationSystem

variable {G} (R : RotationSystem G)

def reverseDart : Equiv.Perm G.Dart where
  toFun := SimpleGraph.Dart.symm
  invFun := SimpleGraph.Dart.symm
  left_inv := SimpleGraph.Dart.symm_symm
  right_inv := SimpleGraph.Dart.symm_symm

/-- To walk along a face, reverse the dart then rotate at its new source. -/
def face : Equiv.Perm G.Dart := R.rotate * reverseDart

@[simp] theorem face_source (d : G.Dart) : (R.face d).fst = d.snd := by
  exact R.source d.symm

theorem face_ne_self (d : G.Dart) : R.face d ≠ d := by
  intro h
  have hh := congrArg (fun x : G.Dart => x.fst) h
  rw [R.face_source] at hh
  exact d.snd_ne_fst hh

@[simp] theorem face_inverse_target (d : G.Dart) : (R.face.symm d).snd = d.fst := by
  have h := R.face_source (R.face.symm d)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Consecutive sources in a facial walk are genuinely adjacent in the graph. -/
theorem face_step_adj (d : G.Dart) : G.Adj d.fst (R.face d).fst := by
  rw [R.face_source]
  exact d.adj

theorem rotate_pow_source (n : ℕ) (d : G.Dart) : ((R.rotate ^ n) d).fst = d.fst := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, R.source, ih]

variable [Fintype V] [DecidableRel G.Adj]

/-- The permutation's vertex orbits are exactly the actual incident-vertex fibers. -/
theorem sameCycle_iff_source (d e : G.Dart) :
    R.rotate.SameCycle d e ↔ d.fst = e.fst := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn, R.rotate_pow_source]
  · exact R.local_cycle d e

abbrev VertexOrbit := Quotient (Equiv.Perm.SameCycle.setoid R.rotate)
abbrev FaceOrbit := Quotient (Equiv.Perm.SameCycle.setoid R.face)

def orbitToVertex : R.VertexOrbit → G.support :=
  Quotient.lift (fun d : G.Dart => ⟨d.fst, d.adj.mem_support_left⟩)
    (by
      intro d e h
      apply Subtype.ext
      exact (R.sameCycle_iff_source d e).mp h)

theorem orbitToVertex_bijective : Function.Bijective R.orbitToVertex := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h d =>
      induction y using Quotient.inductionOn with
      | h e =>
        intro h
        apply Quotient.sound
        apply (R.sameCycle_iff_source d e).mpr
        exact congrArg Subtype.val h
  · intro v
    obtain ⟨w, hw⟩ := G.mem_support.mp v.property
    exact ⟨Quotient.mk _ ⟨(v.val,w),hw⟩, rfl⟩

noncomputable def vertexOrbitEquiv : R.VertexOrbit ≃ G.support :=
  Equiv.ofBijective R.orbitToVertex R.orbitToVertex_bijective

theorem vertexOrbit_card : Nat.card R.VertexOrbit = Nat.card G.support :=
  Nat.card_congr R.vertexOrbitEquiv

/-- Quotient orbits count all faces; no reliance on a list of nontrivial cycles. -/
noncomputable def faceCount : ℕ := Nat.card R.FaceOrbit

end RotationSystem
end JSP512Probe
