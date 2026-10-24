import JSP000404Research.SeparatedSupportTwoTrianglePropagation
import Mathlib.Tactic

/-!
# An original three-vertex small-angle certificate determines its apex

Under planar AngleCap and delta < 1/2, a triangle cannot support small
angles at two different vertices. This upgrades angle rigidity to
INJECTIVITY over unordered three-vertex original-plane triangle supports.
It does not supply global Boolean-hole or dyadic payment.
-/

namespace JSP000404Research

theorem actual_small_triangle_apex_unique_of_same_support
    {V : Type*} [DecidableEq V] {p : V → Plane}
    (hp : Function.Injective p)
    {delta lam : ℝ}
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {s a b t c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (htc : t ≠ c) (htd : t ≠ d) (hcd : c ≠ d)
    (hsmallS :
      EuclideanGeometry.angle (p a) (p s) (p b) ≤ delta * lam)
    (hsmallT :
      EuclideanGeometry.angle (p c) (p t) (p d) ≤ delta * lam)
    (hsupport :
      ({s,a,b} : Finset V) = {t,c,d}) :
    s = t := by
  have hgap : delta * lam < (1 - delta) * lam := by
    have hpos : 0 < (1 - 2 * delta) * lam :=
      mul_pos (by linarith) hlampos
    nlinarith
  obtain ⟨hbigA, hbigB⟩ :=
    both_outer_angles_ge_of_actual_small_angle
      hp hcap hsa hsb hab hsmallS
  have hstrictA :
      delta * lam <
        EuclideanGeometry.angle (p s) (p a) (p b) :=
    hgap.trans_le hbigA
  have hstrictB :
      delta * lam <
        EuclideanGeometry.angle (p s) (p b) (p a) :=
    hgap.trans_le hbigB
  have htMem : t = s ∨ t = a ∨ t = b := by
    have hmem : t ∈ ({s,a,b} : Finset V) := by
      rw [hsupport]
      simp
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases htMem with hts | hta | htb
  · exact hts.symm
  · subst t
    have hsMem : s = a ∨ s = c ∨ s = d := by
      have hmem : s ∈ ({a,c,d} : Finset V) := by
        rw [← hsupport]
        simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hbMem : b = a ∨ b = c ∨ b = d := by
      have hmem : b ∈ ({a,c,d} : Finset V) := by
        rw [← hsupport]
        simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hsCD : s = c ∨ s = d := by
      rcases hsMem with h | h | h
      · exact (hsa h).elim
      · exact Or.inl h
      · exact Or.inr h
    have hbCD : b = c ∨ b = d := by
      rcases hbMem with h | h | h
      · exact (hab h.symm).elim
      · exact Or.inl h
      · exact Or.inr h
    rcases hsCD with hsc | hsd
    · rcases hbCD with hbc | hbd
      · exact (hsb (hsc.trans hbc.symm)).elim
      · have hsmallA := hsmallT
        rw [← hsc, ← hbd] at hsmallA
        exact (False.elim ((not_le_of_gt hstrictA) hsmallA))
    · rcases hbCD with hbc | hbd
      · have hsmallA := hsmallT
        rw [← hbc, ← hsd] at hsmallA
        rw [EuclideanGeometry.angle_comm (p b) (p a) (p s)] at hsmallA
        exact (False.elim ((not_le_of_gt hstrictA) hsmallA))
      · exact (hsb (hsd.trans hbd.symm)).elim
  · subst t
    have hsMem : s = b ∨ s = c ∨ s = d := by
      have hmem : s ∈ ({b,c,d} : Finset V) := by
        rw [← hsupport]
        simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    have haMem : a = b ∨ a = c ∨ a = d := by
      have hmem : a ∈ ({b,c,d} : Finset V) := by
        rw [← hsupport]
        simp
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hsCD : s = c ∨ s = d := by
      rcases hsMem with h | h | h
      · exact (hsb h).elim
      · exact Or.inl h
      · exact Or.inr h
    have haCD : a = c ∨ a = d := by
      rcases haMem with h | h | h
      · exact (hab h).elim
      · exact Or.inl h
      · exact Or.inr h
    rcases hsCD with hsc | hsd
    · rcases haCD with hac | had
      · exact (hsa (hsc.trans hac.symm)).elim
      · have hsmallB := hsmallT
        rw [← hsc, ← had] at hsmallB
        exact (False.elim ((not_le_of_gt hstrictB) hsmallB))
    · rcases haCD with hac | had
      · have hsmallB := hsmallT
        rw [← hac, ← hsd] at hsmallB
        rw [EuclideanGeometry.angle_comm (p a) (p b) (p s)] at hsmallB
        exact (False.elim ((not_le_of_gt hstrictB) hsmallB))
      · exact (hsa (hsd.trans had.symm)).elim

#print axioms actual_small_triangle_apex_unique_of_same_support

end JSP000404Research
