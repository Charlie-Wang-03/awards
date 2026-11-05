import JSP000404Research.OrderedDirectionWires
import JSP000404Research.ProjectionLocalDirectionValue
import JSP000404Research.AngleCapStrictProjectiveTheta

/-!
# Strict local wire directions of actual planar configurations

The existing projective-ray injectivity theorem survives the generic cut rotation and
normalization. Thus genuine positive-angle-cap configurations supply the local injectivity
used by the consecutive-wire construction. Local injectivity also makes triangle
betweenness strict.
-/

namespace JSP000404Research

namespace DirectionData

theorem strict_between_of_local_injective
    {V : Type*} [LinearOrder V] {width : ℝ} (D : DirectionData V width)
    (hinjective : ∀ v, Function.Injective (D.localDirectionValue v))
    {i j k : V} (hij : i < j) (hjk : j < k) :
    (D.value i j < D.value i k ∧ D.value i k < D.value j k) ∨
    (D.value j k < D.value i k ∧ D.value i k < D.value i j) := by
  have hik := hij.trans hjk
  have hfirst : D.value i j ≠ D.value i k := by
    intro heq
    have hlocal : D.localDirectionValue i ⟨j, ne_of_gt hij⟩ =
        D.localDirectionValue i ⟨k, ne_of_gt hik⟩ := by
      simpa [localDirectionValue, not_lt_of_ge hij.le, not_lt_of_ge hik.le] using heq
    have h := congrArg Subtype.val (hinjective i hlocal)
    exact (ne_of_lt hjk) h
  have hlast : D.value i k ≠ D.value j k := by
    intro heq
    have hlocal : D.localDirectionValue k ⟨i, ne_of_lt hik⟩ =
        D.localDirectionValue k ⟨j, ne_of_lt hjk⟩ := by
      simpa [localDirectionValue, hik, hjk] using heq
    have h := congrArg Subtype.val (hinjective k hlocal)
    exact (ne_of_lt hij) h
  rcases D.between hij hjk with h | h
  · exact Or.inl ⟨lt_of_le_of_ne h.1 hfirst, lt_of_le_of_ne h.2 hlast⟩
  · exact Or.inr ⟨lt_of_le_of_ne h.1 hlast.symm, lt_of_le_of_ne h.2 hfirst.symm⟩

end DirectionData

namespace ProjectionOrdered

theorem generic_localDirectionValue_injective
    {V : Type*} [Fintype V] {p : V → Plane} (hp : Function.Injective p)
    {lam width : ℝ} (hcap : AngleCap p lam) (hwidth : 0 < width)
    (hlam : lam = Real.pi / width) (v : ProjectionOrdered V) :
    letI := projectionLinearOrder hp
    Function.Injective
      ((genericDirectionData_sendov hp hcap hwidth hlam).localDirectionValue v) := by
  let := projectionLinearOrder hp
  have hlampos : 0 < lam := by rw [hlam]; exact div_pos Real.pi_pos hwidth
  intro a b heq
  apply rayThetaAt_injective_of_AngleCap (reindexedPoint_injective hp)
    (angleCap_reindexed hcap) hlampos v
  have ha0 := rayThetaAt_nonneg (reindexedPoint_injective hp) v a
  have hb0 := rayThetaAt_nonneg (reindexedPoint_injective hp) v b
  have hal := rayThetaAt_lt_pi (reindexedPoint_injective hp) v a
  have hbl := rayThetaAt_lt_pi (reindexedPoint_injective hp) v b
  rw [genericLocalDirectionValue_eq_cutRotate hp hcap hwidth hlam v a,
    genericLocalDirectionValue_eq_cutRotate hp hcap hwidth hlam v b] at heq
  split_ifs at heq <;> field_simp [ne_of_gt hlampos] at heq <;> linarith

#print axioms generic_localDirectionValue_injective

end ProjectionOrdered

#print axioms DirectionData.strict_between_of_local_injective

end JSP000404Research
