import Probe.SourceSectorInterval

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [DecidableEq α] [Finite α]

/-- The two complementary first-hit intervals partition precisely the original
cycle, with no overlap and no missing element. -/
theorem two_cycle_intervals (σ : Equiv.Perm α) (a b : α) (hne : a ≠ b)
    (hab : σ.SameCycle a b) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ (σ ^ n) a = b ∧ (σ ^ m) b = a ∧
      Function.Injective (fun i : Fin n => (σ ^ i.val) a) ∧
      Function.Injective (fun j : Fin m => (σ ^ j.val) b) ∧
      (∀ i : Fin n, ∀ j : Fin m, (σ ^ i.val) a ≠ (σ ^ j.val) b) ∧
      ∀ x, σ.SameCycle a x ↔
        (∃ i : Fin n, (σ ^ i.val) a = x) ∨ (∃ j : Fin m, (σ ^ j.val) b = x) := by
  obtain ⟨n, hn, hnb, hni, _, hna⟩ := split_cycle_interval σ a b hne hab
  obtain ⟨m, hm, hma, hmi, _, hmb⟩ := split_cycle_interval σ b a hne.symm hab.symm
  simp only [Equiv.swap_comm b a] at hmb
  have sep := swap_splits σ a b hne hab
  refine ⟨n, m, hn, hm, hnb, hma, hni, hmi, ?_, ?_⟩
  · intro i j hh
    have hi := (hna ((σ ^ i.val) a)).mpr ⟨i.val, i.isLt, rfl⟩
    have hj := (hmb ((σ ^ j.val) b)).mpr ⟨j.val, j.isLt, rfl⟩
    exact sep (hi.trans (hh.symm ▸ hj.symm))
  · intro x
    constructor
    · intro hx
      rcases (split_cycle_partition σ a b x hne hab).mp hx.symm with hx | hx
      · obtain ⟨i, hi, he⟩ := (hna x).mp hx.symm
        exact Or.inl ⟨⟨i, hi⟩, he⟩
      · obtain ⟨j, hj, he⟩ := (hmb x).mp hx.symm
        exact Or.inr ⟨⟨j, hj⟩, he⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact Equiv.Perm.SameCycle.rfl.pow_right
      · exact hab.pow_right
end JSP512Probe.CycleSurgery

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

/-- Cutting the inverse source rotation at two darts partitions the actual
neighbor set. Distinct targets, disjointness, and both coverage directions are
proved without triangular-sector assumptions. -/
theorem source_neighbor_partition (root stop : G.Dart) (hr : root.fst = v)
    (hs : stop.fst = v) (hne : root ≠ stop) :
    let r : {d : G.Dart // d.fst = v} := ⟨root, hr⟩
    let s : {d : G.Dart // d.fst = v} := ⟨stop, hs⟩
    let σ : Equiv.Perm {d : G.Dart // d.fst = v} := (R.sourceRotation v).symm
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ (σ ^ n) r = s ∧ (σ ^ m) s = r ∧
      Function.Injective (fun i : Fin n => ((σ ^ i.val) r).val.snd) ∧
      Function.Injective (fun j : Fin m => ((σ ^ j.val) s).val.snd) ∧
      (∀ i : Fin n, ∀ j : Fin m, ((σ ^ i.val) r).val.snd ≠ ((σ ^ j.val) s).val.snd) ∧
      ∀ u, G.Adj v u ↔
        (∃ i : Fin n, ((σ ^ i.val) r).val.snd = u) ∨
        (∃ j : Fin m, ((σ ^ j.val) s).val.snd = u) := by
  classical
  dsimp only
  let r : {d : G.Dart // d.fst = v} := ⟨root, hr⟩
  let s : {d : G.Dart // d.fst = v} := ⟨stop, hs⟩
  let σ : Equiv.Perm {d : G.Dart // d.fst = v} := (R.sourceRotation v).symm
  have hc : ∀ x y, σ.SameCycle x y := by
    intro x y
    apply Equiv.Perm.SameCycle.inv
    apply (subtype_cycles R.rotate _ (fun d => by rw [R.source]) x y).mpr
    exact R.local_cycle x.val y.val (x.property.trans y.property.symm)
  have hi : Function.Injective (fun d : {d : G.Dart // d.fst = v} => d.val.snd) := by
    intro x y hh
    exact Subtype.ext (SimpleGraph.Dart.ext _ _ (Prod.ext (x.property.trans y.property.symm) hh))
  obtain ⟨n,m,hn,hm,hns,hmr,hni,hmi,hdis,hcov⟩ :=
    two_cycle_intervals σ r s (fun hh => hne (congrArg Subtype.val hh)) (hc r s)
  refine ⟨n,m,hn,hm,hns,hmr,fun i j hh => hni (hi hh),
    fun i j hh => hmi (hi hh),fun i j hh => hdis i j (hi hh),?_⟩
  intro u
  constructor
  · intro hu
    let e : {d : G.Dart // d.fst = v} := ⟨⟨(v,u),hu⟩,rfl⟩
    rcases (hcov e).mp (hc r e) with ⟨i,he⟩ | ⟨j,he⟩
    · exact Or.inl ⟨i,congrArg (fun d => d.val.snd) he⟩
    · exact Or.inr ⟨j,congrArg (fun d => d.val.snd) he⟩
  · rintro (⟨i,hi⟩ | ⟨j,hj⟩)
    · have h := ((σ ^ i.val) r).val.adj
      rwa [((σ ^ i.val) r).property,hi] at h
    · have h := ((σ ^ j.val) s).val.adj
      rwa [((σ ^ j.val) s).property,hj] at h

end JSP512Probe.RotationSystem
