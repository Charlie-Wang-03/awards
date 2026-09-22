
import JSP000404Research.ResidualDuplicateBudget
import Mathlib.Tactic

/-!
# The last duplicated retained-code fibre

A duplicated retained-code fibre has size exactly two, and its later vertex is
characterized by HasEarlierSame.

Because the vertex set is finite and linearly ordered, if any duplicate fibre
exists there is a last duplicated upper endpoint v.

This order is useful for the monotone Boolean-hole route. If u<v is that last
duplicate pair and an inactive-coordinate flip at u is occupied, the blocker
lies strictly to the right of v. No vertex to the right of v can belong to
any duplicated retained-code fibre, so every such blocker has a globally
unique retained code.

Thus the Hamming neighbours blocking the last hard pair land in distinct
singleton retained-code fibres.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def duplicateUpperSet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => HasEarlierSame C v

@[simp] theorem mem_duplicateUpperSet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    v ∈ duplicateUpperSet C ↔ HasEarlierSame C v := by
  classical
  simp [duplicateUpperSet]

theorem exists_last_duplicate_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hdup : ∃ v : V, HasEarlierSame C v) :
    ∃ v : V,
      HasEarlierSame C v ∧
      ∀ w : V, v < w → ¬ HasEarlierSame C w := by
  classical
  let S := duplicateUpperSet C
  have hSne : S.Nonempty := by
    obtain ⟨v, hv⟩ := hdup
    exact ⟨v, by simpa [S] using hv⟩
  let v : V := S.max' hSne
  have hvS : v ∈ S := Finset.max'_mem S hSne
  refine ⟨v, ?_, ?_⟩
  · simpa [S] using hvS
  · intro w hvw hw
    have hwS : w ∈ S := by
      simpa [S] using hw
    have hwle : w ≤ v := by
      exact Finset.le_max' S w hwS
    exact (not_lt_of_ge hwle) hvw

theorem retained_code_unique_right_of_last_duplicate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w x : V}
    (hlast : ∀ z : V, v < z → ¬ HasEarlierSame C z)
    (hvw : v < w)
    (hsame : SameRetained C x w) :
    x = w := by
  by_contra hxw
  rcases lt_or_gt_of_ne hxw with hxwlt | hwx
  · exact (hlast w hvw) ⟨x, hxwlt, hsame⟩
  · have hvx : v < x := hvw.trans hwx
    exact (hlast x hvx)
      ⟨w, hwx, sameRetained_symm hsame⟩

theorem last_duplicate_blocker_code_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hlast : ∀ z : V, v < z → ¬ HasEarlierSame C z)
    (hcu : c ∉ retainedActive C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    ∀ x : V, SameRetained C x w → x = w := by
  have hvw :
      v < w :=
    blocker_after_other_of_lower_inactive
      C huv hsame
      (by
        intro hc
        exact hcu
          ((castSucc_mem_active_iff_mem_retainedActive
            C u c).1 hc))
      hblock
  intro x hx
  exact retained_code_unique_right_of_last_duplicate
    C hlast hvw hx

theorem last_duplicate_inactive_injects_singleton_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hlast : ∀ z : V, v < z → ¬ HasEarlierSame C z)
    (hoccupied :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V,
          (fun d => retainedBit C w d) =
            flippedRetainedCode C u c) :
    ∃ f :
        {c : Fin n // c ∈ retainedInactive C u} →
          {w : V // v < w},
      Function.Injective f ∧
      ∀ c,
        ∀ x : V,
          SameRetained C x (f c).1 →
          x = (f c).1 := by
  classical
  let chooseBlocker :
      {c : Fin n // c ∈ retainedInactive C u} → V :=
    fun c => Classical.choose (hoccupied c.1 c.2)
  have hchooseCode :
      ∀ c : {c : Fin n // c ∈ retainedInactive C u},
        (fun d => retainedBit C (chooseBlocker c) d) =
          flippedRetainedCode C u c.1 := by
    intro c
    exact Classical.choose_spec (hoccupied c.1 c.2)
  have hchooseBlock :
      ∀ c : {c : Fin n // c ∈ retainedInactive C u},
        RetainedNeighbourBlocker C u c.1 (chooseBlocker c) := by
    intro c
    exact (retainedCode_eq_flipped_iff_blocker
      C u (chooseBlocker c) c.1).1 (hchooseCode c)
  let f :
      {c : Fin n // c ∈ retainedInactive C u} →
        {w : V // v < w} :=
    fun c => ⟨chooseBlocker c, by
      apply blocker_after_other_of_lower_inactive
        C huv hsame
      · intro hc
        exact c.2
          ((castSucc_mem_active_iff_mem_retainedActive
            C u c.1).1 hc)
      · exact hchooseBlock c⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    have hw : chooseBlocker c = chooseBlocker d :=
      congrArg Subtype.val hcd
    have hd' :
        RetainedNeighbourBlocker C u d.1 (chooseBlocker c) := by
      rw [hw]
      exact hchooseBlock d
    exact blocker_coordinate_unique
      C (hchooseBlock c) hd'
  refine ⟨f, hf, ?_⟩
  intro c x hx
  exact last_duplicate_blocker_code_unique
    C huv hsame hlast
    (by exact c.2)
    (hchooseBlock c)
    x
    (by simpa [f] using hx)


/-- Vertices to the right of v whose retained code is globally unique. -/
noncomputable def singletonRightVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset V := by
  classical
  exact (strictRightVertices v).filter fun w =>
    ∀ x : V, SameRetained C x w → x = w

@[simp] theorem mem_singletonRightVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v w : V) :
    w ∈ singletonRightVertices C v ↔
      v < w ∧
      ∀ x : V, SameRetained C x w → x = w := by
  classical
  simp [singletonRightVertices]

/-- To the right of the last duplicate upper endpoint, every vertex is a
singleton retained-code fibre. -/
theorem singletonRightVertices_eq_strictRight_of_last
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V}
    (hlast : ∀ z : V, v < z → ¬ HasEarlierSame C z) :
    singletonRightVertices C v = strictRightVertices v := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    exact (mem_strictRightVertices v w).2
      ((mem_singletonRightVertices C v w).1 hw).1
  · intro hw
    have hvw : v < w :=
      (mem_strictRightVertices v w).1 hw
    apply (mem_singletonRightVertices C v w).2
    refine ⟨hvw, ?_⟩
    intro x hx
    exact retained_code_unique_right_of_last_duplicate
      C hlast hvw hx

/-- Backward-augmentation dichotomy for the last duplicate fibre.

Either one inactive one-coordinate neighbour of the lower endpoint is a free
Boolean hole, or the exponent of the lower endpoint is paid by at least that
many distinct singleton retained-code fibres strictly to the right. -/
theorem last_duplicate_free_flip_or_many_singleton_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hlast : ∀ z : V, v < z → ¬ HasEarlierSame C z) :
    (∃ c : Fin n,
      c ∈ retainedInactive C u ∧
      ¬ ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c)
    ∨
    exponent u ≤ (singletonRightVertices C v).card := by
  classical
  by_cases hfree :
      ∃ c : Fin n,
        c ∈ retainedInactive C u ∧
        ¬ ∃ w : V,
          (fun d => retainedBit C w d) =
            flippedRetainedCode C u c
  · exact Or.inl hfree
  · right
    have hoccupied :
        ∀ c, c ∈ retainedInactive C u →
          ∃ w : V,
            (fun d => retainedBit C w d) =
              flippedRetainedCode C u c := by
      intro c hc
      by_contra hno
      exact hfree ⟨c, hc, hno⟩
    have hle :
        exponent u ≤ (strictRightVertices v).card :=
      duplicate_left_exponent_le_right_count_of_all_flips_occupied
        C exponent hexp honeLoss huv hsame hoccupied
    rw [singletonRightVertices_eq_strictRight_of_last
      C hlast]
    exact hle

#print axioms exists_last_duplicate_upper
#print axioms retained_code_unique_right_of_last_duplicate
#print axioms last_duplicate_blocker_code_unique
#print axioms last_duplicate_inactive_injects_singleton_right

end OrderedEdgeColoring
end JSP000404Research
