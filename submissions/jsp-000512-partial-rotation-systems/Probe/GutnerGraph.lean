import Probe.ListColorExtension
import Mathlib.Tactic.FinCases

/-!
The 86-vertex intermediate construction H in Section 2 of Shai Gutner,
"The complexity of planar graph choosability", arXiv:0802.2668.
This module defines only the finite graph and its four-element lists.
No planarity or zero-genus property is presumed by the definition.
-/
namespace JSP512Probe.Gutner

/-- Local names: u,v,w,x1,x2,x3,y1,y2,y3. -/
def blockEdges : Finset (Fin 9 × Fin 9) :=
  {(0,1),(0,2),(1,2),
   (0,3),(2,3),(0,4),(1,4),(1,5),(2,5),(3,4),(4,5),(3,5),
   (0,6),(2,6),(0,7),(1,7),(1,8),(2,8),(6,7),(7,8),(6,8)}

/-- The two roots are shared; the other seven vertices are disjoint. -/
def vertex (i : Fin 12) (r : Fin 9) : Fin 86 :=
  ⟨if r.val < 2 then r.val else 7 * i.val + r.val, by split_ifs <;> omega⟩

theorem vertex_injective (i : Fin 12) : Function.Injective (vertex i) := by
  intro a b h
  have he := congrArg Fin.val h
  simp only [vertex] at he
  apply Fin.ext
  split_ifs at he <;> omega

@[simp] theorem vertex_u (i : Fin 12) : vertex i 0 = 0 := rfl
@[simp] theorem vertex_v (i : Fin 12) : vertex i 1 = 1 := rfl

/-- Twelve copies of the nine-vertex block, identified at u and v. -/
def graph : SimpleGraph (Fin 86) where
  Adj x y := x ≠ y ∧ ∃ i : Fin 12, ∃ a b : Fin 9, (a,b) ∈ blockEdges ∧
    ((x = vertex i a ∧ y = vertex i b) ∨ (x = vertex i b ∧ y = vertex i a))
  symm.symm x y h := by
    obtain ⟨hne,i,a,b,he,hxy⟩ := h
    refine ⟨hne.symm,i,a,b,he,?_⟩
    exact hxy.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)
  loopless.irrefl x h := h.1 rfl

instance : DecidableRel graph.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ∃ i : Fin 12, ∃ a b : Fin 9, (a,b) ∈ blockEdges ∧
    ((x = vertex i a ∧ y = vertex i b) ∨ (x = vertex i b ∧ y = vertex i a))))

theorem block_adj (i : Fin 12) (a b : Fin 9) (hne : a ≠ b)
    (he : (a,b) ∈ blockEdges) : graph.Adj (vertex i a) (vertex i b) :=
  ⟨fun h => hne (vertex_injective i h),i,a,b,he,Or.inl ⟨rfl,rfl⟩⟩

def colorA (i : Fin 12) : ℕ := 7 + i.val / 3

def colorB (i : Fin 12) : ℕ :=
  7 + if i.val % 3 < i.val / 3 then i.val % 3 else i.val % 3 + 1

/-- Each possible proper coloring of the common edge has a dedicated block. -/
theorem colors_cover {a b : ℕ} (ha : a ∈ ({7,8,9,10} : Finset ℕ))
    (hb : b ∈ ({7,8,9,10} : Finset ℕ)) (hne : a ≠ b) :
    ∃ i : Fin 12, colorA i = a ∧ colorB i = b := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    first | contradiction | exact ⟨0,by decide⟩ | exact ⟨1,by decide⟩ |
      exact ⟨2,by decide⟩ | exact ⟨3,by decide⟩ | exact ⟨4,by decide⟩ |
      exact ⟨5,by decide⟩ | exact ⟨6,by decide⟩ | exact ⟨7,by decide⟩ |
      exact ⟨8,by decide⟩ | exact ⟨9,by decide⟩ | exact ⟨10,by decide⟩ |
      exact ⟨11,by decide⟩

def localLists (a b : ℕ) (r : Fin 9) : Finset ℕ :=
  match r.val with
  | 0 => {7,8,9,10}
  | 1 => {7,8,9,10}
  | 2 => {a,b,1,2}
  | 3 => {a,1,3,4}
  | 4 => {a,b,3,4}
  | 5 => {b,1,3,4}
  | 6 => {a,2,5,6}
  | 7 => {a,b,5,6}
  | _ => {b,2,5,6}

def lists (x : Fin 86) : Finset ℕ :=
  if hx : x.val < 2 then {7,8,9,10}
  else
    let i : Fin 12 := ⟨(x.val-2)/7,by omega⟩
    let r : Fin 9 := ⟨2+(x.val-2)%7,by omega⟩
    localLists (colorA i) (colorB i) r

theorem lists_vertex (i : Fin 12) (r : Fin 9) :
    lists (vertex i r) = localLists (colorA i) (colorB i) r := by
  fin_cases i <;> fin_cases r <;> decide

theorem lists_card (x : Fin 86) : (lists x).card = 4 := by
  fin_cases x <;> decide

end JSP512Probe.Gutner
