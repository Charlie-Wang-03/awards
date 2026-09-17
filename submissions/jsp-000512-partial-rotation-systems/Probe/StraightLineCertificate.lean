import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace JSP512Probe.StraightLine

/-- Exact integer orientation of three points. -/
def orient (a b c : ℤ × ℤ) : ℤ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

/-- The actual real straight segment parameterization. -/
def mix (a b : ℤ × ℤ) (t : ℝ) : ℝ × ℝ :=
  ((1-t)*(a.1:ℝ)+t*(b.1:ℝ),(1-t)*(a.2:ℝ)+t*(b.2:ℝ))

/-- Equal points on two segment parameterizations obey the determinant equation. -/
theorem mix_line (a b c d : ℤ × ℤ) (t s : ℝ) (h : mix a b t = mix c d s) :
    (1-t)*(orient c d a : ℝ)+t*(orient c d b : ℝ) = 0 := by
  calc
    _ = ((d.1:ℝ)-c.1)*((mix a b t).2-c.2) -
        ((d.2:ℝ)-c.2)*((mix a b t).1-c.1) := by
      simp only [orient,mix,Int.cast_sub,Int.cast_mul]
      ring
    _ = ((d.1:ℝ)-c.1)*((mix c d s).2-c.2) -
        ((d.2:ℝ)-c.2)*((mix c d s).1-c.1) := by rw [h]
    _ = 0 := by simp only [mix]; ring

/-- A convex combination of two real numbers of the same strict sign is nonzero. -/
theorem convex_nonzero (a b t : ℝ) (h : 0 < a*b) (ht : 0 ≤ t ∧ t ≤ 1) :
    (1-t)*a+t*b ≠ 0 := by
  intro hz
  rcases mul_pos_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · by_cases he : t = 1
    · simp only [he,sub_self,zero_mul,one_mul,zero_add] at hz
      linarith
    · have hlt : t < 1 := (lt_or_eq_of_le ht.2).resolve_right he
      have hp := mul_pos (by linarith : 0 < 1-t) ha
      have hq := mul_nonneg ht.1 (le_of_lt hb)
      linarith
  · by_cases he : t = 1
    · simp only [he,sub_self,zero_mul,one_mul,zero_add] at hz
      linarith
    · have hlt : t < 1 := (lt_or_eq_of_le ht.2).resolve_right he
      have hp := mul_neg_of_pos_of_neg (by linarith : 0 < 1-t) ha
      have hq := mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_lt hb)
      linarith

/-- Integer side tests sufficient to separate the open first edge from the
closed second edge. The middle alternatives handle shared endpoints. -/
def Separated (a b c d : ℤ × ℤ) : Prop :=
  0 < orient c d a * orient c d b ∨
  (orient c d a = 0 ∧ orient c d b ≠ 0) ∨
  (orient c d b = 0 ∧ orient c d a ≠ 0) ∨
  0 < orient a b c * orient a b d

instance (a b c d : ℤ × ℤ) : Decidable (Separated a b c d) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem separated_segments (a b c d : ℤ × ℤ) (h : Separated a b c d)
    (t s : ℝ) (ht : 0 < t ∧ t < 1) (hs : 0 ≤ s ∧ s ≤ 1) :
    mix a b t ≠ mix c d s := by
  intro he
  have hz := mix_line a b c d t s he
  rcases h with h | ⟨h0,hn⟩ | ⟨h0,hn⟩ | h
  · exact convex_nonzero _ _ t (by exact_mod_cast h) ⟨le_of_lt ht.1,le_of_lt ht.2⟩ hz
  · have h0' : (orient c d a : ℝ) = 0 := by exact_mod_cast h0
    have hn' : (orient c d b : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [h0',mul_zero,zero_add] at hz
    exact (mul_ne_zero (ne_of_gt ht.1) hn') hz
  · have h0' : (orient c d b : ℝ) = 0 := by exact_mod_cast h0
    have hn' : (orient c d a : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [h0',mul_zero,add_zero] at hz
    exact (mul_ne_zero (by linarith) hn') hz
  · exact convex_nonzero _ _ s (by exact_mod_cast h) hs (mix_line c d a b s t he.symm)

/-- A concrete noncrossing straight-line drawing in the real plane. Vertices
are distinct, no unrelated vertex lies on an edge, and interiors of distinct
undirected edges do not meet another edge even at its endpoints. -/
structure Drawing {V : Type*} (G : SimpleGraph V) where
  pos : V → ℤ × ℤ
  injective : Function.Injective pos
  vertex_avoids : ∀ a b v, G.Adj a b → v ≠ a → v ≠ b →
    ∀ t : ℝ, mix (pos a) (pos b) t ≠ (((pos v).1:ℝ),((pos v).2:ℝ))
  edge_avoids : ∀ a b c d, G.Adj a b → G.Adj c d →
    ¬ (a = c ∧ b = d) → ¬ (a = d ∧ b = c) →
    ∀ t s : ℝ, 0 < t ∧ t < 1 → 0 ≤ s ∧ s ≤ 1 →
      mix (pos a) (pos b) t ≠ mix (pos c) (pos d) s

/-- Finite integer tests produce an actual drawing, not an assumed embedding. -/
def drawingOfChecks {V : Type*} (G : SimpleGraph V) (p : V → ℤ × ℤ)
    (hinj : Function.Injective p)
    (hv : ∀ a b v, G.Adj a b → v ≠ a → v ≠ b → orient (p a) (p b) (p v) ≠ 0)
    (he : ∀ a b c d, G.Adj a b → G.Adj c d →
      ¬ (a = c ∧ b = d) → ¬ (a = d ∧ b = c) →
      Separated (p a) (p b) (p c) (p d)) : Drawing G where
  pos := p
  injective := hinj
  vertex_avoids a b v hab hva hvb t h := by
    have heq : mix (p v) (p v) 0 = mix (p a) (p b) t := by
      simpa [mix] using h.symm
    have hz := mix_line (p v) (p v) (p a) (p b) 0 t heq
    have hn : (orient (p a) (p b) (p v) : ℝ) ≠ 0 := by
      exact_mod_cast hv a b v hab hva hvb
    apply hn
    simpa using hz
  edge_avoids a b c d hab hcd h1 h2 t s ht hs :=
    separated_segments _ _ _ _ (he a b c d hab hcd h1 h2) t s ht hs

theorem orient_reverse (a b c : ℤ × ℤ) : orient b a c = -orient a b c := by
  simp only [orient]
  ring

theorem separated_reverse_left (a b c d : ℤ × ℤ) (h : Separated a b c d) :
    Separated b a c d := by
  rcases h with h | ⟨h1,h2⟩ | ⟨h1,h2⟩ | h
  · exact Or.inl (by simpa only [mul_comm] using h)
  · exact Or.inr (Or.inr (Or.inl ⟨h1,h2⟩))
  · exact Or.inr (Or.inl ⟨h1,h2⟩)
  · right; right; right
    simpa only [orient_reverse a b c,orient_reverse a b d,neg_mul_neg] using h

theorem separated_reverse_right (a b c d : ℤ × ℤ) (h : Separated a b c d) :
    Separated a b d c := by
  rcases h with h | ⟨h1,h2⟩ | ⟨h1,h2⟩ | h
  · left
    simpa only [orient_reverse c d a,orient_reverse c d b,neg_mul_neg] using h
  · right; left
    simpa only [orient_reverse c d a,orient_reverse c d b,neg_eq_zero,neg_ne_zero] using And.intro h1 h2
  · right; right; left
    simpa only [orient_reverse c d a,orient_reverse c d b,neg_eq_zero,neg_ne_zero] using And.intro h1 h2
  · exact Or.inr (Or.inr (Or.inr (by simpa only [mul_comm] using h)))

end JSP512Probe.StraightLine
