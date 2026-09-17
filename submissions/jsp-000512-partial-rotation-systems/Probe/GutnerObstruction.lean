import Probe.GutnerGraph

namespace JSP512Probe.Gutner

/-- The two-color triangle obstruction inside one of the local blocks. -/
private theorem triangle_obstruction (a b k p q x y z : ℕ)
    (hx : x ∈ ({a,k,p,q} : Finset ℕ))
    (hy : y ∈ ({a,b,p,q} : Finset ℕ))
    (hz : z ∈ ({b,k,p,q} : Finset ℕ))
    (hxa : a ≠ x) (hxk : k ≠ x) (hya : a ≠ y) (hyb : b ≠ y)
    (hzb : b ≠ z) (hzk : k ≠ z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : False := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy hz
  omega

/-- A block has no respecting coloring when its shared edge has the designated
ordered pair of colors. -/
theorem block_obstruction (i : Fin 12) (c : graph.Coloring ℕ)
    (hL : ListColoring.Respects graph lists c)
    (hu : c 0 = colorA i) (hv : c 1 = colorB i) : False := by
  have hm : ∀ r, c (vertex i r) ∈ localLists (colorA i) (colorB i) r := by
    intro r
    simpa only [lists_vertex] using hL (vertex i r)
  have h02 := c.valid (block_adj i 0 2 (by decide) (by decide))
  have h12 := c.valid (block_adj i 1 2 (by decide) (by decide))
  simp only [vertex_u,vertex_v,hu,hv] at h02 h12
  have hw := hm 2
  change c (vertex i 2) ∈ ({colorA i,colorB i,1,2} : Finset ℕ) at hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with hw | hw | hw | hw
  · exact h02 hw.symm
  · exact h12 hw.symm
  · apply triangle_obstruction (colorA i) (colorB i) 1 3 4
      (c (vertex i 3)) (c (vertex i 4)) (c (vertex i 5))
      (hm 3) (hm 4) (hm 5)
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 0 3 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 2 3 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 0 4 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 1 4 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 1 5 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 2 5 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 3 4 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 4 5 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 3 5 (by decide) (by decide))
  · apply triangle_obstruction (colorA i) (colorB i) 2 5 6
      (c (vertex i 6)) (c (vertex i 7)) (c (vertex i 8))
      (hm 6) (hm 7) (hm 8)
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 0 6 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 2 6 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 0 7 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 1 7 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 1 8 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 2 8 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 6 7 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 7 8 (by decide) (by decide))
    · simpa only [vertex_u,vertex_v,hu,hv,hw] using
        c.valid (block_adj i 6 8 (by decide) (by decide))

/-- Explicit four-element lists on 86 vertices have no proper respecting
coloring. Planarity is a separate obligation, not a hypothesis hidden here. -/
theorem no_list_coloring : ¬ ∃ c : graph.Coloring ℕ, ListColoring.Respects graph lists c := by
  rintro ⟨c,hc⟩
  have hu : c 0 ∈ ({7,8,9,10} : Finset ℕ) := hc 0
  have hv : c 1 ∈ ({7,8,9,10} : Finset ℕ) := hc 1
  have he : c 0 ≠ c 1 := c.valid (block_adj 0 0 1 (by decide) (by decide))
  obtain ⟨i,hi,hj⟩ := colors_cover hu hv he
  exact block_obstruction i c hc hi.symm hj.symm

end JSP512Probe.Gutner
