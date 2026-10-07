import CodingGap.Paths

/-!
# Rooted connectivity becomes pairwise connectivity in `2G` (Section `sec:paths`)

If every `v ≠ s` has `r` edge-disjoint `s`–`v` paths of length at most `h`, then `2G` is
`(r, 2h)`-connected: for `u, w ≠ s`, the `i`-th `s`–`u` path reversed and followed by the `i`-th
`s`–`w` path is a `u`–`w` walk of length at most `2h`; shortcutting it gives a path. Every edge of
`G` lies on at most one path of each rooted family, hence on at most two of the resulting paths,
which can use the two different parallel copies of the edge.
-/

namespace CodingGap

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Doubling reduction:** `2G` is `(r, 2h)`-connected. -/
theorem doubledConnected_of_rooted {s : V} {r h : ℕ}
    (hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ h) :
    DoubledConnected G r (2 * h) := by
  intro u w huw
  by_cases hu : u = s
  · subst hu
    obtain ⟨P, hlen⟩ := hP w (Ne.symm huw)
    exact ⟨⟨P.path, P.isPath, fun i => (hlen i).trans (by omega), fun _ _ => 0,
      fun i j hij e he he' _ => P.disjoint hij he he'⟩⟩
  by_cases hw : w = s
  · subst hw
    obtain ⟨P, hlen⟩ := hP u hu
    refine ⟨⟨fun i => (P.path i).reverse, fun i => (P.isPath i).reverse,
      fun i => by rw [SimpleGraph.Walk.length_reverse]; exact (hlen i).trans (by omega),
      fun _ _ => 0, fun i j hij e he he' _ => ?_⟩⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he he'
    exact P.disjoint hij he he'
  obtain ⟨Pu, hlu⟩ := hP u hu
  obtain ⟨Pw, hlw⟩ := hP w hw
  let W : Fin r → G.Walk u w := fun i => ((Pu.path i).reverse.append (Pw.path i)).bypass
  have hWedges : ∀ i, ∀ e ∈ (W i).edges, e ∈ (Pu.path i).edges ∨ e ∈ (Pw.path i).edges := by
    intro i e he
    have := SimpleGraph.Walk.edges_bypass_subset_edges _ he
    rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at this
    exact this
  refine ⟨⟨W, fun i => SimpleGraph.Walk.bypass_isPath _, fun i => ?_,
    fun i e => if e ∈ (Pu.path i).edges then 0 else 1, fun i j hij e he he' hc => ?_⟩⟩
  · refine (SimpleGraph.Walk.length_bypass_le_length _).trans ?_
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    have := hlu i; have := hlw i; omega
  · by_cases hi : e ∈ (Pu.path i).edges
    · have hj : e ∈ (Pu.path j).edges := by
        by_contra hj; simp [hi, hj] at hc
      exact Pu.disjoint hij hi hj
    · have hj : e ∉ (Pu.path j).edges := by
        intro hj; simp [hi, hj] at hc
      exact Pw.disjoint hij ((hWedges i e he).resolve_left hi) ((hWedges j e he').resolve_left hj)

end CodingGap
