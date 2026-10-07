import CodingGap.Model

/-!
# Cited results

Results of other papers that the routing upper bound relies on. They are *not* proved here: they
are stated as propositions and appear as explicit hypotheses of the theorems that use them.
-/

namespace CodingGap

universe u

/-- **Chuzhoy–Parter–Tan [CPT20, Lemma 6.6] (`lem:cpt` in the paper), for doubled graphs.**
Let `H` be an `(r,d)`-connected multigraph, `U ⊊ V(H)` and `s ∉ U`. There is a set of paths, each joining two distinct vertices of
`U ∪ {s}`, such that every `u ∈ U` is an endpoint of at least `r` paths, every path has length at
most `2d`, and every edge of `H` lies on at most two paths. (Section 6 of the cited paper allows
parallel edges; its paths are simple.) Only the case `H = 2G` is used. -/
def CPTTerminalPaths : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r d : ℕ) (U : Finset V) (s : V),
    s ∉ U → DoubledConnected G r d → Nonempty (DoubledTerminalPaths G s U r (2 * d))

end CodingGap
