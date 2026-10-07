# CodingGap — a Lean 4 formalization

Formalization (Lean 4 + Mathlib) of the results of the paper *On the Completion Time of Broadcast*
(the statements are in Section "Our results", the proofs in Section "Main Proofs" and
the appendices).

The whole library builds with **no `sorry` and no axioms** beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`). The only unproved ingredient is the cited
integral terminal-path lemma of Chuzhoy–Parter–Tan (arXiv:2006.07486v1, Lemma 6.6; `lem:cpt` in
the paper), which appears as the explicit hypothesis `CPTTerminalPaths` of the routing upper bound.

## Building

```sh
# the toolchain is installed in ~/.elan
export PATH=$HOME/.elan/bin:$PATH
lake exe cache get   # download prebuilt Mathlib (only needed once)
lake build
```

`bash check.sh CodingGap/File.lean` compiles a single file and prints only errors (or `OK`).

## Layout

| File | Contents |
|------|----------|
| `CodingGap/Model.lean` | **All definitions** used by the main statements: time-expanded network `G[T]`, finite temporal cuts, `C_T(s,v)`, `τ(G,s,k)`; coding schemes (deterministic protocols) and `CODE(G,s,k)` (`codedTime`), `B`-bit alphabet `Bits B`; routing schedules, `ROUTE(G,s,k)` (`routingTime`) and the multi-source variant; edge-disjoint path families; the doubled multigraph `2G` and the path systems used by the halving hierarchy. |
| `CodingGap/Cited.lean` | Statement (as a `Prop`, not an axiom) of the cited Chuzhoy–Parter–Tan lemma (`lem:cpt`). |
| `CodingGap/MainTheorems.lean` | **All high-level results**, stated using only the model's definitions. |
| `LowerBound.lean` | `thm:lower` (cut-transcript counting argument). |
| `ActivationLabels.lean` | Finite temporal cuts ↔ activation labels (`eq:temporal-label-capacity`). |
| `Paths.lean`, `Potentials.lean`, `DartFlow.lean`, `FlowOverTime.lean` | Path families; Bellman–Ford potentials; unit flows and path decomposition; the discrete maximum flow over time (`eq:ff-cut-value` in path form). |
| `Benchmark.lean` | Consequences: monotonicity and finiteness of `τ`, `lem:short`. |
| `Doubling.lean` | `2G` is `(r, 2h)`-connected. |
| `Halving.lean`, `Hierarchy.lean` | `lem:halving` (via a maximum cut of the terminal-path multigraph), one level of the calendar, the hierarchy and `ROUTE ≤ 24 τ ⌈log₂ n⌉` (`thm:forwarding`). |
| `Pipeline.lean` | Basic facts on routing schedules; spanning-tree pipelines (some routing schedule always exists). |
| `Simulation.lean` | Routing schedules are coding schemes (`CODE ≤ ROUTE`). |
| `TemporalPaths.lean`, `LinearCode.lean`, `CodingProtocol.lean` | Temporal path systems, the greedy (Jaggi et al.) linear code on `G[T]`, and `CODE = τ` over a finite field `F` with `|F| ≥ n` (`thm:coded`). |
| `Alphabet.lean` | `CODE` depends only on the alphabet size; transfer to `B`-bit packets via `GaloisField 2 B`. |
| `ToyExample.lean` | The instance of Figure `fig:coding-example`: `τ = CODE = 2`, `ROUTE = 3`. |
| `MultiSource.lean` | Multi-source broadcast reduction for routing (`ROUTE` at most doubles). |
| `MaxFlow.lean` | Integral max-flow min-cut (augmenting paths) on a finite network. |
| `MultiSourceCoding.lean` | Multi-source broadcast reduction for coding (`CODE` at most doubles): the cut condition of the gathering network, its decomposition into packet trajectories, and the gather-then-broadcast scheme. |

## What is proved

| Paper (`sections/results.tex`) | Lean (`MainTheorems.lean`) |
|-------|----------------------------|
| `thm:lower` (Lower Bound) | `lower_bound`, `tau_le_codedTime` |
| `thm:forwarding` (Routing Upper Bound) | `routing_upper_bound` (assumes `CPTTerminalPaths`; `ROUTE ≤ 24 τ ⌈log₂ n⌉`) |
| `thm:coding gap`, `O(log n)` | `coding_gap_upper_bound` (`τ ≤ CODE ≤ ROUTE ≤ 24 ⌈log₂ n⌉ CODE`) |
| `thm:coding gap`, `≥ 3/2` | `coding_gap_lower_bound` (Figure `fig:coding-example`, every `B ≥ 1`) |
| `thm:coded` (Optimal Coded Broadcast) | `optimal_coded_broadcast` (needs `2^B ≥ n`), `coding_attains_tau`, `linear_code_exists` |
| Multi-Source Broadcast Reduction (routing) | `multi_source_reduction`, `multiSourceRoutingTime_le_two_mul` (factor 2) |
| Multi-Source Broadcast Reduction (coding) | `multi_source_reduction_coding`, `multiSourceCodedTime_le_two_mul` (factor 2) |
| `eq:ff-cut-value` (path form) | `max_flow_over_time`, `max_flow_over_time_short_paths` |
| `lem:short` | `short_disjoint_paths` |
| `2G` is `(r,2h)`-connected | `doubling_reduction` |
| `lem:halving` | `integral_halving_step` |
| `eq:hierarchy`, `eq:phase` | `rooted_short_path_broadcast` |
| `τ ≤ k + n - 2` | `tau_le_k_add_card` |
| `eq:temporal-label-capacity` | `activation_label_formula` |

## Modelling choices and deviations from the paper

* **Routing schemes are content-oblivious.** A routing schedule fixes in advance which packet (by
  index) is sent along which edge in which round; a channel may also be left unused. The paper
  defines a routing scheme only by "a vertex sends a packet only if it received it". Without
  obliviousness, the choice of *which* packet is sent (or whether one is sent) can depend on the
  packet values and encodes information. For example, with `B = 1` in the toy example, `c` can
  send `m₁` if `m₁ ≠ m₂` and stay silent otherwise. This content-dependent "routing" finishes in
  two rounds, so the proof of the `3/2` lower bound needs obliviousness. The paper's upper bounds
  construct oblivious schedules, so they are unaffected.
* **`thm:coded` needs a large alphabet.** It is proved for `B`-bit packets with `2^B ≥ n` (more
  generally, over any finite field with at least `n` elements), which is what the paper's proof
  uses. For small `B` the statement can fail.
* **Completion time.** A scheme is correct at time `T` if every vertex outputs the input at
  time `T`. This matches the paper's `T = max_v T_v`, because memory is unrestricted.
* **Cited result.** `lem:cpt` is the hypothesis `CPTTerminalPaths`, used only for the doubled
  graphs `2G`. Its paths are simple paths of the multigraph, i.e. paths of `G` with a choice of
  parallel copy per edge.
* **Ford–Fulkerson.** `eq:ff-cut-value` is proved directly for `G[T]` in path form
  (`C_T(s,v) = max ∑ᵢ (T + 1 - |Pᵢ|)` over edge-disjoint path families), not derived from the
  cited dynamic-flow theorem.
* **Multi-source reduction.** Both versions are formalized. For routing, the gathering paths are
  read off the given schedule: trace each packet backwards from its owner, then reverse time. For
  coding, the appendix's flow argument is used, with the time reversal applied to cuts: the
  gathering network (`G[T]` with storage arcs of capacity `k` and a super-source joined to the
  initial owners) has all cuts of capacity at least `k`, an integral maximum flow
  (`MaxFlow.exists_flow`) is split time layer by time layer into packet trajectories, and the
  packets are forwarded along them before the given coding scheme is run. A multi-source coding
  scheme (`MultiProtocol`) differs from `Protocol` only in its initial states: each vertex starts
  from the packets it holds.
* **Logarithms** are `Nat.clog 2 n = ⌈log₂ n⌉`.

## Not formalized

* Polynomial-time computability (running times are not modelled).
* The equivalence of temporal and moving cuts (`lem:temporal-moving`); its main ingredient
  `eq:temporal-label-capacity` is proved.
