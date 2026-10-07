import CodingGap.Alphabet
import CodingGap.Hierarchy
import CodingGap.ToyExample
import CodingGap.MultiSource
import CodingGap.MultiSourceCoding

/-!
# Main theorems

The results of Section "Our results" of the paper, together with the
main lemmas of their proofs, stated in terms of the definitions of `CodingGap.Model` only. Each
statement is proved by referring to the file that contains the actual argument. Paper labels are
the LaTeX labels.

| Paper                                         | Here                                  | Proof in        |
|-----------------------------------------------|---------------------------------------|-----------------|
| `thm:lower` (Lower Bound)                     | `lower_bound`, `tau_le_codedTime`     | `LowerBound`    |
| `thm:forwarding` (Routing Upper Bound)        | `routing_upper_bound`                 | `Hierarchy`     |
| `thm:coding gap` (Coding Gap), upper bound    | `coding_gap_upper_bound`              | all of the above|
| `thm:coding gap`, lower bound `3/2`           | `coding_gap_lower_bound`              | `ToyExample`    |
| `thm:coded` (Optimal Coded Broadcast)         | `optimal_coded_broadcast`, `linear_code_exists` | `CodingProtocol`, `Alphabet` |
| Multi-Source Broadcast Reduction (routing)    | `multi_source_reduction`              | `MultiSource`   |
| Multi-Source Broadcast Reduction (coding)     | `multi_source_reduction_coding`       | `MultiSourceCoding`, `MaxFlow` |
| `eq:ff-cut-value` (via `thm:ff`)              | `max_flow_over_time`, `…_short_paths` | `FlowOverTime`  |
| `lem:short` (Short-path certificate)          | `short_disjoint_paths`                | `Benchmark`     |
| `2G` is `(r, 2h)`-connected (`sec:paths`)     | `doubling_reduction`                  | `Doubling`      |
| `lem:halving` (Root-preserving halving)       | `integral_halving_step`               | `Halving`       |
| hierarchy `eq:hierarchy` and levels           | `rooted_short_path_broadcast`         | `Hierarchy`     |
| `τ ≤ k + n - 2` (used for the binary search)  | `tau_le_k_add_card`                   | `Benchmark`     |
| `CODE ≤ ROUTE`                                | `codedTime_le_routingTime'`           | `Simulation`    |
| `eq:temporal-label-capacity` (`app:moving-cut`) | `activation_label_formula`          | `ActivationLabels` |

The routing upper bound uses the integral terminal-path lemma of Chuzhoy, Parter and Tan
(`lem:cpt`), which is not formalized; it is the explicit hypothesis `CPTTerminalPaths`
(see `CodingGap.Cited`).

Packets and messages are `B`-bit strings (`Bits B`, with `B ≥ 1`); several statements are also
given for an arbitrary finite alphabet or finite field.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Theorem `thm:lower` (Lower Bound) -/

/-- **Theorem `thm:lower`.** Over any alphabet with at least two symbols (e.g. `Bits B`, `B ≥ 1`),
every correct coding scheme that completes broadcast by time `T` has `T ≥ τ(G,s,k)`. -/
theorem lower_bound {A : Type} [Fintype A] (hA : 2 ≤ Fintype.card A) {k : ℕ}
    (P : Protocol V A k) {s : V} {T : ℕ} (h : ∀ X, P.Broadcasts G s X T) : tau G s k ≤ T :=
  tau_le_of_broadcasts G hA P h

/-- **Theorem `thm:lower`, `CODE ≥ τ`**, for a connected graph and `B`-bit packets. -/
theorem tau_le_codedTime {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (s : V) (k : ℕ) {B : ℕ} (hB : 1 ≤ B) :
    tau G s k ≤ codedTime G s (Bits B) k :=
  tau_le_codedTime_of_connected hG s k (two_le_card_bits hB)

/-! ## Theorem `thm:forwarding` (Routing Upper Bound) -/

universe u in
/-- **Theorem `thm:forwarding`.** Assume the integral terminal-path lemma of Chuzhoy–Parter–Tan
(`lem:cpt`). For every connected graph on `n ≥ 2` vertices, source `s` and `k ≥ 1` packets,
`ROUTE(G,s,k) ≤ 24 τ(G,s,k) ⌈log₂ n⌉`. -/
theorem routing_upper_bound {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcpt : CPTTerminalPaths.{u}) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (s : V) {k : ℕ} (hk : 1 ≤ k) :
    routingTime G s k ≤ 24 * tau G s k * Nat.clog 2 (Fintype.card V) :=
  routingTime_le_log hcpt hG hn s hk

/-! ## Theorem `thm:coding gap` (Coding Gap) -/

/-- **Theorem `thm:coding gap`, upper bound.** Assume `lem:cpt`. For every connected graph on
`n ≥ 2` vertices, source `s`, `k ≥ 1` packets of `B ≥ 1` bits,
`τ ≤ CODE ≤ ROUTE ≤ 24 ⌈log₂ n⌉ · CODE`, so the coding gap `ROUTE / CODE` is `O(log n)`. -/
theorem coding_gap_upper_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcpt : CPTTerminalPaths.{0}) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (s : V) {k : ℕ} (hk : 1 ≤ k) {B : ℕ} (hB : 1 ≤ B) :
    tau G s k ≤ codedTime G s (Bits B) k ∧ codedTime G s (Bits B) k ≤ routingTime G s k ∧
      routingTime G s k ≤ 24 * Nat.clog 2 (Fintype.card V) * codedTime G s (Bits B) k := by
  have h1 := tau_le_codedTime G hG s k hB
  refine ⟨h1, codedTime_le_routingTime _ (exists_routingSchedule hG s k), ?_⟩
  calc routingTime G s k ≤ 24 * tau G s k * Nat.clog 2 (Fintype.card V) :=
        routingTime_le_log hcpt hG hn s hk
    _ ≤ 24 * codedTime G s (Bits B) k * Nat.clog 2 (Fintype.card V) := by gcongr
    _ = _ := by ring

/-- **Theorem `thm:coding gap`, lower bound.** On the instance of Figure `fig:coding-example`
(`k = 2` packets of `B ≥ 1` bits), `τ = CODE = 2` while `ROUTE = 3`: a coding gap of `3/2`. -/
theorem coding_gap_lower_bound {B : ℕ} (hB : 1 ≤ B) :
    tau ToyExample.graph ToyExample.s 2 = 2 ∧
      codedTime ToyExample.graph ToyExample.s (Bits B) 2 = 2 ∧
      routingTime ToyExample.graph ToyExample.s 2 = 3 := by
  have : Fintype (GaloisField 2 B) := Fintype.ofFinite _
  refine ⟨(ToyExample.codedTime_eq (F := GaloisField 2 B)).2, ?_, ToyExample.routingTime_eq⟩
  rw [codedTime_congr (bitsEquivGaloisField (by omega : B ≠ 0))]
  exact (ToyExample.codedTime_eq (F := GaloisField 2 B)).1

/-! ## Theorem `thm:coded` (Optimal Coded Broadcast) -/

/-- **Theorem `thm:coded`.** For every connected graph on `n` vertices, `k ≥ 1` packets of `B ≥ 1`
bits with `2 ^ B ≥ n`, some correct coding scheme completes broadcast in exactly `τ(G,s,k)`
rounds, and none is faster: `CODE(G,s,k) = τ(G,s,k)`. (The scheme is the linear code of
`linear_code_exists`.) The paper states this for every instance; the proof needs `2 ^ B ≥ n`. -/
theorem optimal_coded_broadcast {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (s : V) {k : ℕ} (hk : 1 ≤ k) {B : ℕ} (hB : 1 ≤ B)
    (hn : Fintype.card V ≤ 2 ^ B) :
    (∃ P : Protocol V (Bits B) k, ∀ X, P.Broadcasts G s X (tau G s k)) ∧
      codedTime G s (Bits B) k = tau G s k := by
  have heq := codedTime_bits_eq_tau hG s hk hB hn
  refine ⟨?_, heq⟩
  rw [← heq]
  refine Nat.sInf_mem (s := {T | ∃ P : Protocol V (Bits B) k, ∀ X, P.Broadcasts G s X T}) ?_
  have : Nonempty (Bits B) := ⟨fun _ => false⟩
  obtain ⟨R, σ, hv, hc⟩ := exists_routingSchedule hG s k
  exact ⟨R, σ.toProtocol _, σ.broadcasts_toProtocol hv hc⟩

/-- **Theorem `thm:coded`, over a finite field `F` with `|F| ≥ n`:** `CODE(G,s,k) = τ(G,s,k)`. -/
theorem coding_attains_tau {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (s : V) {k : ℕ} (hk : 1 ≤ k) (F : Type) [Field F]
    [Fintype F] [DecidableEq F] (hF : Fintype.card V ≤ Fintype.card F) :
    codedTime G s F k = tau G s k :=
  codedTime_eq_tau hG hF hk

/-- **The linear code of `thm:coded`** (Jaggi et al. applied to `G[T]`). Over a finite field with
`|F| ≥ n`, if every receiver `v ≠ s` has `C_T(s,v) ≥ k`, there is a linear code on the
communication arcs of `G[T]` — every arc vector lies in the span of what its sender knows — after
which every vertex knows all of `F^k` at time `T`. -/
theorem linear_code_exists {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card V ≤ Fintype.card F) (s : V) {T k : ℕ}
    (hT : ∀ v, v ≠ s → k ≤ temporalMinCut G s v T) :
    ∃ g : Code V F k, IsValidCode G s T g ∧ ∀ v, knowledge G s g v T = ⊤ :=
  exists_code (fun v => Classical.choice (exists_temporalPathSystem v.2 (hT v v.2))) hF

/-! ## Multi-Source Broadcast Reduction -/

/-- **Multi-Source Broadcast Reduction** (routing). If a routing schedule broadcasts `k` packets
from `s` within `T` rounds, then for every placement `src : Fin k → V` of the packets (packet `i`
initially held only by `src i`) some routing schedule broadcasts them within `2 T` rounds. In
particular `ROUTE(G, src, k) ≤ 2 ROUTE(G, s, k)` in a connected graph. -/
theorem multi_source_reduction {s : V} {k T : ℕ} {σ : RoutingSchedule V k}
    (hv : σ.IsValid G s T) (hc : σ.Completes G s T) (src : Fin k → V) :
    ∃ σ' : RoutingSchedule V k, σ'.IsValidFrom G src (2 * T) ∧ σ'.CompletesFrom G src (2 * T) :=
  exists_multiSource_schedule hv hc src

/-- **Multi-Source Broadcast Reduction**, as a bound on routing times. -/
theorem multiSourceRoutingTime_le_two_mul (hG : G.Connected) (s : V) {k : ℕ} (src : Fin k → V) :
    multiSourceRoutingTime G src ≤ 2 * routingTime G s k :=
  CodingGap.multiSourceRoutingTime_le hG s src

/-- **Multi-Source Broadcast Reduction** (coding). Over an alphabet with at least two symbols (e.g.
`Bits B`, `B ≥ 1`), if a coding scheme broadcasts `k` packets from `s` within `T` rounds, then for
every placement `src : Fin k → V` of the packets (packet `i` initially held only by `src i`) some
coding scheme broadcasts them within `2 T` rounds. -/
theorem multi_source_reduction_coding {A : Type} [Fintype A] (hA : 2 ≤ Fintype.card A) {k : ℕ}
    (P : Protocol V A k) {s : V} {T : ℕ} (hP : ∀ X, P.Broadcasts G s X T) (src : Fin k → V) :
    ∃ Q : MultiProtocol V A k, ∀ X, Q.Broadcasts G src X (2 * T) :=
  exists_multiSource_protocol G hA P hP src

/-- **Multi-Source Broadcast Reduction** (coding), as a bound on coded times for `B`-bit packets:
`CODE(G, src, k) ≤ 2 CODE(G, s, k)` in a connected graph. -/
theorem multiSourceCodedTime_le_two_mul (hG : G.Connected) (s : V) {k : ℕ} (src : Fin k → V)
    {B : ℕ} (hB : 1 ≤ B) :
    multiSourceCodedTime G src (Bits B) ≤ 2 * codedTime G s (Bits B) k :=
  multiSourceCodedTime_le G hG s src (two_le_card_bits hB)

/-! ## Main lemmas of the proofs -/

/-- **Equation `eq:ff-cut-value`, in path form** (Ford–Fulkerson's dynamic-flow theorem for
`G[T]`, proved here directly). For `v ≠ s`, `C_T(s,v)` is the maximum, over families of
edge-disjoint `s`–`v` paths `P₁, …, P_q`, of `∑ᵢ (T + 1 - |Pᵢ|)`. -/
theorem max_flow_over_time {s v : V} (hv : v ≠ s) (T : ℕ) :
    (∀ (q : ℕ) (P : DisjointPaths G s v q),
      (q : ℤ) * (T + 1) - P.totalLength ≤ temporalMinCut G s v T) ∧
    ∃ (q : ℕ) (P : DisjointPaths G s v q),
      (q : ℤ) * (T + 1) - P.totalLength = temporalMinCut G s v T :=
  ⟨fun _ P => value_le_temporalMinCut hv T P, exists_value_eq_temporalMinCut hv T⟩

/-- The maximum in `max_flow_over_time` is attained by edge-disjoint `s`–`v` paths of length at
most `T` each. -/
theorem max_flow_over_time_short_paths {s v : V} (hv : v ≠ s) (T : ℕ) :
    ∃ (q : ℕ) (P : DisjointPaths G s v q),
      (q : ℤ) * (T + 1) - P.totalLength = temporalMinCut G s v T ∧
      ∀ i, (P.path i).length ≤ T :=
  exists_value_eq_temporalMinCut_short hv T

/-- **Lemma `lem:short` (Short-path certificate).** If `T ≥ 1` and `C_T(s,v) ≥ k`, then `G`
contains `⌈k / T⌉` edge-disjoint `s`–`v` paths, each of length at most `min T (n - 1)`. -/
theorem short_disjoint_paths {s v : V} (hv : v ≠ s) {T k : ℕ} (hT : 1 ≤ T)
    (hk : k ≤ temporalMinCut G s v T) :
    ∃ P : DisjointPaths G s v ⌈(k : ℚ) / T⌉₊,
      ∀ i, (P.path i).length ≤ min T (Fintype.card V - 1) :=
  exists_short_disjointPaths hv hT hk

/-- **The doubled graph is `(r, 2h)`-connected** (Section `sec:paths`). If every `v ≠ s` has `r`
edge-disjoint `s`–`v` paths of length at most `h`, then `2G` is `(r, 2h)`-connected. -/
theorem doubling_reduction {s : V} {r h : ℕ}
    (hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ h) :
    DoubledConnected G r (2 * h) :=
  doubledConnected_of_rooted hP

universe u in
/-- **Lemma `lem:halving` (Root-preserving halving).** Assume `lem:cpt`. If every `v ≠ s` has
`r ≥ 1` edge-disjoint `s`–`v` paths of length at most `h`, then every `S ∋ s` with `|S| ≥ 2`
contains `A ⊊ S` with `s ∈ A`, `|A| ≤ ⌈|S|/2⌉`, such that every `v ∈ S \ A` receives `⌈r/2⌉`
paths from `A` of length at most `4h`, every edge lying on at most four of them. -/
theorem integral_halving_step {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hcpt : CPTTerminalPaths.{u}) {s : V} {r h : ℕ} (hr : 1 ≤ r)
    (hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ h)
    {S : Finset V} (hs : s ∈ S) (hS : 2 ≤ S.card) :
    ∃ A : Finset V, A ⊆ S ∧ A ≠ S ∧ s ∈ A ∧ 2 * A.card ≤ S.card + 1 ∧
      Nonempty (LevelPaths G A (S \ A) ((r + 1) / 2) (4 * h) 4) :=
  exists_halving hcpt hr hP hs hS

universe u in
/-- **The halving hierarchy, executed level by level** (`eq:hierarchy`, `eq:phase`). Assume
`lem:cpt`. If every `v ≠ s` has `r ≥ 1` edge-disjoint `s`–`v` paths of length at most `h`, then
`ROUTE(G,s,k) ≤ 4 (4h + ⌈k/⌈r/2⌉⌉ - 1) ⌈log₂ n⌉`. -/
theorem rooted_short_path_broadcast {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcpt : CPTTerminalPaths.{u}) {s : V} {r h : ℕ}
    (hr : 1 ≤ r) (hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ h)
    (k : ℕ) :
    routingTime G s k ≤
      4 * (4 * h + ⌈(k : ℚ) / ((r + 1) / 2 : ℕ)⌉₊ - 1) * Nat.clog 2 (Fintype.card V) := by
  obtain ⟨σ, R, hR, hv, hk⟩ := exists_schedule_hierarchy hcpt hr hP k Finset.univ
    (Finset.mem_univ s)
  rw [Finset.card_univ] at hR
  have hmem : R ∈ {R | ∃ σ : RoutingSchedule V k, σ.IsValid G s R ∧ σ.Completes G s R} :=
    ⟨σ, hv, fun v m => hk v (Finset.mem_univ v) m⟩
  exact (Nat.sInf_le hmem).trans hR

/-- The benchmark is finite: `τ(G,s,k) ≤ k + n - 2` in a connected graph. -/
theorem tau_le_k_add_card (hG : G.Connected) (s : V) {k : ℕ} (hk : 1 ≤ k) :
    tau G s k ≤ k + (Fintype.card V - 1) - 1 :=
  tau_le_card hG hk

/-- **`CODE ≤ ROUTE`.** In a connected graph, a routing schedule is a special coding scheme. -/
theorem codedTime_le_routingTime' (hG : G.Connected) (s : V) (k : ℕ) (A : Type) [Nonempty A] :
    codedTime G s A k ≤ routingTime G s k :=
  codedTime_le_routingTime A (exists_routingSchedule hG s k)

/-- **Equation `eq:temporal-label-capacity`** (used for the equivalence of temporal and moving
cuts, Appendix `app:moving-cut`). Finite temporal cuts correspond to activation labels `a` with
`a s = 0`, `a v = T + 1`, `a ≤ T + 1`, and
`C_T(s,v) = min_a ∑_{(u,w) adjacent} [a w - a u - 1]₊`. -/
theorem activation_label_formula (s v : V) (T : ℕ) :
    temporalMinCut G s v T = sInf {c | ∃ a : V → ℕ, (a s = 0 ∧ a v = T + 1 ∧ ∀ u, a u ≤ T + 1) ∧
      ∑ p ∈ (univ ×ˢ univ).filter (fun p : V × V => G.Adj p.1 p.2), (a p.2 - (a p.1 + 1)) = c} := by
  rw [temporalMinCut_eq_sInf_labelCost]
  congr 1
  ext c
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ⟨ha.1, ha.2, ha.3⟩, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ⟨ha.1, ha.2.1, ha.2.2⟩, h⟩⟩

end CodingGap
