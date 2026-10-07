import Mathlib

/-!
# The model

This file contains *every definition* that the high-level statements in `CodingGap.MainTheorems`
use, following Section "Model and problem" of the paper and the
definition of temporal cuts in Section "Techniques overview". No theorems are proved here.

Throughout, `G : SimpleGraph V` is a finite simple undirected graph, `s : V` is the source,
and `k : ℕ` is the number of packets.

## Contents

* The time-expanded network `G[T]`, its finite-capacity temporal cuts, the temporal min-cut
  `C_T(s,v)` (`temporalMinCut`) and the benchmark `τ(G,s,k)` (`tau`).
* Coding schemes: deterministic protocols over an alphabet `A` (`Protocol`), their execution, and
  `CODE(G,s,k)` (`codedTime`). The paper's alphabet of `B`-bit strings is `Bits B`. Their
  multi-source variant (`MultiProtocol`, `multiSourceCodedTime`), where packet `i` starts at
  `src i`.
* Routing schemes: content-oblivious routing schedules (`RoutingSchedule`) and `ROUTE(G,s,k)`
  (`routingTime`); their multi-source variant (`multiSourceRoutingTime`), where packet `i` starts
  at an arbitrary vertex `src i`.
* Edge-disjoint path families, `λ_v` (`maxDisjointPaths`) and `L_v(q)` (`minTotalLength`).
* The doubled multigraph `2G`: `(r,d)`-connectivity (`DoubledConnected`) and integral terminal
  path systems (`DoubledTerminalPaths`), used to state the cited lemma of Chuzhoy, Parter and Tan;
  the path systems of one level of the halving hierarchy (`LevelPaths`).
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The time-expanded network `G[T]` -/

section TimeExpanded

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The communication arcs of the time-expanded network `G[T]`.

A triple `(u, w, t)` stands for the unit-capacity arc `(u, t) → (w, t + 1)`; it exists for every
ordered pair of adjacent vertices and every `0 ≤ t < T`. (The storage arcs `(u,t) → (u,t+1)` have
infinite capacity and never appear in a finite cut, see `IsTemporalCut`.) -/
def commArcs (T : ℕ) : Finset (V × V × ℕ) :=
  (univ ×ˢ univ ×ˢ range T).filter fun a => G.Adj a.1 a.2.1

/-- `S` is the source side of a *finite-capacity* `(s,0)`–`(v,T)` cut of `G[T]`.

The vertices of `G[T]` are the pairs `(u,t)` with `t ≤ T`; points of `S` with `t > T` are
irrelevant. Because storage arcs `(u,t) → (u,t+1)` have infinite capacity, a cut has finite
capacity exactly when no storage arc leaves `S`, which is the condition `storage_closed`. -/
structure IsTemporalCut (s v : V) (T : ℕ) (S : Set (V × ℕ)) : Prop where
  source_mem : (s, 0) ∈ S
  sink_not_mem : (v, T) ∉ S
  storage_closed : ∀ u t, t < T → (u, t) ∈ S → (u, t + 1) ∈ S

/-- The communication arcs of `G[T]` leaving the set `S`. -/
noncomputable def cutArcs (T : ℕ) (S : Set (V × ℕ)) : Finset (V × V × ℕ) := by
  classical
  exact (commArcs G T).filter fun a => (a.1, a.2.2) ∈ S ∧ (a.2.1, a.2.2 + 1) ∉ S

/-- The capacity of the cut with source side `S`: the number of unit-capacity communication arcs
leaving `S` (for a finite cut no infinite-capacity storage arc leaves `S`). -/
noncomputable def cutCapacity (T : ℕ) (S : Set (V × ℕ)) : ℕ :=
  (cutArcs G T S).card

/-- `C_T(s,v)`: the minimum capacity of an `(s,0)`–`(v,T)` cut in the time-expanded network
`G[T]`. Cuts of infinite capacity are never minimal (a finite cut exists whenever `v ≠ s`), so it
suffices to minimize over finite-capacity cuts. -/
noncomputable def temporalMinCut (s v : V) (T : ℕ) : ℕ :=
  sInf {c | ∃ S, IsTemporalCut s v T S ∧ cutCapacity G T S = c}

/-- The temporal benchmark (equation (1) of the paper):
`τ(G,s,k) = min {T ≥ 0 : C_T(s,v) ≥ k for all v ≠ s}`. -/
noncomputable def tau (s : V) (k : ℕ) : ℕ :=
  sInf {T | ∀ v, v ≠ s → k ≤ temporalMinCut G s v T}

end TimeExpanded

/-! ## Coding schemes -/

section Protocols

/-- A (deterministic) coding scheme over the alphabet `A` of packets and messages (`A = Bits B` in
the paper; `A` is a type in the lowest universe, like the state spaces).

* Every vertex has a state; memory and local computation are unrestricted, so the state space is
  an arbitrary type.
* The source starts in a state depending on the input `X : Fin k → A`; every other vertex starts
  in an input-independent state (which may encode arbitrary advice about the topology).
* In round `t` (from time `t` to time `t + 1`) every vertex `u` sends one symbol of `A` to each
  neighbour `w`, depending on its current state; there is no extra silence symbol.
* At time `t + 1` every vertex updates its state from its old state and the symbols it received
  (only from its neighbours: the messages are masked by adjacency when the protocol is run).
* The output of a vertex is a function of its state.

A protocol may depend arbitrarily on `G`, `s` and `k` (offline advice). -/
structure Protocol (V : Type*) (A : Type) (k : ℕ) where
  /-- The state space of the vertices. -/
  State : Type
  /-- Initial state of the source, holding the input. -/
  initSource : (Fin k → A) → State
  /-- Initial (input-independent) state of every other vertex. -/
  init : V → State
  /-- `send u w t σ` is the symbol sent by `u` to `w` in round `t` when `u` is in state `σ`. -/
  send : V → V → ℕ → State → A
  /-- `step w t σ m` is the new state of `w` at time `t + 1`, given its state `σ` at time `t` and
  the received messages `m u` (which is `none` for non-neighbours `u`). -/
  step : V → ℕ → State → (V → Option A) → State
  /-- The decoded input of a vertex in a given state. -/
  output : V → State → (Fin k → A)

namespace Protocol

variable {A : Type} {k : ℕ} (P : Protocol V A k) (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The execution of a protocol: `P.run G s X t u` is the state of `u` at time `t` on input `X`. -/
def run (s : V) (X : Fin k → A) : ℕ → V → P.State
  | 0 => fun u => if u = s then P.initSource X else P.init u
  | t + 1 => fun w =>
      P.step w t (run s X t w)
        (fun u => if G.Adj u w then some (P.send u w t (run s X t u)) else none)

/-- Vertex `v` outputs the correct input at time `T`. -/
def Recovers (s : V) (X : Fin k → A) (v : V) (T : ℕ) : Prop :=
  P.output v (P.run G s X T v) = X

/-- Broadcast is complete at time `T`: every vertex outputs the input. -/
def Broadcasts (s : V) (X : Fin k → A) (T : ℕ) : Prop :=
  ∀ v, P.Recovers G s X v T

end Protocol

/-- The alphabet of the paper: `B`-bit strings. Packets and messages are both elements of
`Bits B`. -/
abbrev Bits (B : ℕ) := Fin B → Bool

/-- `CODE(G,s,k)`: the minimum completion time of a correct (deterministic) coding scheme over the
alphabet `A`, i.e. the least `T` such that some protocol makes every vertex output the input `X`
at time `T`, for every input `X`. With `A = Bits B` this is `CODE(G,s,k,B)` of the paper.

(The paper lets every vertex `v` stop at its own round `T_v` and takes `T = max_v T_v`; since
memory is unrestricted, a vertex can keep its output until time `T`, so both definitions agree.) -/
noncomputable def codedTime (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (A : Type)
    (k : ℕ) : ℕ :=
  sInf {T | ∃ P : Protocol V A k, ∀ X, P.Broadcasts G s X T}

/-- A coding scheme for *multi-source* broadcast, where packet `i` is initially held only by
`src i`. It is a `Protocol` except for the initial states: every vertex starts in a state that
depends only on the packets it holds, given as `held i = some (X i)` for its own packets and
`held i = none` for the others. -/
structure MultiProtocol (V : Type*) (A : Type) (k : ℕ) where
  /-- The state space of the vertices. -/
  State : Type
  /-- Initial state of a vertex, given the packets it holds. -/
  init : V → (Fin k → Option A) → State
  /-- `send u w t σ` is the symbol sent by `u` to `w` in round `t` when `u` is in state `σ`. -/
  send : V → V → ℕ → State → A
  /-- `step w t σ m` is the new state of `w` at time `t + 1` (`m u = none` for non-neighbours). -/
  step : V → ℕ → State → (V → Option A) → State
  /-- The decoded input of a vertex in a given state. -/
  output : V → State → (Fin k → A)

namespace MultiProtocol

variable {A : Type} {k : ℕ} (P : MultiProtocol V A k) (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The packets initially held by `u` when packet `i` starts at `src i`. -/
def held (src : Fin k → V) (X : Fin k → A) (u : V) : Fin k → Option A :=
  fun i => if src i = u then some (X i) else none

/-- The execution of a multi-source protocol on input `X`. -/
def run (src : Fin k → V) (X : Fin k → A) : ℕ → V → P.State
  | 0 => fun u => P.init u (held src X u)
  | t + 1 => fun w =>
      P.step w t (run src X t w)
        (fun u => if G.Adj u w then some (P.send u w t (run src X t u)) else none)

/-- Broadcast is complete at time `T`: every vertex outputs the input. -/
def Broadcasts (src : Fin k → V) (X : Fin k → A) (T : ℕ) : Prop :=
  ∀ v, P.output v (P.run G src X T v) = X

end MultiProtocol

/-- The minimum completion time of a correct coding scheme over the alphabet `A` for the
multi-source broadcast instance in which packet `i` is initially held by `src i`. -/
noncomputable def multiSourceCodedTime (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (src : Fin k → V) (A : Type) : ℕ :=
  sInf {T | ∃ P : MultiProtocol V A k, ∀ X, P.Broadcasts G src X T}

end Protocols

/-! ## Routing schemes -/

section Routing

/-- A routing schedule for `k` packets: `σ.send u w t = some i` means that `u` forwards (a copy
of) packet `i` to `w` in round `t` (from time `t` to time `t + 1`); `none` means that the channel
is unused. Packets are treated as opaque: the schedule is fixed in advance and does not depend on
the packet contents.

The paper defines a routing scheme as a scheme in which a vertex only sends packets it has
already received. Content-obliviousness is what its upper bounds construct and what its lower
bound for routing (the toy example) needs: if the choice of the forwarded packet could depend on
the packet values, this choice could itself encode information. -/
structure RoutingSchedule (V : Type*) (k : ℕ) where
  send : V → V → ℕ → Option (Fin k)

namespace RoutingSchedule

variable {k : ℕ} (σ : RoutingSchedule V k) (G : SimpleGraph V)

/-- `σ.Knows G s t u i`: vertex `u` holds packet `i` at time `t` (all packets start at `s`). -/
def Knows (s : V) : ℕ → V → Fin k → Prop
  | 0 => fun u _ => u = s
  | t + 1 => fun w i => Knows s t w i ∨ ∃ u, G.Adj u w ∧ σ.send u w t = some i

/-- The schedule is valid during the first `R` rounds: packets are only sent along edges and only
by vertices that already hold them. -/
def IsValid (s : V) (R : ℕ) : Prop :=
  ∀ u w t i, t < R → σ.send u w t = some i → G.Adj u w ∧ σ.Knows G s t u i

/-- Every vertex holds every packet at time `R`. -/
def Completes (s : V) (R : ℕ) : Prop :=
  ∀ v i, σ.Knows G s R v i

/-- Multi-source version of `Knows`: packet `i` is initially held only by `src i`. -/
def KnowsFrom (src : Fin k → V) : ℕ → V → Fin k → Prop
  | 0 => fun u i => u = src i
  | t + 1 => fun w i => KnowsFrom src t w i ∨ ∃ u, G.Adj u w ∧ σ.send u w t = some i

/-- Multi-source version of `IsValid`. -/
def IsValidFrom (src : Fin k → V) (R : ℕ) : Prop :=
  ∀ u w t i, t < R → σ.send u w t = some i → G.Adj u w ∧ σ.KnowsFrom G src t u i

/-- Multi-source version of `Completes`. -/
def CompletesFrom (src : Fin k → V) (R : ℕ) : Prop :=
  ∀ v i, σ.KnowsFrom G src R v i

end RoutingSchedule

/-- `ROUTE(G,s,k)`: the minimum completion time of a valid routing schedule. -/
noncomputable def routingTime (G : SimpleGraph V) (s : V) (k : ℕ) : ℕ :=
  sInf {R | ∃ σ : RoutingSchedule V k, σ.IsValid G s R ∧ σ.Completes G s R}

/-- The minimum completion time of a valid routing schedule for the multi-source broadcast
instance in which packet `i` is initially held by `src i`. -/
noncomputable def multiSourceRoutingTime (G : SimpleGraph V) {k : ℕ} (src : Fin k → V) : ℕ :=
  sInf {R | ∃ σ : RoutingSchedule V k, σ.IsValidFrom G src R ∧ σ.CompletesFrom G src R}

end Routing

/-! ## Edge-disjoint path families -/

section Paths

variable (G : SimpleGraph V)

/-- A family of `q` pairwise edge-disjoint `s`–`v` paths in `G`. -/
structure DisjointPaths (s v : V) (q : ℕ) where
  path : Fin q → G.Walk s v
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise fun i j => (path i).edges.Disjoint (path j).edges

/-- The total length (number of edges) of a path family. -/
def DisjointPaths.totalLength {G : SimpleGraph V} {s v : V} {q : ℕ} (P : DisjointPaths G s v q) :
    ℕ :=
  ∑ i, (P.path i).length

/-- `λ_v`: the maximum number of edge-disjoint `s`–`v` paths. -/
noncomputable def maxDisjointPaths (s v : V) : ℕ :=
  sSup {q | Nonempty (DisjointPaths G s v q)}

/-- `L_v(q)`: the minimum total length of `q` edge-disjoint `s`–`v` paths (`L_v(0) = 0`). -/
noncomputable def minTotalLength (s v : V) (q : ℕ) : ℕ :=
  sInf {L | ∃ P : DisjointPaths G s v q, P.totalLength = L}

end Paths

/-! ## The doubled multigraph `2G` -/

section Doubled

variable (G : SimpleGraph V)

/-- A family of `r` pairwise edge-disjoint `u`–`w` paths with at most `d` edges each in the
multigraph `2G` obtained from `G` by doubling every edge. A path of `2G` is a path of `G` together
with the choice of one of the two parallel copies (`copy i e : Fin 2`) of each of its edges; the
family is edge-disjoint in `2G` when no copy of an edge is used by two different paths (a path
never uses an edge twice). -/
structure DoubledDisjointPaths (u w : V) (r d : ℕ) where
  path : Fin r → G.Walk u w
  isPath : ∀ i, (path i).IsPath
  length_le : ∀ i, (path i).length ≤ d
  copy : Fin r → Sym2 V → Fin 2
  disjoint : ∀ i j, i ≠ j → ∀ e ∈ (path i).edges, e ∈ (path j).edges → copy i e ≠ copy j e

/-- `2G` is `(r,d)`-connected: every two distinct vertices are joined by `r` edge-disjoint paths
of `2G` with at most `d` edges each. -/
def DoubledConnected (r d : ℕ) : Prop :=
  ∀ u w : V, u ≠ w → Nonempty (DoubledDisjointPaths G u w r d)

/-- An integral terminal path system in `2G` (the conclusion of Chuzhoy–Parter–Tan, `lem:cpt`):
finitely many paths of `2G` (paths of `G` with a choice of copy for each edge), each joining two
distinct vertices of `U ∪ {s}`, such that every `u ∈ U` is an endpoint of at least `r` of them,
every path has at most `D` edges, and every edge copy lies on at most two paths. -/
structure DoubledTerminalPaths [DecidableEq V] (s : V) (U : Finset V) (r D : ℕ) where
  N : ℕ
  src : Fin N → V
  dst : Fin N → V
  path : ∀ i, G.Walk (src i) (dst i)
  isPath : ∀ i, (path i).IsPath
  src_ne_dst : ∀ i, src i ≠ dst i
  src_mem : ∀ i, src i = s ∨ src i ∈ U
  dst_mem : ∀ i, dst i = s ∨ dst i ∈ U
  endpoint : ∀ u ∈ U, r ≤ (Finset.univ.filter fun i => src i = u ∨ dst i = u).card
  length_le : ∀ i, (path i).length ≤ D
  copy : Fin N → Sym2 V → Fin 2
  congestion : ∀ (e : Sym2 V) (c : Fin 2),
    (Finset.univ.filter fun i => e ∈ (path i).edges ∧ copy i e = c).card ≤ 2

end Doubled

/-! ## Level path systems of the halving hierarchy -/

/-- One level of the halving hierarchy (`lem:halving`): every `v ∈ B` receives `q` paths of length
at most `H` from vertices of `A`, and every edge lies on at most `W` of these paths. -/
structure LevelPaths (G : SimpleGraph V) (A B : Finset V) (q H W : ℕ) where
  start : V → Fin q → V
  start_mem : ∀ v ∈ B, ∀ j, start v j ∈ A
  path : ∀ v j, G.Walk (start v j) v
  isPath : ∀ v ∈ B, ∀ j, (path v j).IsPath
  length_le : ∀ v ∈ B, ∀ j, (path v j).length ≤ H
  congestion : ∀ e : Sym2 V,
    ((B ×ˢ (Finset.univ : Finset (Fin q))).filter fun p => e ∈ (path p.1 p.2).edges).card ≤ W

end CodingGap
