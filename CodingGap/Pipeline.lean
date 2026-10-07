import CodingGap.Model

/-!
# Tree pipelines and basic facts about routing schedules

* Basic facts about `RoutingSchedule.Knows` (monotonicity, the source knows everything).
* Framed tree pipelines: given `r` spanning trees rooted at `s`, of height at most `H₀` and edge
  congestion at most `W`, there is a routing schedule for `k` packets of length
  `W (H₀ + ⌈k / r⌉ - 1)`. Packets are assigned round-robin to the trees (`packet i` goes to tree
  `i % r` as its `(i / r)`-th packet). Every edge `e` gives each tree containing it a distinct
  *slot* in `{0, …, W - 1}`. Execution is divided into frames of `W` rounds; the `b`-th packet of
  tree `j` crosses the tree edge into a child at depth `d` during frame `b + d - 1`, in the slot
  of tree `j` on that edge.
* `exists_routingSchedule`: with a single shortest-path tree this shows that every connected graph
  admits a routing schedule (so `ROUTE(G,s,k)` is a minimum over a nonempty set).
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A spanning tree of `G` rooted at `s`, given by parent pointers and depths (any rooted spanning
tree, e.g. a BFS tree, has this form). -/
structure RootedTree (G : SimpleGraph V) (s : V) where
  parent : V → V
  depth : V → ℕ
  depth_root : depth s = 0
  adj : ∀ u, u ≠ s → G.Adj (parent u) u
  depth_parent : ∀ u, u ≠ s → depth u = depth (parent u) + 1

namespace RootedTree

variable {s : V} (T : RootedTree G s)

theorem depth_pos {u : V} (hu : u ≠ s) : 0 < T.depth u := by
  rw [T.depth_parent u hu]; omega

theorem eq_root_of_depth_eq_zero {u : V} (h : T.depth u = 0) : u = s := by
  by_contra hu; have := T.depth_pos hu; omega

/-- Tree `T` contains the edge `e` (as the edge from a vertex to its parent). -/
def Uses (e : Sym2 V) : Prop := ∃ u, u ≠ s ∧ s(T.parent u, u) = e

/-- A tree uses every edge for at most one child. -/
theorem child_unique {u u' : V} (hu : u ≠ s) (hu' : u' ≠ s)
    (h : s(T.parent u, u) = s(T.parent u', u')) : u = u' := by
  rcases Sym2.eq_iff.1 h with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · have := T.depth_parent u hu
    have := T.depth_parent u' hu'
    rw [h1] at *
    rw [← h2] at *
    omega

end RootedTree

namespace RoutingSchedule

variable [DecidableRel G.Adj] {k : ℕ} (σ : RoutingSchedule V k) {s : V}

theorem knows_mono {t t' : ℕ} (h : t ≤ t') {u : V} {i : Fin k} (hk : σ.Knows G s t u i) :
    σ.Knows G s t' u i := by
  induction t', h using Nat.le_induction with
  | base => exact hk
  | succ n _ ih => exact Or.inl ih

theorem knows_source (t : ℕ) (i : Fin k) : σ.Knows G s t s i :=
  σ.knows_mono (Nat.zero_le t) (show σ.Knows G s 0 s i from rfl)

theorem knows_succ_of_send {t : ℕ} {u w : V} {i : Fin k} (hadj : G.Adj u w)
    (h : σ.send u w t = some i) : σ.Knows G s (t + 1) w i :=
  Or.inr ⟨u, hadj, h⟩

end RoutingSchedule

/-! ### The framed pipeline schedule -/

section Framed

variable [DecidableRel G.Adj] {s : V} {r : ℕ} (T : Fin r → RootedTree G s) (W : ℕ)

/-- The slot of tree `j` on edge `e`: the number of trees with smaller index using `e`. -/
noncomputable def slot (e : Sym2 V) (j : Fin r) : ℕ := by
  classical
  exact (univ.filter fun j' => j' < j ∧ (T j').Uses e).card

theorem slot_lt {e : Sym2 V} {j : Fin r} (hj : (T j).Uses e)
    (hW : ∀ e, (by classical exact (univ.filter fun j => (T j).Uses e).card) ≤ W) :
    slot T e j < W := by
  classical
  refine lt_of_lt_of_le (card_lt_card ?_) (hW e)
  refine ⟨fun j' hj' => ?_, fun h => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hj' ⊢; exact hj'.2
  · have := h (show j ∈ univ.filter fun j => (T j).Uses e by simp [hj])
    simp at this

theorem slot_injective {e : Sym2 V} {j j' : Fin r} (hj : (T j).Uses e) (hj' : (T j').Uses e)
    (h : slot T e j = slot T e j') : j = j' := by
  classical
  by_contra hne
  wlog hlt : j < j' generalizing j j'
  · exact this hj' hj h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have : slot T e j < slot T e j' := by
    refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨hx.1.trans hlt, hx.2⟩
    · have := hsub (show j ∈ univ.filter fun j'' => j'' < j' ∧ (T j'').Uses e by simp [hlt, hj])
      simp at this
  omega

/-- Congestion at most `W`: every edge lies in at most `W` of the trees. -/
def CongestionLE : Prop :=
  ∀ e : Sym2 V, (by classical exact (univ.filter fun j => (T j).Uses e).card) ≤ W

variable (hr : 0 < r) {k : ℕ}

/-- The tree carrying packet `i`. -/
def treeOf (i : Fin k) : Fin r := ⟨i.val % r, Nat.mod_lt _ hr⟩

/-- Packet `i` crosses the tree edge `x → y` of its tree `j` in round `t`: the edge leads to the
child `y` at depth `d`, and `t` is the slot of `j` on the edge in frame `i / r + d - 1`. -/
def SendCond (x y : V) (t : ℕ) (i : Fin k) : Prop :=
  y ≠ s ∧ (T (treeOf hr i)).parent y = x ∧
    t = (i.val / r + (T (treeOf hr i)).depth y - 1) * W + slot T s(x, y) (treeOf hr i)

open Classical in
/-- The framed pipeline schedule. -/
noncomputable def framedSchedule : RoutingSchedule V k :=
  ⟨fun x y t => if h : ∃ i, SendCond T W hr x y t i then some h.choose else none⟩

variable {T W hr}

theorem sendCond_unique (hW : CongestionLE T W) {x y : V} {t : ℕ} {i i' : Fin k}
    (h : SendCond T W hr x y t i) (h' : SendCond T W hr x y t i') : i = i' := by
  obtain ⟨hy, hp, ht⟩ := h
  obtain ⟨-, hp', ht'⟩ := h'
  have hu : (T (treeOf hr i)).Uses s(x, y) := ⟨y, hy, by rw [hp]⟩
  have hu' : (T (treeOf hr i')).Uses s(x, y) := ⟨y, hy, by rw [hp']⟩
  have hs := slot_lt T W hu hW
  have hs' := slot_lt T W hu' hW
  have hmod : t % W = slot T s(x, y) (treeOf hr i) := by rw [ht, Nat.mul_add_mod_of_lt hs]
  have hmod' : t % W = slot T s(x, y) (treeOf hr i') := by rw [ht', Nat.mul_add_mod_of_lt hs']
  have hjj : treeOf hr i = treeOf hr i' := slot_injective T hu hu' (hmod.symm.trans hmod')
  rw [← hjj] at ht'
  have hW0 : 0 < W := by omega
  have hd := (T (treeOf hr i)).depth_pos hy
  have h1 := Nat.eq_of_mul_eq_mul_right hW0 (Nat.add_right_cancel (ht.symm.trans ht'))
  generalize (T (treeOf hr i)).depth y = d at hd h1
  have hdiv : i.val / r = i'.val / r := by
    generalize i.val / r = b at h1 ⊢
    generalize i'.val / r = b' at h1 ⊢
    omega
  have hmod'' : i.val % r = i'.val % r := congrArg Fin.val hjj
  exact Fin.ext (by rw [← Nat.div_add_mod i.val r, ← Nat.div_add_mod i'.val r, hdiv, hmod''])

theorem framedSchedule_send (hW : CongestionLE T W) {x y : V} {t : ℕ} {i : Fin k} :
    (framedSchedule (k := k) T W hr).send x y t = some i ↔ SendCond T W hr x y t i := by
  classical
  simp only [framedSchedule]
  constructor
  · intro h
    split_ifs at h with hex
    · cases h; exact hex.choose_spec
  · intro h
    rw [dif_pos ⟨i, h⟩]
    exact congrArg some (sendCond_unique hW (Exists.choose_spec ⟨i, h⟩) h)

/-- Packet `i` reaches every vertex `y` by the end of frame `i / r + depth y - 1`. -/
theorem knows_framed (hW : CongestionLE T W) (i : Fin k) :
    ∀ y, (framedSchedule (k := k) T W hr).Knows G s ((i.val / r + (T (treeOf hr i)).depth y) * W)
      y i := by
  suffices ∀ n y, (T (treeOf hr i)).depth y = n →
      (framedSchedule (k := k) T W hr).Knows G s ((i.val / r + n) * W) y i from
    fun y => this _ y rfl
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [(T _).eq_root_of_depth_eq_zero hy]
    exact RoutingSchedule.knows_source _ _ i
  | succ n ih =>
    intro y hy
    have hys : y ≠ s := by rintro rfl; rw [(T _).depth_root] at hy; omega
    have hdx : (T (treeOf hr i)).depth ((T (treeOf hr i)).parent y) = n := by
      have := (T (treeOf hr i)).depth_parent y hys; omega
    have hu : (T (treeOf hr i)).Uses s((T (treeOf hr i)).parent y, y) := ⟨y, hys, rfl⟩
    have hs := slot_lt T W hu hW
    have hsend : (framedSchedule (k := k) T W hr).send ((T (treeOf hr i)).parent y) y
        ((i.val / r + n) * W + slot T s((T (treeOf hr i)).parent y, y) (treeOf hr i)) =
        some i := by
      rw [framedSchedule_send hW]
      refine ⟨hys, rfl, ?_⟩
      rw [hy, show i.val / r + (n + 1) - 1 = i.val / r + n by generalize i.val / r = b; omega]
    have h2 := RoutingSchedule.knows_succ_of_send (s := s) _ ((T _).adj y hys) hsend
    refine RoutingSchedule.knows_mono _ ?_ h2
    nlinarith

theorem isValid_framed (hW : CongestionLE T W) (R : ℕ) :
    (framedSchedule (k := k) T W hr).IsValid G s R := by
  intro x y t i _ h
  rw [framedSchedule_send hW] at h
  obtain ⟨hys, hp, ht⟩ := h
  refine ⟨hp ▸ (T _).adj y hys, ?_⟩
  have hdx := (T (treeOf hr i)).depth_parent y hys
  rw [hp] at hdx
  refine RoutingSchedule.knows_mono _ ?_ (knows_framed hW i x)
  rw [ht, hdx]
  generalize i.val / r = b
  generalize (T (treeOf hr i)).depth x = d
  rw [show b + (d + 1) - 1 = b + d by omega]
  exact Nat.le_add_right _ _

/-- **Framed tree pipelines.** `r ≥ 1` rooted spanning trees of height at most `H₀`
and edge congestion at most `W` yield a valid routing schedule of `k` packets of length
`W (H₀ + ⌈k / r⌉ - 1)`. -/
theorem framed_mem (hr : 0 < r) (hW : CongestionLE T W) {H₀ : ℕ}
    (hH : ∀ j u, (T j).depth u ≤ H₀) :
    ∃ σ : RoutingSchedule V k, σ.IsValid G s (W * (H₀ + ⌈(k : ℚ) / r⌉₊ - 1)) ∧
      σ.Completes G s (W * (H₀ + ⌈(k : ℚ) / r⌉₊ - 1)) := by
  refine ⟨framedSchedule (k := k) T W hr, isValid_framed hW _, fun y i => ?_⟩
  refine RoutingSchedule.knows_mono _ ?_ (knows_framed hW i y)
  have hb : i.val / r + 1 ≤ ⌈(k : ℚ) / r⌉₊ := by
    rw [Nat.add_one_le_iff, Nat.lt_ceil, lt_div_iff₀ (by exact_mod_cast hr)]
    have : i.val / r * r ≤ i.val := Nat.div_mul_le_self _ _
    have : (i.val / r * r : ℕ) < k := lt_of_le_of_lt this i.isLt
    exact_mod_cast this
  have := hH (treeOf hr i) y
  rw [mul_comm W]
  exact Nat.mul_le_mul_right _ (by omega)

/-- Framed tree pipelines as a bound on `ROUTE(G,s,k)`. -/
theorem routingTime_le_framed (hr : 0 < r) (hW : CongestionLE T W) {H₀ : ℕ}
    (hH : ∀ j u, (T j).depth u ≤ H₀) :
    routingTime G s k ≤ W * (H₀ + ⌈(k : ℚ) / r⌉₊ - 1) :=
  Nat.sInf_le (framed_mem (k := k) hr hW hH)

end Framed

/-! ### Rooting a spanning tree: some routing schedule exists -/

section Rooting

variable {T : SimpleGraph V} (hT : T.Connected) {s : V}

include hT in
theorem exists_parent {u : V} (hu : u ≠ s) :
    ∃ w, T.Adj w u ∧ T.dist s u = T.dist s w + 1 := by
  obtain ⟨p, hp⟩ := hT.exists_walk_length_eq_dist u s
  cases p with
  | nil => exact absurd rfl hu
  | cons h q =>
    rename_i w
    refine ⟨w, h.symm, le_antisymm ?_ ?_⟩
    · obtain ⟨p', hp'⟩ := hT.exists_walk_length_eq_dist s w
      have := SimpleGraph.dist_le (p'.concat h.symm)
      rw [SimpleGraph.Walk.length_concat, hp'] at this
      exact this
    · have h1 := SimpleGraph.dist_le q
      rw [SimpleGraph.dist_comm (u := s) (v := u), ← hp, SimpleGraph.Walk.length_cons,
        SimpleGraph.dist_comm]
      omega

/-- The connected spanning subgraph `T ≤ G`, rooted at `s` along shortest paths of `T`. -/
noncomputable def rootAt (hle : T ≤ G) (s : V) : RootedTree G s where
  parent u := if h : u = s then s else (exists_parent hT h).choose
  depth u := T.dist s u
  depth_root := SimpleGraph.dist_self
  adj u hu := by
    simp only [dif_neg hu]
    exact hle (exists_parent hT hu).choose_spec.1
  depth_parent u hu := by
    simp only [dif_neg hu]
    exact (exists_parent hT hu).choose_spec.2

theorem rootAt_depth_le (hle : T ≤ G) (u : V) : (rootAt hT hle s).depth u ≤ T.diam :=
  haveI : Nonempty V := ⟨s⟩
  SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.1 hT)

end Rooting

/-- A connected graph admits some routing schedule (a pipeline along one shortest-path tree). -/
theorem exists_routingSchedule [DecidableRel G.Adj] (hG : G.Connected) (s : V) (k : ℕ) :
    ∃ R, ∃ σ : RoutingSchedule V k, σ.IsValid G s R ∧ σ.Completes G s R := by
  classical
  refine ⟨_, framed_mem (k := k) (T := fun _ : Fin 1 => rootAt hG le_rfl s) (W := 1) one_pos
    (fun e => ?_) (H₀ := G.diam) fun _ u => rootAt_depth_le hG le_rfl u⟩
  exact (card_filter_le (univ : Finset (Fin 1)) _).trans (by simp)

end CodingGap
