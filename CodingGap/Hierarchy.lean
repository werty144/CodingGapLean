import CodingGap.Halving
import CodingGap.Pipeline
import CodingGap.Benchmark

/-!
# Whole-packet broadcast along the halving hierarchy (`thm:forwarding`)

* `extend_level` (one level of the calendar `eq:calendar`): if every vertex of `A` holds all `k` packets at time `R₁` and
  every `v ∈ B` has `q` paths from `A` of length at most `H` with edge congestion at most `4`, the
  schedule can be extended so that every vertex of `B` holds all packets at time
  `R₁ + 4 (H + ⌈k/q⌉ - 1)`. Packet `m` travels to `v` along its path number `m mod q`; its
  `(m / q)`-th packet crosses the `d`-th edge in frame `m / q + d - 1` (frames of four rounds),
  in the slot of that path on that edge.
* `exists_schedule_hierarchy` (the hierarchy `eq:hierarchy`): repeating the halving step from `V` down to
  `{s}` and informing the levels in reverse order,
  `ROUTE(G,s,k) ≤ 4 (4h + ⌈k/⌈r/2⌉⌉ - 1) ⌈log₂ n⌉`.
* `routingTime_le_log` (**Theorem `thm:forwarding`**): `ROUTE(G,s,k) ≤ 24 τ(G,s,k) ⌈log₂ n⌉`.
-/

namespace CodingGap

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} {s : V}

/-- `Knows` only depends on the sends before the current time. -/
theorem RoutingSchedule.knows_congr {σ σ' : RoutingSchedule V k} {R : ℕ}
    (h : ∀ u w t, t < R → σ.send u w t = σ'.send u w t) :
    ∀ t ≤ R, ∀ w i, σ.Knows G s t w i ↔ σ'.Knows G s t w i := by
  intro t
  induction t with
  | zero => intro _ w i; exact Iff.rfl
  | succ t ih =>
    intro ht w i
    change σ.Knows G s t w i ∨ _ ↔ σ'.Knows G s t w i ∨ _
    rw [ih (by omega) w i]
    simp only [h _ _ t (by omega)]

/-! ### One level -/

section Level

variable {A B : Finset V} {q H : ℕ} (L : LevelPaths G A B q H 4)

/-- A numbering of the path occurrences `(v, j)`. -/
noncomputable def occRank (o : V × Fin q) : ℕ := Fintype.equivFin (V × Fin q) o

/-- The slot of path occurrence `o` on the edge `e`. -/
noncomputable def lslot (e : Sym2 V) (o : V × Fin q) : ℕ :=
  ((B ×ˢ (univ : Finset (Fin q))).filter fun o' =>
    occRank o' < occRank o ∧ e ∈ (L.path o'.1 o'.2).edges).card

theorem lslot_lt {e : Sym2 V} {o : V × Fin q} (ho : o.1 ∈ B) (he : e ∈ (L.path o.1 o.2).edges) :
    lslot L e o < 4 := by
  refine lt_of_lt_of_le (card_lt_card ⟨fun o' ho' => ?_, fun hsub => ?_⟩) (L.congestion e)
  · simp only [mem_filter] at ho' ⊢; exact ⟨ho'.1, ho'.2.2⟩
  · have := hsub (show o ∈ (B ×ˢ (univ : Finset (Fin q))).filter
      (fun p => e ∈ (L.path p.1 p.2).edges) by simp [ho, he])
    simp at this

theorem lslot_injective {e : Sym2 V} {o o' : V × Fin q} (ho : o.1 ∈ B) (ho' : o'.1 ∈ B)
    (he : e ∈ (L.path o.1 o.2).edges) (he' : e ∈ (L.path o'.1 o'.2).edges)
    (h : lslot L e o = lslot L e o') : o = o' := by
  by_contra hne
  have hr : occRank o ≠ occRank o' := fun h' => hne ((Fintype.equivFin _).injective (Fin.ext h'))
  wlog hlt : occRank o < occRank o' generalizing o o'
  · exact this ho' ho he' he h.symm (Ne.symm hne) (Ne.symm hr) (by omega)
  have : lslot L e o < lslot L e o' := by
    refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1.trans hlt, hx.2.2⟩
    · have := hsub (show o ∈ (B ×ˢ (univ : Finset (Fin q))).filter (fun x =>
        occRank x < occRank o' ∧ e ∈ (L.path x.1 x.2).edges) by simp [ho, hlt, he])
      simp at this
  omega

variable (hq : 0 < q) (R₁ : ℕ)

/-- The path carrying packet `m`. -/
def pathIdx (m : Fin k) : Fin q := ⟨m.val % q, Nat.mod_lt _ hq⟩

/-- Packet `m` crosses the edge `u → w` in round `t`, as the `d`-th edge of the path to `v`. -/
def LSend (u w : V) (t : ℕ) (m : Fin k) : Prop :=
  ∃ v ∈ B, ∃ d < (L.path v (pathIdx hq m)).length,
    (L.path v (pathIdx hq m)).getVert d = u ∧ (L.path v (pathIdx hq m)).getVert (d + 1) = w ∧
    t = R₁ + 4 * (m.val / q + d) + lslot L s(u, w) (v, pathIdx hq m)

variable {L hq R₁}

theorem lsend_unique {u w : V} {t : ℕ} {m m' : Fin k} (h : LSend L hq R₁ u w t m)
    (h' : LSend L hq R₁ u w t m') : m = m' := by
  obtain ⟨v, hv, d, hd, hu, hw, ht⟩ := h
  obtain ⟨v', hv', d', hd', hu', hw', ht'⟩ := h'
  have he : s(u, w) ∈ (L.path v (pathIdx hq m)).edges :=
    (SimpleGraph.Walk.mk_mem_edges_iff_exists _).2 ⟨d, hd, by rw [hu, hw]⟩
  have he' : s(u, w) ∈ (L.path v' (pathIdx hq m')).edges :=
    (SimpleGraph.Walk.mk_mem_edges_iff_exists _).2 ⟨d', hd', by rw [hu', hw']⟩
  have hs := lslot_lt L (o := (v, pathIdx hq m)) hv he
  have hs' := lslot_lt L (o := (v', pathIdx hq m')) hv' he'
  have hslot : lslot L s(u, w) (v, pathIdx hq m) = lslot L s(u, w) (v', pathIdx hq m') := by
    omega
  have ho := lslot_injective L hv hv' he he' hslot
  simp only [Prod.mk.injEq] at ho
  obtain ⟨rfl, hj⟩ := ho
  rw [hj] at hu hd
  have hdd : d = d' := (L.isPath v hv _).getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) (hu.trans hu'.symm)
  subst hdd
  have hdiv : m.val / q = m'.val / q := by
    generalize m.val / q = a at ht
    generalize m'.val / q = a' at ht'
    rw [hslot] at ht
    omega
  have hmod : m.val % q = m'.val % q := congrArg Fin.val hj
  exact Fin.ext (by rw [← Nat.div_add_mod m.val q, ← Nat.div_add_mod m'.val q, hdiv, hmod])

variable (L hq R₁)

open Classical in
/-- The extended schedule: `σ₁` before time `R₁`, then the level's pipelines. -/
noncomputable def extendSchedule (σ₁ : RoutingSchedule V k) : RoutingSchedule V k :=
  ⟨fun u w t => if t < R₁ then σ₁.send u w t else
    if h : ∃ m, LSend L hq R₁ u w t m then some h.choose else none⟩

variable {L hq R₁}

theorem extendSchedule_send {σ₁ : RoutingSchedule V k} {u w : V} {t : ℕ} {m : Fin k}
    (ht : R₁ ≤ t) : (extendSchedule L hq R₁ σ₁).send u w t = some m ↔ LSend L hq R₁ u w t m := by
  classical
  simp only [extendSchedule, if_neg (not_lt.2 ht)]
  constructor
  · intro h
    split_ifs at h with hex
    cases h; exact hex.choose_spec
  · intro h
    rw [dif_pos ⟨m, h⟩]
    exact congrArg some (lsend_unique (Exists.choose_spec ⟨m, h⟩) h)

variable {σ₁ : RoutingSchedule V k}

theorem knows_extend_early {t : ℕ} (ht : t ≤ R₁) {w : V} {m : Fin k} :
    (extendSchedule L hq R₁ σ₁).Knows G s t w m ↔ σ₁.Knows G s t w m :=
  RoutingSchedule.knows_congr (fun u w t ht => by simp [extendSchedule, ht]) t ht w m

/-- Along its path, packet `m` reaches the `d`-th vertex by time `R₁ + 4 (m / q + d)`. -/
theorem knows_extend_path (hA : ∀ a ∈ A, ∀ m, σ₁.Knows G s R₁ a m) {v : V} (hv : v ∈ B)
    (m : Fin k) : ∀ d ≤ (L.path v (pathIdx hq m)).length,
      (extendSchedule L hq R₁ σ₁).Knows G s (R₁ + 4 * (m.val / q + d))
        ((L.path v (pathIdx hq m)).getVert d) m := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [SimpleGraph.Walk.getVert_zero]
    have := (knows_extend_early (L := L) (hq := hq) le_rfl).2 (hA _ (L.start_mem v hv (pathIdx hq m)) m)
    exact RoutingSchedule.knows_mono _ (by omega) this
  | succ d ih =>
    intro hd
    set P := L.path v (pathIdx hq m)
    have hsl := lslot_lt L (o := (v, pathIdx hq m)) hv
      ((SimpleGraph.Walk.mk_mem_edges_iff_exists P).2 ⟨d, hd, rfl⟩)
    have hsend : (extendSchedule L hq R₁ σ₁).send (P.getVert d) (P.getVert (d + 1))
        (R₁ + 4 * (m.val / q + d) + lslot L s(P.getVert d, P.getVert (d + 1)) (v, pathIdx hq m)) =
        some m :=
      (extendSchedule_send (by omega)).2 ⟨v, hv, d, hd, rfl, rfl, rfl⟩
    have := RoutingSchedule.knows_succ_of_send (s := s) _ (P.adj_getVert_succ hd) hsend
    exact RoutingSchedule.knows_mono _ (by omega) this

/-- **A single level of the hierarchy.** -/
theorem extend_level (hv₁ : σ₁.IsValid G s R₁) (hA : ∀ a ∈ A, ∀ m, σ₁.Knows G s R₁ a m) :
    (extendSchedule L hq R₁ σ₁).IsValid G s (R₁ + 4 * (H + ⌈(k : ℚ) / q⌉₊ - 1)) ∧
      ∀ v ∈ A ∪ B, ∀ m,
        (extendSchedule L hq R₁ σ₁).Knows G s (R₁ + 4 * (H + ⌈(k : ℚ) / q⌉₊ - 1)) v m := by
  constructor
  · intro u w t m _ h
    by_cases ht : t < R₁
    · have h' : σ₁.send u w t = some m := by simpa [extendSchedule, ht] using h
      obtain ⟨hadj, hk⟩ := hv₁ u w t m ht h'
      exact ⟨hadj, (knows_extend_early ht.le).2 hk⟩
    · obtain ⟨v, hv, d, hd, rfl, rfl, rfl⟩ := (extendSchedule_send (not_lt.1 ht)).1 h
      refine ⟨(L.path v (pathIdx hq m)).adj_getVert_succ hd, ?_⟩
      exact RoutingSchedule.knows_mono _ (by omega) (knows_extend_path hA hv m d hd.le)
  · intro v hv m
    rcases mem_union.1 hv with hvA | hvB
    · exact RoutingSchedule.knows_mono _ (by omega)
        ((knows_extend_early le_rfl).2 (hA v hvA m))
    · have h := knows_extend_path (L := L) (hq := hq) hA hvB m _ le_rfl
      rw [SimpleGraph.Walk.getVert_length] at h
      refine RoutingSchedule.knows_mono _ ?_ h
      have hb : m.val / q + 1 ≤ ⌈(k : ℚ) / q⌉₊ := by
        rw [Nat.add_one_le_iff, Nat.lt_ceil, lt_div_iff₀ (by exact_mod_cast hq)]
        have : m.val / q * q ≤ m.val := Nat.div_mul_le_self _ _
        have : (m.val / q * q : ℕ) < k := lt_of_le_of_lt this m.isLt
        exact_mod_cast this
      have := L.length_le v hvB (pathIdx hq m)
      omega

end Level

/-! ### The hierarchy -/

/-- **Rooted short-path broadcast, inductive form.** Every `S ∋ s` can be
informed within `4 (4h + ⌈k/q⌉ - 1) ⌈log₂ |S|⌉` rounds, `q = ⌈r/2⌉`. -/
theorem exists_schedule_hierarchy (hcpt : CPTTerminalPaths.{u}) {r h : ℕ} (hr : 1 ≤ r)
    (hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ h) (k : ℕ) :
    ∀ S : Finset V, s ∈ S → ∃ σ : RoutingSchedule V k, ∃ R,
      R ≤ 4 * (4 * h + ⌈(k : ℚ) / ((r + 1) / 2 : ℕ)⌉₊ - 1) * Nat.clog 2 S.card ∧
      σ.IsValid G s R ∧ ∀ v ∈ S, ∀ m, σ.Knows G s R v m := by
  set D := 4 * (4 * h + ⌈(k : ℚ) / ((r + 1) / 2 : ℕ)⌉₊ - 1)
  have hq : 0 < (r + 1) / 2 := by omega
  intro S
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro hs
    by_cases h2 : 2 ≤ n
    · obtain ⟨A, hAS, hAne, hsA, hAcard, ⟨L⟩⟩ := exists_halving hcpt hr hP hs (hn ▸ h2)
      have hlt : A.card < n := hn ▸ card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hAS, hAne⟩)
      obtain ⟨σ₁, R₁, hR₁, hv₁, hk₁⟩ := ih _ hlt A rfl hsA
      obtain ⟨hv₂, hk₂⟩ := extend_level (L := L) (hq := hq) hv₁ hk₁
      refine ⟨_, _, ?_, hv₂, fun v hv m => hk₂ v (by rw [union_sdiff_of_subset hAS]; exact hv) m⟩
      have hclog : Nat.clog 2 A.card + 1 ≤ Nat.clog 2 n := by
        rw [Nat.clog_of_two_le (by norm_num) h2]
        have := Nat.clog_mono_right 2 (show A.card ≤ (n + 2 - 1) / 2 by omega)
        omega
      calc R₁ + 4 * (4 * h + ⌈(k : ℚ) / ((r + 1) / 2 : ℕ)⌉₊ - 1)
          ≤ D * Nat.clog 2 A.card + D := by omega
        _ = D * (Nat.clog 2 A.card + 1) := by ring
        _ ≤ D * Nat.clog 2 n := Nat.mul_le_mul_left _ hclog
    · -- `S = {s}`: nothing to do
      refine ⟨⟨fun _ _ _ => none⟩, 0, Nat.zero_le _, fun _ _ _ _ h => absurd h (by omega),
        fun v hv m => ?_⟩
      have : v = s := by
        by_contra hvs
        have : 2 ≤ S.card := Finset.one_lt_card_iff.2 ⟨v, s, hv, hs, hvs⟩
        omega
      subst this
      rfl

/-- **Theorem `thm:forwarding`.** Assuming the integral terminal-path lemma of Chuzhoy–Parter–Tan
(`lem:cpt`), `ROUTE(G,s,k) ≤ 24 τ(G,s,k) ⌈log₂ n⌉`. -/
theorem routingTime_le_log (hcpt : CPTTerminalPaths.{u}) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (s : V) {k : ℕ} (hk : 1 ≤ k) :
    routingTime G s k ≤ 24 * tau G s k * Nat.clog 2 (Fintype.card V) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, v ≠ s := by
    by_contra h
    push Not at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    omega
  set T := tau G s k
  have hT : 1 ≤ T := one_le_tau hG hk ⟨v₀, hv₀⟩
  set r := ⌈(k : ℚ) / T⌉₊
  have hr : 1 ≤ r := Nat.one_le_ceil_iff.2 (by positivity)
  have hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ T :=
    fun v hv => (exists_short_disjointPaths hv hT (tau_mem hG hk v hv)).imp
      fun _ hP i => (hP i).trans (min_le_left _ _)
  obtain ⟨σ, R, hR, hv, hkn⟩ := exists_schedule_hierarchy hcpt hr hP k univ (mem_univ s)
  have hR' : routingTime G s k ≤ R := Nat.sInf_le ⟨σ, hv, fun v m => hkn v (mem_univ v) m⟩
  -- one level takes at most `24 T` rounds
  have hkq : ⌈(k : ℚ) / ((r + 1) / 2 : ℕ)⌉₊ ≤ 2 * T := by
    have hq : (0 : ℚ) < ((r + 1) / 2 : ℕ) := by exact_mod_cast (show 0 < (r + 1) / 2 by omega)
    rw [Nat.ceil_le, div_le_iff₀ hq]
    have h1 := Nat.le_ceil ((k : ℚ) / T)
    rw [div_le_iff₀ (by exact_mod_cast hT)] at h1
    have h2 : (r : ℚ) ≤ 2 * ((r + 1) / 2 : ℕ) := by exact_mod_cast (show r ≤ 2 * ((r + 1) / 2) by omega)
    have h3 : (0 : ℚ) ≤ T := by positivity
    push_cast at h2 ⊢
    nlinarith
  rw [card_univ] at hR
  refine hR'.trans (hR.trans (Nat.mul_le_mul_right _ ?_))
  omega

end CodingGap
