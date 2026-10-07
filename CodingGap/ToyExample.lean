import CodingGap.CodingProtocol

/-!
# The toy example of Figure `fig:coding-example`: a coding gap of `3/2`

The source `s` is adjacent to three relays `a, b, c`; the sinks are `t₁` (adjacent to `a, b`),
`t₂` (adjacent to `a, c`) and `t₃` (adjacent to `b, c`). With `k = 2` packets `m₁, m₂`:

* `τ = 2`: the sinks are two hops away from `s`, and two rounds suffice for coding;
* coding finishes in two rounds over every finite field (`ToyExample.codedTime_eq`): `s` sends
  `m₁`, `m₂`, `m₁ + m₂` to `a, b, c` and then `m₂, m₁, m₁` to complete the relays, while the relays
  forward their first symbol to the sinks;
* no two-round routing schedule exists, since the three relays would need pairwise different
  packets (`ToyExample.not_completes_le_two`), while three rounds suffice
  (`ToyExample.routingTime_eq`).
-/

namespace CodingGap

/-- The seven vertices of Figure `fig:coding-example`. -/
inductive ToyExample
  | s | a | b | c | t₁ | t₂ | t₃
  deriving DecidableEq

namespace ToyExample

instance : Fintype ToyExample :=
  Fintype.ofList [s, a, b, c, t₁, t₂, t₃] (by intro x; cases x <;> simp)

/-- Adjacency of the seven-vertex graph. -/
def adjB : ToyExample → ToyExample → Bool
  | s, a | s, b | s, c | a, s | b, s | c, s => true
  | a, t₁ | b, t₁ | t₁, a | t₁, b => true
  | a, t₂ | c, t₂ | t₂, a | t₂, c => true
  | b, t₃ | c, t₃ | t₃, b | t₃, c => true
  | _, _ => false

/-- The graph of Figure `fig:coding-example`. -/
def graph : SimpleGraph ToyExample where
  Adj x y := adjB x y = true
  symm := ⟨fun x y h => by cases x <;> cases y <;> simp_all [adjB]⟩
  loopless := ⟨fun x h => by cases x <;> simp_all [adjB]⟩

@[simp] theorem graph_adj (x y : ToyExample) : graph.Adj x y ↔ adjB x y = true := Iff.rfl

instance : DecidableRel graph.Adj := fun x y => decidable_of_iff _ (graph_adj x y).symm

end ToyExample

open ToyExample

theorem ToyExample.reachable (x : ToyExample) : graph.Reachable s x := by
  have h1 : graph.Adj s a := by decide
  cases x
  · rfl
  · exact (show graph.Adj s a by decide).reachable
  · exact (show graph.Adj s b by decide).reachable
  · exact (show graph.Adj s c by decide).reachable
  · exact h1.reachable.trans (show graph.Adj a t₁ by decide).reachable
  · exact h1.reachable.trans (show graph.Adj a t₂ by decide).reachable
  · exact (show graph.Adj s b by decide).reachable.trans (show graph.Adj b t₃ by decide).reachable

instance : Nonempty ToyExample := ⟨s⟩

theorem ToyExample.connected : graph.Connected :=
  ⟨fun x y => (ToyExample.reachable x).symm.trans (ToyExample.reachable y)⟩

/-! ### The temporal benchmark -/

/-- The cut labels `0` at `s`, `1` at the relays and `2` at the sinks. -/
def ToyExample.label : ToyExample → ℕ
  | s => 0
  | a | b | c => 1
  | _ => 2

/-- At horizon `1` the sink `t₁` has temporal capacity `0` (it is two hops away). -/
theorem ToyExample.temporalMinCut_one : temporalMinCut graph s t₁ 1 = 0 := by
  have hl : IsCutLabel s t₁ 1 ToyExample.label := ⟨rfl, rfl, by intro u; cases u <;> decide⟩
  have := temporalMinCut_le_labelCost graph hl
  have h0 : labelCost graph ToyExample.label = 0 := by decide
  omega

/-- `τ ≥ 2`. -/
theorem ToyExample.two_le_tau : 2 ≤ tau graph s 2 := by
  by_contra h
  push Not at h
  have h1 := tau_mem ToyExample.connected (s := s) (k := 2) (by norm_num) t₁ (by decide)
  have h2 := temporalMinCut_mono (G := graph) (s := s) (v := t₁) (by decide)
    (show tau graph s 2 ≤ 1 by omega)
  rw [ToyExample.temporalMinCut_one] at h2
  omega

/-! ### Coding in two rounds over every finite field -/

variable (F : Type) [Field F]

/-- The symbols received by the relays in round `0`: `m₁`, `m₂` and `m₁ + m₂`. -/
def ToyExample.relayVec : ToyExample → (Fin 2 → F)
  | a => Pi.single 0 1
  | b => Pi.single 1 1
  | c => Pi.single 0 1 + Pi.single 1 1
  | _ => 0

/-- The symbols received by the relays in round `1`: `m₂`, `m₁` and `m₁`. -/
def ToyExample.relayVec' : ToyExample → (Fin 2 → F)
  | a => Pi.single 1 1
  | b | c => Pi.single 0 1
  | _ => 0

/-- Round `0`: `s` sends `m₁, m₂, m₁ + m₂` to the relays; round `1`: every relay forwards its
symbol to all its neighbours, and `s` sends `m₂, m₁, m₁` to the relays. -/
def ToyExample.code : Code ToyExample F 2 := fun e =>
  if e.2.2 = 0 ∧ e.1 = s then ToyExample.relayVec F e.2.1
  else if e.2.2 = 1 ∧ e.1 = s then ToyExample.relayVec' F e.2.1
  else if e.2.2 = 1 then ToyExample.relayVec F e.1 else 0

variable {F}

theorem ToyExample.code_isValid : IsValidCode graph s 2 (ToyExample.code F) := by
  rintro ⟨u, w, t⟩ ht
  simp only at ht ⊢
  by_cases hu : u = s
  · subst hu; rw [knowledge_source_eq_top]; trivial
  interval_cases t
  · simp [ToyExample.code, hu, zero_mem]
  · simp only [ToyExample.code, one_ne_zero, if_false, hu, and_false, if_true]
    have hrel : ∀ x, graph.Adj s x → ToyExample.relayVec F x = ToyExample.code F (s, x, 0) := by
      intro x _; simp [ToyExample.code]
    cases u
    · exact absurd rfl hu
    all_goals first
      | (rw [hrel _ (by decide)]; exact mem_knowledge_of_adj _ (by decide) (by norm_num))
      | simp [ToyExample.relayVec, zero_mem]

theorem ToyExample.top_of_singles {K : Submodule F (Fin 2 → F)} (h0 : Pi.single 0 1 ∈ K)
    (h1 : Pi.single 1 1 ∈ K) : K = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun F (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem ToyExample.knowledge_two (v : ToyExample) :
    knowledge graph s (ToyExample.code F) v 2 = ⊤ := by
  have hm : ∀ {u w : ToyExample} (t : ℕ), graph.Adj u w → t < 2 →
      ToyExample.code F (u, w, t) ∈ knowledge graph s (ToyExample.code F) w 2 :=
    fun t h ht => mem_knowledge_of_adj _ h ht
  cases v
  · exact knowledge_source_eq_top _ _
  · refine ToyExample.top_of_singles ?_ ?_
    · simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := s) (w := a) 0 (by decide) (by norm_num)
    · simpa [ToyExample.code, ToyExample.relayVec'] using
        hm (u := s) (w := a) 1 (by decide) (by norm_num)
  · refine ToyExample.top_of_singles ?_ ?_
    · simpa [ToyExample.code, ToyExample.relayVec'] using
        hm (u := s) (w := b) 1 (by decide) (by norm_num)
    · simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := s) (w := b) 0 (by decide) (by norm_num)
  · have h0 : Pi.single 0 1 ∈ knowledge graph s (ToyExample.code F) c 2 := by
      simpa [ToyExample.code, ToyExample.relayVec'] using
        hm (u := s) (w := c) 1 (by decide) (by norm_num)
    have h01 : Pi.single 0 1 + Pi.single 1 1 ∈ knowledge graph s (ToyExample.code F) c 2 := by
      simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := s) (w := c) 0 (by decide) (by norm_num)
    refine ToyExample.top_of_singles h0 ?_
    simpa using Submodule.sub_mem _ h01 h0
  · refine ToyExample.top_of_singles ?_ ?_
    · simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := a) (w := t₁) 1 (by decide) (by norm_num)
    · simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := b) (w := t₁) 1 (by decide) (by norm_num)
  · have h0 : Pi.single 0 1 ∈ knowledge graph s (ToyExample.code F) t₂ 2 := by
      simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := a) (w := t₂) 1 (by decide) (by norm_num)
    have h01 : Pi.single 0 1 + Pi.single 1 1 ∈ knowledge graph s (ToyExample.code F) t₂ 2 := by
      simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := c) (w := t₂) 1 (by decide) (by norm_num)
    refine ToyExample.top_of_singles h0 ?_
    simpa using Submodule.sub_mem _ h01 h0
  · have h1 : Pi.single 1 1 ∈ knowledge graph s (ToyExample.code F) t₃ 2 := by
      simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := b) (w := t₃) 1 (by decide) (by norm_num)
    have h01 : Pi.single 0 1 + Pi.single 1 1 ∈ knowledge graph s (ToyExample.code F) t₃ 2 := by
      simpa [ToyExample.code, ToyExample.relayVec] using
        hm (u := c) (w := t₃) 1 (by decide) (by norm_num)
    refine ToyExample.top_of_singles ?_ h1
    simpa using Submodule.sub_mem _ h01 h1

/-- Over every finite field, `τ = CODE = 2`. -/
theorem ToyExample.codedTime_eq [Fintype F] : codedTime graph s F 2 = 2 ∧ tau graph s 2 = 2 := by
  have hC : codedTime graph s F 2 ≤ 2 :=
    codedTime_le_of_code ToyExample.code_isValid ToyExample.knowledge_two
  have hτ := tau_le_codedTime_of_connected ToyExample.connected s 2 (A := F) Fintype.one_lt_card
  have := ToyExample.two_le_tau
  omega

/-! ### Routing needs three rounds -/

/-- Decidability of `Knows` for concrete schedules. -/
@[instance_reducible]
def RoutingSchedule.knowsDecidable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (σ : RoutingSchedule V k) (s : V) :
    ∀ t w i, Decidable (σ.Knows G s t w i)
  | 0, w, _ => inferInstanceAs (Decidable (w = s))
  | t + 1, w, i => @instDecidableOr _ _ (knowsDecidable σ s t w i) inferInstance

attribute [local instance] RoutingSchedule.knowsDecidable

/-- Round `0`: `s` sends `m₁, m₂, m₁` to the relays; round `1`: every relay forwards its packet to
all its neighbours, and `s` sends `m₂, m₁, m₂` to the relays; round `2`: `a` sends `m₂` to `t₂`. -/
def ToyExample.sched : RoutingSchedule ToyExample 2 := ⟨fun u w t =>
  if graph.Adj u w then
    match t, u, w with
    | 0, s, a => some 0
    | 0, s, b => some 1
    | 0, s, c => some 0
    | 1, s, a => some 1
    | 1, s, b => some 0
    | 1, s, c => some 1
    | 1, a, _ => some 0
    | 1, b, _ => some 1
    | 1, c, _ => some 0
    | 2, a, t₂ => some 1
    | _, _, _ => none
  else none⟩

theorem ToyExample.sched_valid : ToyExample.sched.IsValid graph s 3 := by
  intro u w t i ht h
  interval_cases t <;> revert u w i <;> decide

theorem ToyExample.sched_completes : ToyExample.sched.Completes graph s 3 := by
  unfold RoutingSchedule.Completes; decide

/-- A packet held by a sink after two valid rounds was sent by `s` to one of its neighbours in
round `0`. -/
theorem ToyExample.knows_two {σ : RoutingSchedule ToyExample 2} (hσ : σ.IsValid graph s 2) {t : ToyExample}
    (ht : ¬ graph.Adj s t) (hts : t ≠ s) {i : Fin 2} (h : σ.Knows graph s 2 t i) :
    ∃ w, graph.Adj w t ∧ σ.send s w 0 = some i := by
  have hA : ∀ u i, σ.Knows graph s 1 u i → u = s ∨ σ.send s u 0 = some i := by
    intro u i h
    rcases h with h | ⟨w, -, hw⟩
    · exact Or.inl h
    · have := (hσ w u 0 i (by norm_num) hw).2
      change w = s at this
      subst this
      exact Or.inr hw
  rcases h with h | ⟨w, hadj, hw⟩
  · rcases hA t i h with h | h
    · exact absurd h hts
    · exact absurd (hσ s t 0 i (by norm_num) h).1 ht
  · rcases hA w i (hσ w t 1 i (by norm_num) hw).2 with rfl | h
    · exact absurd hadj ht
    · exact ⟨w, hadj, h⟩

/-- No routing schedule finishes within two rounds. -/
theorem ToyExample.not_completes_le_two {R : ℕ} (hR : R ≤ 2) (σ : RoutingSchedule ToyExample 2)
    (hσ : σ.IsValid graph s R) (hc : σ.Completes graph s R) : False := by
  interval_cases R
  · exact absurd (hc t₁ 0) (by change ¬ (t₁ = s); decide)
  · rcases hc t₁ 0 with h | ⟨w, hadj, hw⟩
    · exact absurd h (by change ¬ (t₁ = s); decide)
    · have := (hσ w t₁ 0 0 (by norm_num) hw).2
      change w = s at this
      subst this
      exact absurd hadj (by decide)
  · -- the three relays would need pairwise different packets
    have hpair : ∀ t x y, (∀ w, graph.Adj w t → w = x ∨ w = y) → ¬ graph.Adj s t → t ≠ s →
        σ.send s x 0 ≠ σ.send s y 0 ∧ σ.send s x 0 ≠ none ∧ σ.send s y 0 ≠ none := by
      intro t x y hnb ht hts
      obtain ⟨w₀, h₀, e₀⟩ := ToyExample.knows_two hσ ht hts (hc t 0)
      obtain ⟨w₁, h₁, e₁⟩ := ToyExample.knows_two hσ ht hts (hc t 1)
      rcases hnb w₀ h₀ with rfl | rfl <;> rcases hnb w₁ h₁ with rfl | rfl <;> simp_all
    have nb₁ : ∀ w, graph.Adj w t₁ → w = a ∨ w = b := by decide
    have nb₂ : ∀ w, graph.Adj w t₂ → w = a ∨ w = c := by decide
    have nb₃ : ∀ w, graph.Adj w t₃ → w = b ∨ w = c := by decide
    obtain ⟨h12, h1, h2⟩ := hpair t₁ a b nb₁ (by decide) (by decide)
    obtain ⟨h13, -, h3⟩ := hpair t₂ a c nb₂ (by decide) (by decide)
    obtain ⟨h23, -, -⟩ := hpair t₃ b c nb₃ (by decide) (by decide)
    obtain ⟨p₁, e₁⟩ := Option.ne_none_iff_exists'.1 h1
    obtain ⟨p₂, e₂⟩ := Option.ne_none_iff_exists'.1 h2
    obtain ⟨p₃, e₃⟩ := Option.ne_none_iff_exists'.1 h3
    rw [e₁, e₂] at h12
    rw [e₁, e₃] at h13
    rw [e₂, e₃] at h23
    simp only [ne_eq, Option.some.injEq] at h12 h13 h23
    clear e₁ e₂ e₃
    revert p₁ p₂ p₃
    decide

/-- `ROUTE = 3`. -/
theorem ToyExample.routingTime_eq : routingTime graph s 2 = 3 := by
  refine le_antisymm (Nat.sInf_le ⟨ToyExample.sched, ToyExample.sched_valid, ToyExample.sched_completes⟩) ?_
  refine le_csInf ⟨3, ToyExample.sched, ToyExample.sched_valid, ToyExample.sched_completes⟩ fun R ⟨σ, hσ, hc⟩ => ?_
  by_contra h
  exact ToyExample.not_completes_le_two (by omega) σ hσ hc

end CodingGap
