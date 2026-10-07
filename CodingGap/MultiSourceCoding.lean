import CodingGap.MaxFlow
import CodingGap.LowerBound
import CodingGap.Simulation

/-!
# Multi-source broadcast for coding schemes (Appendix `app:multiple-sources`)

If a coding scheme broadcasts `k` packets from `s` within `T` rounds, then for every initial
placement `src : Fin k → V` of the packets some multi-source coding scheme broadcasts them within
`2 T` rounds (`exists_multiSource_protocol`, `multiSourceCodedTime_le`).

As in the appendix, the scheme first gathers all packets at `s` within `T` rounds by routing and
then runs the given scheme. A coding scheme cannot be reversed in time, so the gathering schedule
comes from the cut condition instead. By `thm:lower`, `C_T(s,v) ≥ k` for every `v ≠ s`.

* `cutCap_ge`: in the *gathering network* — the time-expanded network `G[T]` (storage arcs of
  capacity `k`) with a super-source joined to `(u, 0)` by an arc of capacity `|src⁻¹(u)|` — every
  cut separating the super-source from `(s, T)` has capacity at least `k`. This is the cut argument
  of the appendix, with the time reversal applied to cuts instead of to paths.
* `exists_flow` (max-flow min-cut, `CodingGap.MaxFlow`) then gives an integral flow of value `k`,
  which `exists_gathering` splits time layer by time layer into one trajectory per packet: packet
  `j` starts at `src j`, ends at `s` at time `T`, moves only along edges, and no two packets cross
  the same directed edge in the same round.
* `gatherProtocol` forwards the packets along these trajectories during rounds `0, …, T - 1`
  and runs the given scheme during rounds `T, …, 2T - 1`.
-/

namespace CodingGap

open Finset MaxFlow

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

namespace Gather

/-- The number of packets initially held by `u`. -/
def cnt (src : Fin k → V) (u : V) : ℕ := (univ.filter fun i => src i = u).card

/-- The capacities of the gathering network on `Option (V × Fin (T + 1))`: `none` is the
super-source, `some (u, t)` is the vertex `(u, t)` of `G[T]`. -/
def cap (T : ℕ) (src : Fin k → V) : Option (V × Fin (T + 1)) → Option (V × Fin (T + 1)) → ℤ
  | none, some p => if p.2.val = 0 then cnt src p.1 else 0
  | some p, some q =>
      if q.2.val = p.2.val + 1 then (if p.1 = q.1 then k else if G.Adj p.1 q.1 then 1 else 0)
      else 0
  | _, _ => 0

variable {G} {T : ℕ} {src : Fin k → V}

theorem cap_nonneg (x y : Option (V × Fin (T + 1))) : 0 ≤ cap G T src x y := by
  rcases x with _ | p <;> rcases y with _ | q <;> simp only [cap] <;> (try split_ifs) <;> positivity

theorem cap_none_right (x : Option (V × Fin (T + 1))) : cap G T src x none = 0 := by
  rcases x with _ | p <;> rfl

theorem cap_some_some (u w : V) (t t' : Fin (T + 1)) :
    cap G T src (some (u, t)) (some (w, t')) =
      if t'.val = t.val + 1 then (if u = w then (k : ℤ) else if G.Adj u w then 1 else 0) else 0 :=
  rfl

theorem cap_none_some (u : V) (t : Fin (T + 1)) :
    cap G T src none (some (u, t)) = if t.val = 0 then (cnt src u : ℤ) else 0 := rfl

theorem sum_cnt (src : Fin k → V) : ∑ u, cnt src u = k := by
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin k))) (t := univ) (f := src)
    (fun _ _ => mem_univ _)
  simpa [cnt] using this.symm

theorem sum_ite_val_eq_zero {T : ℕ} (x : ℤ) :
    ∑ t : Fin (T + 1), (if t.val = 0 then x else 0) = x := by
  rw [Fin.sum_univ_succ]
  simp

theorem sum_cap_none : ∑ y, cap G T src none y = k := by
  rw [Fintype.sum_option, cap_none_right, zero_add, Fintype.sum_prod_type]
  simp only [cap_none_some, sum_ite_val_eq_zero]
  exact_mod_cast sum_cnt src

/-- A cut contains the capacity of any arc leaving it. -/
theorem le_cutCap {S : Finset (Option (V × Fin (T + 1)))} {x y : Option (V × Fin (T + 1))}
    (hx : x ∈ S) (hy : y ∉ S) : cap G T src x y ≤ cutCap (cap G T src) S := by
  unfold cutCap
  calc cap G T src x y ≤ ∑ y ∈ Sᶜ, cap G T src x y :=
        single_le_sum (fun _ _ => cap_nonneg _ _) (mem_compl.2 hy)
    _ ≤ _ := single_le_sum (f := fun x => ∑ y ∈ Sᶜ, cap G T src x y)
        (fun _ _ => sum_nonneg fun _ _ => cap_nonneg _ _) hx

/-- **The cut condition of the gathering network** (the cut argument of the appendix). If
`C_T(s,v) ≥ k` for every `v ≠ s`, every cut separating the super-source from `(s, T)` has capacity
at least `k`. -/
theorem cutCap_ge {s : V} (hcut : ∀ v, v ≠ s → k ≤ temporalMinCut G s v T)
    (S : Finset (Option (V × Fin (T + 1)))) (ha : none ∈ S) (hb : some (s, Fin.last T) ∉ S) :
    (k : ℤ) ≤ cutCap (cap G T src) S := by
  classical
  by_cases hA : ∀ j, some (src j, (0 : Fin (T + 1))) ∉ S
  · -- every arc out of the super-source leaves the cut
    calc (k : ℤ) = ∑ y, cap G T src none y := sum_cap_none.symm
      _ = ∑ y ∈ Sᶜ, cap G T src none y := by
        refine (sum_subset (subset_univ _) fun y _ hy => ?_).symm
        rw [mem_compl, not_not] at hy
        rcases y with _ | ⟨u, t⟩
        · exact cap_none_right _
        · rw [cap_none_some]
          split_ifs with ht
          · have ht0 : t = 0 := Fin.ext ht
            subst ht0
            have : (univ.filter fun i => src i = u) = ∅ := by
              ext j
              simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
              rintro rfl
              exact hA j hy
            simp [cnt, this]
          · rfl
      _ ≤ cutCap (cap G T src) S := by
        unfold cutCap
        exact single_le_sum (f := fun x => ∑ y ∈ Sᶜ, cap G T src x y)
          (fun _ _ => sum_nonneg fun _ _ => cap_nonneg _ _) ha
  push Not at hA
  obtain ⟨j, hj⟩ := hA
  by_cases hst : ∃ (u : V) (t t' : Fin (T + 1)), t'.val = t.val + 1 ∧ some (u, t) ∈ S ∧
      some (u, t') ∉ S
  · -- a storage arc of capacity `k` leaves the cut
    obtain ⟨u, t, t', htt, hin, hout⟩ := hst
    have := le_cutCap (G := G) (src := src) hin hout
    rwa [cap_some_some, if_pos htt, if_pos rfl] at this
  push Not at hst
  -- the cut is closed under storage arcs
  by_cases hjs : src j = s
  · exfalso
    have key : ∀ n (hn : n ≤ T), some (s, (⟨n, by omega⟩ : Fin (T + 1))) ∈ S := by
      intro n
      induction n with
      | zero => intro _; rw [← hjs]; exact hj
      | succ n ih => intro hn; exact hst s ⟨n, by omega⟩ ⟨n + 1, by omega⟩ rfl (ih (by omega))
    exact hb (key T le_rfl)
  -- the time reversal of the complement is a finite temporal cut of `G[T]`
  set v := src j
  let Sf : Set (V × ℕ) := {p | some (p.1, (⟨T - p.2, by omega⟩ : Fin (T + 1))) ∉ S}
  have hSf : IsTemporalCut s v T Sf := by
    refine ⟨?_, ?_, ?_⟩
    · change some (s, (⟨T - 0, _⟩ : Fin (T + 1))) ∉ S
      convert hb using 3
      simp [Fin.ext_iff]
    · change ¬ some (v, (⟨T - T, _⟩ : Fin (T + 1))) ∉ S
      rw [not_not]
      convert hj using 3
      ext; simp
    · intro u t ht h hcon
      exact h (hst u ⟨T - (t + 1), by omega⟩ ⟨T - t, by omega⟩ (by simp only; omega) hcon)
  have h1 : k ≤ cutCapacity G T Sf := (hcut v hjs).trans (temporalMinCut_le G hSf)
  -- every arc of the temporal cut is the reversal of an arc of capacity one leaving `S`
  let φ : V × V × ℕ → Option (V × Fin (T + 1)) × Option (V × Fin (T + 1)) := fun a =>
    (some (a.2.1, ⟨T - a.2.2 - 1, by omega⟩), some (a.1, ⟨T - a.2.2, by omega⟩))
  have hmem : ∀ a ∈ cutArcs G T Sf, a.2.2 < T ∧ G.Adj a.1 a.2.1 ∧ (φ a).1 ∈ S ∧ (φ a).2 ∉ S := by
    intro a ha
    simp only [cutArcs, commArcs, mem_filter, mem_product, mem_univ, mem_range, true_and] at ha
    obtain ⟨⟨ht, hadj⟩, hin, hout⟩ := ha
    refine ⟨ht, hadj, ?_, hin⟩
    have : some (a.2.1, (⟨T - (a.2.2 + 1), by omega⟩ : Fin (T + 1))) ∈ S := by
      simpa [Sf] using hout
    convert this using 4
  have hinj : Set.InjOn φ (cutArcs G T Sf) := by
    intro a ha b hb' hab
    have ha' := (hmem a ha).1
    have hb'' := (hmem b hb').1
    simp only [φ, Prod.mk.injEq, Option.some.injEq, Fin.mk.injEq] at hab
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hab
    exact Prod.ext h3 (Prod.ext h1 (by omega))
  calc (k : ℤ) ≤ (cutArcs G T Sf).card := by exact_mod_cast h1
    _ = ((cutArcs G T Sf).image φ).card := by rw [card_image_of_injOn hinj]
    _ = ∑ p ∈ (cutArcs G T Sf).image φ, cap G T src p.1 p.2 := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine sum_congr rfl fun p hp => ?_
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
      obtain ⟨ht, hadj, -, -⟩ := hmem a ha
      simp only [φ, cap_some_some]
      rw [if_pos (by omega), if_neg hadj.ne.symm, if_pos hadj.symm]
    _ ≤ ∑ p ∈ S ×ˢ Sᶜ, cap G T src p.1 p.2 := by
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => cap_nonneg _ _
      intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
      obtain ⟨-, -, h1, h2⟩ := hmem a ha
      exact mem_product.2 ⟨h1, mem_compl.2 h2⟩
    _ = cutCap (cap G T src) S := by rw [sum_product]; rfl

/-! ### Splitting the flow into packet trajectories -/

/-- A finite set of size `∑ b, n b` can be split into parts of sizes `n b`. -/
theorem exists_split {ι β : Type*} [DecidableEq β] [Fintype β] [Nonempty β] (Q : Finset ι)
    (n : β → ℕ) (h : Q.card = ∑ b, n b) :
    ∃ φ : ι → β, ∀ b, (Q.filter fun i => φ i = b).card = n b := by
  classical
  have hc : Fintype.card Q = Fintype.card (Σ b, Fin (n b)) := by simp [h]
  let e : Q ≃ Σ b, Fin (n b) := Fintype.equivOfCardEq hc
  refine ⟨fun i => if hi : i ∈ Q then (e ⟨i, hi⟩).1 else Classical.arbitrary β, fun b => ?_⟩
  calc (Q.filter fun i => (if hi : i ∈ Q then (e ⟨i, hi⟩).1 else Classical.arbitrary β) = b).card
      = (univ.filter fun x : Q => (e x).1 = b).card := by
        refine card_bij (fun i hi => ⟨i, (mem_filter.1 hi).1⟩) (fun i hi => ?_)
          (fun i _ j _ h => by simpa using h) (fun x hx => ⟨x.1, ?_, rfl⟩)
        · obtain ⟨hiQ, hib⟩ := mem_filter.1 hi
          simpa [dif_pos hiQ] using hib
        · simp only [mem_filter, mem_univ, true_and] at hx
          simpa [dif_pos x.2] using hx
    _ = (univ.filter fun σ : Σ b, Fin (n b) => σ.1 = b).card :=
        card_equiv e fun x => by simp
    _ = n b := by
        have : (univ.filter fun σ : Σ b, Fin (n b) => σ.1 = b) =
            (univ : Finset (Fin (n b))).map ⟨Sigma.mk b, sigma_mk_injective⟩ := by
          ext ⟨b', i⟩
          simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
          constructor
          · rintro rfl; exact ⟨i, rfl⟩
          · rintro ⟨i', h⟩; exact (Sigma.mk.inj_iff.1 h).1.symm
        rw [this, card_map, card_univ, Fintype.card_fin]

variable (T)

/-- The time `t` as an element of `Fin (T + 1)` (capped at `T`). -/
def tm (t : ℕ) : Fin (T + 1) := ⟨min t T, by omega⟩

variable {T}

theorem tm_val {t : ℕ} (h : t ≤ T) : (tm T t).val = t := by simp [tm, h]

variable (f : Option (V × Fin (T + 1)) → Option (V × Fin (T + 1)) → ℤ)

/-- The flow entering `(u, t)`. -/
def inflow (t : ℕ) (u : V) : ℤ := ∑ x, f x (some (u, tm T t))

/-- The flow on the arc `(u, t) → (w, t + 1)`. -/
def flowOf (t : ℕ) (u w : V) : ℤ := f (some (u, tm T t)) (some (w, tm T (t + 1)))

/-- `pos'` moves the packets from their positions `pos` at time `t` as prescribed by the flow. -/
def StepOK (t : ℕ) (pos pos' : Fin k → V) : Prop :=
  ∀ u w, ((univ.filter fun j => pos j = u ∧ pos' j = w).card : ℤ) = flowOf f t u w

variable (src)

open Classical in
/-- The packet trajectories read off the flow, one time layer at a time. -/
noncomputable def traj : ℕ → Fin k → V
  | 0 => src
  | t + 1 => if h : ∃ pos', StepOK f t (traj t) pos' then h.choose else traj t

variable {f src} {s : V}
  (hf : IsFlow (cap G T src) none (some (s, Fin.last T)) f)
include hf

theorem flow_eq_zero {x y} (h : cap G T src x y = 0) : f x y = 0 :=
  le_antisymm (h ▸ hf.le_cap x y) (hf.nonneg x y)

/-- Arcs out of `(u, t)` all go to time `t + 1`. -/
theorem sum_out {t : ℕ} (ht : t < T) (u : V) :
    ∑ y, f (some (u, tm T t)) y = ∑ w, flowOf f t u w := by
  rw [Fintype.sum_option, flow_eq_zero hf (cap_none_right _), zero_add, Fintype.sum_prod_type]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_eq_single (tm T (t + 1))]
  · rfl
  · intro t' _ ht'
    refine flow_eq_zero hf ?_
    rw [cap_some_some, if_neg]
    intro h
    exact ht' (Fin.ext (by rw [h, tm_val ht.le, tm_val ht]))
  · simp

/-- Arcs into `(w, t + 1)` all come from time `t`. -/
theorem inflow_succ {t : ℕ} (ht : t < T) (w : V) :
    inflow f (t + 1) w = ∑ u, flowOf f t u w := by
  unfold inflow
  rw [Fintype.sum_option, flow_eq_zero hf (by rw [cap_none_some, if_neg (by rw [tm_val ht]; omega)]),
    zero_add, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_eq_single (tm T t)]
  · rfl
  · intro t' _ ht'
    refine flow_eq_zero hf ?_
    rw [cap_some_some, if_neg]
    intro h
    exact ht' (Fin.ext (by rw [tm_val ht.le]; rw [tm_val ht] at h; omega))
  · simp

/-- No arc leaves the last layer. -/
theorem sum_out_last (u : V) : ∑ y, f (some (u, tm T T)) y = 0 := by
  rw [Fintype.sum_option, flow_eq_zero hf (cap_none_right _), zero_add]
  refine sum_eq_zero fun ⟨w, t'⟩ _ => flow_eq_zero hf ?_
  rw [cap_some_some, if_neg]
  rw [tm_val le_rfl]
  omega

/-- Conservation at `(u, t)`, which is not the sink. -/
theorem sum_out_eq_inflow {t : ℕ} (ht : t ≤ T) {u : V} (hne : ¬ (u = s ∧ t = T)) :
    ∑ y, f (some (u, tm T t)) y = inflow f t u := by
  have := hf.conserve (some (u, tm T t)) (by simp) (by
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact hne ⟨h.1, by rw [← tm_val ht, h.2]; simp⟩)
  unfold outflow at this
  unfold inflow
  linarith

/-- A maximum flow saturates the arcs out of the super-source. -/
theorem inflow_zero (hval : (k : ℤ) ≤ outflow f none) (u : V) :
    inflow f 0 u = cnt src u := by
  have hin : ∀ y, f y none = 0 := fun y => flow_eq_zero hf (cap_none_right y)
  have hsum : ∑ y, (cap G T src none y - f none y) = 0 := by
    refine le_antisymm ?_ (sum_nonneg fun y _ => sub_nonneg.2 (hf.le_cap _ _))
    rw [sum_sub_distrib, sum_cap_none]
    unfold outflow at hval
    simp only [hin, sum_const_zero, sub_zero] at hval
    linarith
  have hsat : ∀ y, f none y = cap G T src none y := fun y => by
    have := (sum_eq_zero_iff_of_nonneg fun y _ => sub_nonneg.2 (hf.le_cap none y)).1 hsum y
      (mem_univ _)
    linarith
  unfold inflow
  rw [Fintype.sum_option, hsat, cap_none_some, if_pos (by simp [tm]),
    sum_eq_zero fun x _ => flow_eq_zero hf ?_, add_zero]
  rw [cap_some_some, if_neg (by simp [tm])]

theorem exists_step {t : ℕ} (ht : t < T) {pos : Fin k → V}
    (hpos : ∀ u, ((univ.filter fun j => pos j = u).card : ℤ) = inflow f t u) :
    ∃ pos', StepOK f t pos pos' := by
  classical
  have hn : ∀ u, (univ.filter fun j => pos j = u).card = ∑ w, (flowOf f t u w).toNat := by
    intro u
    have h1 := hpos u
    rw [← sum_out_eq_inflow hf ht.le (by omega), sum_out hf ht] at h1
    have h2 : ((∑ w, (flowOf f t u w).toNat : ℕ) : ℤ) = ∑ w, flowOf f t u w := by
      push_cast
      exact sum_congr rfl fun w _ => Int.toNat_of_nonneg (hf.nonneg _ _)
    exact_mod_cast h1.trans h2.symm
  have : Nonempty V := ⟨s⟩
  choose φ hφ using fun u => exists_split _ _ (hn u)
  refine ⟨fun j => φ (pos j) j, fun u w => ?_⟩
  have : (univ.filter fun j => pos j = u ∧ φ (pos j) j = w) =
      ((univ.filter fun j => pos j = u).filter fun j => φ u j = w) := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  rw [this, hφ u w]
  exact Int.toNat_of_nonneg (hf.nonneg _ _)

theorem traj_spec (hval : (k : ℤ) ≤ outflow f none) :
    ∀ t ≤ T, (∀ u, ((univ.filter fun j => traj src f t j = u).card : ℤ) = inflow f t u) ∧
      (t < T → StepOK f t (traj src f t) (traj src f (t + 1))) := by
  intro t
  induction t with
  | zero =>
    intro _
    have h0 : ∀ u, ((univ.filter fun j => traj src f 0 j = u).card : ℤ) = inflow f 0 u :=
      fun u => by rw [inflow_zero hf hval]; rfl
    refine ⟨h0, fun hT => ?_⟩
    have hex := exists_step hf hT h0
    have e : traj src f (0 + 1) = hex.choose := by rw [traj, dif_pos hex]
    rw [e]
    exact hex.choose_spec
  | succ t ih =>
    intro ht
    obtain ⟨-, hstep⟩ := ih (by omega)
    have hstep := hstep (by omega)
    have hcount : ∀ w, ((univ.filter fun j => traj src f (t + 1) j = w).card : ℤ) =
        inflow f (t + 1) w := by
      intro w
      rw [inflow_succ hf (by omega), card_eq_sum_card_fiberwise (f := traj src f t)
        (t := univ) (fun _ _ => mem_univ _)]
      push_cast
      refine sum_congr rfl fun u _ => ?_
      rw [← hstep u w, filter_filter]
      congr 2
      ext j
      simp only [mem_filter, mem_univ, true_and]
      exact and_comm
    refine ⟨hcount, fun hT => ?_⟩
    have hex := exists_step hf hT hcount
    have e : traj src f (t + 1 + 1) = hex.choose := by rw [traj, dif_pos hex]
    rw [e]
    exact hex.choose_spec

end Gather

open Gather in
/-- **Gathering.** If `C_T(s,v) ≥ k` for every `v ≠ s`, then for every initial placement `src` of
the `k` packets there are trajectories `pos t j` (the position of packet `j` at time `t`) that
start at `src`, end at `s` at time `T`, move only along edges, and never move two packets along
the same directed edge in the same round. -/
theorem exists_gathering {s : V} {T : ℕ} (hcut : ∀ v, v ≠ s → k ≤ temporalMinCut G s v T)
    (src : Fin k → V) :
    ∃ pos : ℕ → Fin k → V, pos 0 = src ∧ (∀ j, pos T j = s) ∧
      ∀ t < T, ∀ j, pos t j ≠ pos (t + 1) j → G.Adj (pos t j) (pos (t + 1) j) ∧
        ∀ j', pos t j' = pos t j → pos (t + 1) j' = pos (t + 1) j → j' = j := by
  classical
  obtain ⟨f, hf, hval⟩ := exists_flow (a := none) (b := some (s, Fin.last T)) (cap_nonneg (G := G) (src := src))
    (by simp) k (fun S ha hb => cutCap_ge hcut S ha hb)
  have spec := traj_spec hf hval
  refine ⟨traj src f, rfl, fun j => ?_, fun t ht j hne => ?_⟩
  · by_contra hj
    have h1 := (spec T le_rfl).1 (traj src f T j)
    rw [← sum_out_eq_inflow hf le_rfl (by tauto), sum_out_last hf] at h1
    have : j ∈ univ.filter fun j' => traj src f T j' = traj src f T j := by simp
    have := card_pos.2 ⟨j, this⟩
    omega
  · set u := traj src f t j
    set w := traj src f (t + 1) j
    have hstep := (spec t ht.le).2 ht u w
    let C := univ.filter fun j' => traj src f t j' = u ∧ traj src f (t + 1) j' = w
    have hjC : j ∈ C := by simp [C, u, w]
    have hcap : ((C.card : ℕ) : ℤ) ≤ if G.Adj u w then 1 else 0 := by
      have := hf.le_cap (some (u, tm T t)) (some (w, tm T (t + 1)))
      rw [cap_some_some, if_pos (by rw [tm_val ht, tm_val ht.le]), if_neg hne] at this
      exact hstep ▸ this
    have hpos := card_pos.2 ⟨j, hjC⟩
    split_ifs at hcap with hadj
    · refine ⟨hadj, fun j' h1 h2 => ?_⟩
      have hj'C : j' ∈ C := by simp [C, h1, h2]
      exact card_le_one.1 (by exact_mod_cast hcap) j' hj'C j hjC
    · omega

/-! ### The multi-source coding scheme -/

namespace Gather

variable {A : Type} (P : Protocol V A k) (s : V) (T : ℕ) (pos : ℕ → Fin k → V) (d : A)

/-- The state in which `w` starts the given scheme at time `T`, given the packets it holds. -/
def start (w : V) (st : Fin k → Option A) : P.State :=
  if w = s then P.initSource fun i => (st i).getD d else P.init w

open Classical in
/-- Gather the packets at `s` along the trajectories `pos` during rounds `0, …, T - 1`, then run
`P` during rounds `T, …, 2T - 1`. A state is the list of packets held so far together with a
state of `P`. -/
noncomputable def gatherProtocol : MultiProtocol V A k where
  State := (Fin k → Option A) × P.State
  init u st := (st, if T = 0 then start P s d u st else P.init u)
  send u w t σ :=
    if t < T then
      if h : ∃ j, pos t j = u ∧ pos (t + 1) j = w then (σ.1 h.choose).getD d else d
    else P.send u w (t - T) σ.2
  step w t σ m :=
    let st : Fin k → Option A :=
      if t < T then fun j => if pos (t + 1) j = w ∧ pos t j ≠ w then m (pos t j) else σ.1 j
      else σ.1
    (st, if t + 1 < T then σ.2 else if t + 1 = T then start P s d w st
      else P.step w (t - T) σ.2 m)
  output v σ := P.output v σ.2

variable {P s T pos d} {src : Fin k → V} (X : Fin k → A)
  (hpos0 : pos 0 = src)
  (hmove : ∀ t < T, ∀ j, pos t j ≠ pos (t + 1) j → G.Adj (pos t j) (pos (t + 1) j) ∧
    ∀ j', pos t j' = pos t j → pos (t + 1) j' = pos (t + 1) j → j' = j)

theorem run_snd_succ (t : ℕ) (w : V) :
    ((gatherProtocol P s T pos d).run G src X (t + 1) w).2 =
      if t + 1 < T then ((gatherProtocol P s T pos d).run G src X t w).2
      else if t + 1 = T then start P s d w ((gatherProtocol P s T pos d).run G src X (t + 1) w).1
      else P.step w (t - T) ((gatherProtocol P s T pos d).run G src X t w).2
        (fun u => if G.Adj u w then
          some ((gatherProtocol P s T pos d).send u w t
            ((gatherProtocol P s T pos d).run G src X t u)) else none) := rfl

include hpos0 hmove in
/-- During the gathering phase, packet `j` is held by `pos t j` at time `t`. -/
theorem run_fst_pos : ∀ t ≤ T, ∀ j,
    ((gatherProtocol P s T pos d).run G src X t (pos t j)).1 j = some (X j) := by
  intro t
  induction t with
  | zero =>
    intro _ j
    subst hpos0
    simp [MultiProtocol.run, gatherProtocol, MultiProtocol.held]
  | succ t ih =>
    intro ht j
    have ih := ih (by omega)
    simp only [MultiProtocol.run, gatherProtocol, if_pos (show t < T by omega)]
    by_cases hne : pos t j = pos (t + 1) j
    · simp only [hne, ne_eq, not_true_eq_false, and_false, if_false]
      rw [← hne]
      exact ih j
    · obtain ⟨hadj, huniq⟩ := hmove t (by omega) j hne
      simp only [ne_eq, hne, not_false_eq_true, and_self, if_true, if_pos hadj]
      have hex : ∃ j', pos t j' = pos t j ∧ pos (t + 1) j' = pos (t + 1) j := ⟨j, rfl, rfl⟩
      rw [dif_pos hex, huniq _ hex.choose_spec.1 hex.choose_spec.2]
      change some ((((gatherProtocol P s T pos d).run G src X t (pos t j)).1 j).getD d) =
        some (X j)
      rw [ih j]
      rfl

include hpos0 hmove in
/-- At time `T` every vertex starts `P`, the source holding all packets. -/
theorem run_snd_T (hposT : ∀ j, pos T j = s) (u : V) :
    ((gatherProtocol P s T pos d).run G src X T u).2 = P.run G s X 0 u := by
  have hfull : ∀ i, ((gatherProtocol P s T pos d).run G src X T s).1 i = some (X i) := by
    intro i
    have := run_fst_pos (P := P) (s := s) (d := d) G X hpos0 hmove T le_rfl i
    rwa [hposT] at this
  cases T with
  | zero =>
    simp only [MultiProtocol.run, gatherProtocol, if_true, start, Protocol.run]
    split_ifs with hu
    · subst hu
      congr 1
      funext i
      have := hfull i
      simp only [MultiProtocol.run, gatherProtocol] at this
      rw [this]
      rfl
    · rfl
  | succ T =>
    rw [run_snd_succ, if_neg (lt_irrefl _), if_pos rfl]
    simp only [start, Protocol.run]
    split_ifs with hu
    · subst hu
      congr 1
      funext i
      rw [hfull i]
      rfl
    · rfl

include hpos0 hmove in
/-- After time `T`, the scheme runs `P`. -/
theorem run_snd_late (hposT : ∀ j, pos T j = s) :
    ∀ t u, ((gatherProtocol P s T pos d).run G src X (T + t) u).2 = P.run G s X t u := by
  intro t
  induction t with
  | zero => exact run_snd_T (P := P) (d := d) G X hpos0 hmove hposT
  | succ t ih =>
    intro w
    rw [← add_assoc, run_snd_succ, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
      ih w]
    simp only [Protocol.run]
    congr 1
    funext u
    split_ifs
    · congr 1
      change (if T + t < T then _ else
        P.send u w (T + t - T) ((gatherProtocol P s T pos d).run G src X (T + t) u).2) = _
      rw [if_neg (by omega), Nat.add_sub_cancel_left, ih u]
    · rfl

end Gather

open Gather in
/-- **Multi-source reduction for coding schemes, protocol form.** Over an alphabet with at least
two symbols, if a coding scheme broadcasts `k` packets from `s` within `T` rounds, then for every
initial placement `src` of the packets some multi-source coding scheme broadcasts them within
`2 T` rounds. -/
theorem exists_multiSource_protocol {A : Type} [Fintype A] (hA : 2 ≤ Fintype.card A)
    (P : Protocol V A k) {s : V} {T : ℕ} (hP : ∀ X, P.Broadcasts G s X T) (src : Fin k → V) :
    ∃ Q : MultiProtocol V A k, ∀ X, Q.Broadcasts G src X (2 * T) := by
  have hcut : ∀ v, v ≠ s → k ≤ temporalMinCut G s v T := fun v hv =>
    le_temporalMinCut_of_recovers G hA P hv fun X => hP X v
  obtain ⟨pos, hpos0, hposT, hmove⟩ := exists_gathering G hcut src
  have : Nonempty A := Fintype.card_pos_iff.1 (by omega)
  refine ⟨gatherProtocol P s T pos (Classical.arbitrary A), fun X v => ?_⟩
  change P.output v (_ : _ × _).2 = X
  rw [two_mul, run_snd_late (P := P) (d := Classical.arbitrary A) G X hpos0 hmove hposT]
  exact hP X v

/-- **Multi-source reduction for coding schemes.** In a connected graph, over an alphabet with at
least two symbols, `CODE(G, src, k) ≤ 2 CODE(G, s, k)` for every source `s` and every initial
placement `src` of the packets. -/
theorem multiSourceCodedTime_le (hG : G.Connected) (s : V) (src : Fin k → V) {A : Type}
    [Fintype A] (hA : 2 ≤ Fintype.card A) :
    multiSourceCodedTime G src A ≤ 2 * codedTime G s A k := by
  have : Nonempty A := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨R, σ, hv, hc⟩ := exists_routingSchedule hG s k
  obtain ⟨P, hP⟩ := Nat.sInf_mem (s := {T | ∃ P : Protocol V A k, ∀ X, P.Broadcasts G s X T})
    ⟨R, σ.toProtocol A, σ.broadcasts_toProtocol hv hc⟩
  obtain ⟨Q, hQ⟩ := exists_multiSource_protocol G hA P hP src
  exact Nat.sInf_le ⟨Q, hQ⟩

end CodingGap
