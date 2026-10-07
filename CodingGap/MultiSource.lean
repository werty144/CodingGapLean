import CodingGap.Pipeline

/-!
# Multi-source broadcast (Appendix `app:multiple-sources`)

If a routing schedule broadcasts `k` packets from `s` within `R` rounds, then for every initial
placement `src : Fin k → V` of the packets there is a routing schedule broadcasting them within
`2 R` rounds (`exists_multiSource_schedule`, `multiSourceRoutingTime_le`).

The schedule first gathers all packets at `s` within `R` rounds and then runs the given schedule.
For routing, the gathering paths can be read off the given schedule itself, without the flow
argument of the appendix (which is needed only for coding schemes): packet `i` reaches `src i`
by time `R`, so tracing its copies backwards gives a temporal path from `(s, 0)` to `(src i, R)`
(`RoutingSchedule.back`) that only uses transmissions of packet `i`. A transmission carries a
single packet, so these paths are arc-disjoint. Reversed in time, they bring every packet from
`src i` to `s` within `R` rounds.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

namespace RoutingSchedule

variable (σ : RoutingSchedule V k) (G) (s : V)

open Classical in
/-- One step back along the copies of packet `i`: a vertex `u` from which `w` received packet `i`
in round `t`, if `w` did not already hold it at time `t`; otherwise `w` itself. -/
noncomputable def prev (t : ℕ) (w : V) (i : Fin k) : V :=
  if h : ∃ u, G.Adj u w ∧ σ.send u w t = some i ∧ σ.Knows G s t u i ∧ ¬ σ.Knows G s t w i then
    h.choose
  else w

/-- `back R src i d`: where the copy of packet `i` that reaches `src i` at time `R` is at time
`R - d`. -/
noncomputable def back (R : ℕ) (src : Fin k → V) (i : Fin k) : ℕ → V
  | 0 => src i
  | d + 1 => σ.prev G s (R - (d + 1)) (back R src i d) i

/-- Packet `i` moves from `w` to `u` in round `t` of the gathering phase. -/
def Gathers (R : ℕ) (src : Fin k → V) (w u : V) (t : ℕ) (i : Fin k) : Prop :=
  σ.back G s R src i t = w ∧ σ.back G s R src i (t + 1) = u ∧ w ≠ u

open Classical in
/-- The multi-source schedule: gather every packet at `s` along the reversed paths `back` during
rounds `0, …, R - 1`, then run `σ` during rounds `R, …, 2R - 1`. -/
noncomputable def gatherThen (R : ℕ) (src : Fin k → V) : RoutingSchedule V k where
  send w u t :=
    if t < R then
      if h : ∃ i, σ.Gathers G s R src w u t i then some h.choose else none
    else σ.send w u (t - R)

variable {σ G s}

theorem prev_spec (t : ℕ) (w : V) (i : Fin k) :
    σ.prev G s t w i = w ∨
      (G.Adj (σ.prev G s t w i) w ∧ σ.send (σ.prev G s t w i) w t = some i) := by
  unfold prev
  split_ifs with h
  · exact Or.inr ⟨h.choose_spec.1, h.choose_spec.2.1⟩
  · exact Or.inl rfl

theorem knows_prev {R t : ℕ} (hv : σ.IsValid G s R) (ht : t < R) {w : V} {i : Fin k}
    (hk : σ.Knows G s (t + 1) w i) : σ.Knows G s t (σ.prev G s t w i) i := by
  unfold prev
  split_ifs with h
  · exact h.choose_spec.2.2.1
  · rcases hk with hk | ⟨u, hadj, hsend⟩
    · exact hk
    · by_contra hw
      exact h ⟨u, hadj, hsend, (hv u w t i ht hsend).2, hw⟩

theorem knows_back {R : ℕ} (hv : σ.IsValid G s R) {src : Fin k → V}
    (hsrc : ∀ i, σ.Knows G s R (src i) i) (i : Fin k) :
    ∀ d ≤ R, σ.Knows G s (R - d) (σ.back G s R src i d) i := by
  intro d
  induction d with
  | zero => intro _; exact hsrc i
  | succ d ih =>
    intro hd
    have h := ih (by omega)
    rw [show R - d = R - (d + 1) + 1 by omega] at h
    exact knows_prev hv (by omega) h

theorem back_spec (R : ℕ) (src : Fin k → V) (i : Fin k) (d : ℕ) :
    σ.back G s R src i (d + 1) = σ.back G s R src i d ∨
      (G.Adj (σ.back G s R src i (d + 1)) (σ.back G s R src i d) ∧
        σ.send (σ.back G s R src i (d + 1)) (σ.back G s R src i d) (R - (d + 1)) = some i) :=
  prev_spec _ _ _

theorem back_eq_source {R : ℕ} (hv : σ.IsValid G s R) {src : Fin k → V}
    (hsrc : ∀ i, σ.Knows G s R (src i) i) (i : Fin k) : σ.back G s R src i R = s := by
  have := knows_back hv hsrc i R le_rfl
  rwa [Nat.sub_self] at this

/-- A gathering step reverses a transmission of the given schedule, so at most one packet moves
along a channel in a round. -/
theorem gathers_unique {R : ℕ} {src : Fin k → V} {w u : V} {t : ℕ} {i j : Fin k}
    (hi : σ.Gathers G s R src w u t i) (hj : σ.Gathers G s R src w u t j) : i = j := by
  obtain ⟨hi1, hi2, hne⟩ := hi
  obtain ⟨hj1, hj2, -⟩ := hj
  have key : ∀ m, σ.Gathers G s R src w u t m → σ.send u w (R - (t + 1)) = some m := by
    rintro m ⟨h1, h2, -⟩
    rcases back_spec (σ := σ) (G := G) (s := s) R src m t with h | ⟨-, h⟩
    · exact absurd (h1 ▸ h2 ▸ h).symm hne
    · rwa [h1, h2] at h
  have := (key i ⟨hi1, hi2, hne⟩).symm.trans (key j ⟨hj1, hj2, hne⟩)
  exact Option.some_injective _ this

theorem gatherThen_send_of_gathers {R : ℕ} {src : Fin k → V} {w u : V} {t : ℕ} {i : Fin k}
    (ht : t < R) (h : σ.Gathers G s R src w u t i) :
    (σ.gatherThen G s R src).send w u t = some i := by
  have hex : ∃ i, σ.Gathers G s R src w u t i := ⟨i, h⟩
  simp only [gatherThen, if_pos ht, dif_pos hex]
  exact congrArg some (gathers_unique hex.choose_spec h)

theorem gatherThen_send_late {R : ℕ} {src : Fin k → V} {w u : V} {t : ℕ} :
    (σ.gatherThen G s R src).send w u (R + t) = σ.send w u t := by
  simp [gatherThen]

/-- During the gathering phase, at time `t` packet `i` is held by `back i t`. -/
theorem knowsFrom_back {R : ℕ} {src : Fin k → V} (i : Fin k) :
    ∀ t ≤ R, (σ.gatherThen G s R src).KnowsFrom G src t (σ.back G s R src i t) i := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have h := ih (by omega)
    by_cases heq : σ.back G s R src i t = σ.back G s R src i (t + 1)
    · rw [← heq]; exact Or.inl h
    · refine Or.inr ⟨σ.back G s R src i t, ?_, gatherThen_send_of_gathers (by omega)
        ⟨rfl, rfl, heq⟩⟩
      rcases back_spec (σ := σ) (G := G) (s := s) R src i t with h' | ⟨hadj, -⟩
      · exact absurd h'.symm heq
      · exact hadj.symm

/-- After the gathering phase, the schedule knows at least what `σ` knows, shifted by `R`. -/
theorem knowsFrom_late {R : ℕ} (hv : σ.IsValid G s R) {src : Fin k → V}
    (hsrc : ∀ i, σ.Knows G s R (src i) i) :
    ∀ t u i, σ.Knows G s t u i → (σ.gatherThen G s R src).KnowsFrom G src (R + t) u i := by
  intro t
  induction t with
  | zero =>
    intro u i h
    change u = s at h
    subst h
    have := knowsFrom_back (σ := σ) (G := G) (s := u) (R := R) (src := src) i R le_rfl
    rwa [back_eq_source hv hsrc] at this
  | succ t ih =>
    intro w i h
    rcases h with h | ⟨u, hadj, hsend⟩
    · exact Or.inl (ih w i h)
    · exact Or.inr ⟨u, hadj, gatherThen_send_late.trans hsend⟩

theorem isValidFrom_gatherThen {R : ℕ} (hv : σ.IsValid G s R) {src : Fin k → V}
    (hsrc : ∀ i, σ.Knows G s R (src i) i) :
    (σ.gatherThen G s R src).IsValidFrom G src (2 * R) := by
  intro w u t i ht hsend
  by_cases htR : t < R
  · have hex : ∃ i, σ.Gathers G s R src w u t i := by
      by_contra hno
      simp [gatherThen, htR, hno] at hsend
    obtain ⟨j, hj⟩ := hex
    rw [gatherThen_send_of_gathers htR hj, Option.some_inj] at hsend
    subst hsend
    obtain ⟨h1, h2, hne⟩ := hj
    refine ⟨?_, h1 ▸ knowsFrom_back j t htR.le⟩
    rcases back_spec (σ := σ) (G := G) (s := s) R src j t with h | ⟨hadj, -⟩
    · exact absurd (h1 ▸ h2 ▸ h).symm hne
    · rw [← h1, ← h2]; exact hadj.symm
  · obtain ⟨t, rfl⟩ : ∃ t', t = R + t' := ⟨t - R, by omega⟩
    rw [gatherThen_send_late] at hsend
    obtain ⟨hadj, hk⟩ := hv w u t i (by omega) hsend
    exact ⟨hadj, knowsFrom_late hv hsrc t w i hk⟩

end RoutingSchedule

/-- **Multi-source reduction, schedule form.** If a routing schedule broadcasts `k` packets from
`s` within `R` rounds, then for every initial placement `src` of the packets some routing schedule
broadcasts them within `2 R` rounds. -/
theorem exists_multiSource_schedule {s : V} {R : ℕ} {σ : RoutingSchedule V k}
    (hv : σ.IsValid G s R) (hc : σ.Completes G s R) (src : Fin k → V) :
    ∃ σ' : RoutingSchedule V k, σ'.IsValidFrom G src (2 * R) ∧ σ'.CompletesFrom G src (2 * R) := by
  refine ⟨σ.gatherThen G s R src, σ.isValidFrom_gatherThen hv fun i => hc _ i,
    fun v i => ?_⟩
  rw [two_mul]
  exact RoutingSchedule.knowsFrom_late hv (fun i => hc _ i) R v i (hc v i)

/-- **Multi-source reduction.** In a connected graph, for every source `s` and every initial
placement `src` of the `k` packets, `ROUTE(G, src, k) ≤ 2 ROUTE(G, s, k)`. -/
theorem multiSourceRoutingTime_le [DecidableRel G.Adj] (hG : G.Connected) (s : V)
    (src : Fin k → V) : multiSourceRoutingTime G src ≤ 2 * routingTime G s k := by
  obtain ⟨σ, hv, hc⟩ := Nat.sInf_mem (s := {R | ∃ σ : RoutingSchedule V k,
    σ.IsValid G s R ∧ σ.Completes G s R}) (exists_routingSchedule hG s k)
  exact Nat.sInf_le (exists_multiSource_schedule hv hc src)

end CodingGap
