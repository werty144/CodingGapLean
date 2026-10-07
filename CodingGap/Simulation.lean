import CodingGap.Pipeline

/-!
# Routing schedules are coding schemes (`CODE ≤ ROUTE`)

A routing schedule treats the packets as opaque symbols: its timetable is fixed in advance,
so it runs as a deterministic protocol (coding scheme). Every vertex stores the
packets it holds; on an edge scheduled to forward packet `i` the sender transmits its copy of
`X i`, and on every other channel opportunity it transmits a fixed dummy symbol.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

namespace RoutingSchedule

variable (σ : RoutingSchedule V k)

/-- The symbol sent by `u` to `w` in round `t`: its copy of the scheduled packet, or a dummy. -/
noncomputable def fwdSend (A : Type) [Nonempty A] (u w : V) (t : ℕ) (st : Fin k → Option A) : A :=
  match σ.send u w t with
  | some i => (st i).getD (Classical.arbitrary A)
  | none => Classical.arbitrary A

open Classical in
/-- The state update of `w`: store a packet received from a scheduled sender. -/
noncomputable def fwdStep (A : Type) [Nonempty A] (w : V) (t : ℕ) (st : Fin k → Option A)
    (msgs : V → Option A) : Fin k → Option A := fun i =>
  match st i with
  | some a => some a
  | none =>
    if h : ∃ u a, msgs u = some a ∧ σ.send u w t = some i then some h.choose_spec.choose
    else none

/-- The protocol executing a routing schedule: the state of a vertex records the packets it
holds. -/
noncomputable def toProtocol (A : Type) [Nonempty A] : Protocol V A k where
  State := Fin k → Option A
  initSource X := fun i => some (X i)
  init _ := fun _ => none
  send := σ.fwdSend A
  step := σ.fwdStep A
  output _ st := fun i => (st i).getD (Classical.arbitrary A)

variable {A : Type} [Nonempty A] {s : V}

theorem fwdSend_of_send {u w : V} {t : ℕ} {i : Fin k} (h : σ.send u w t = some i)
    (st : Fin k → Option A) : σ.fwdSend A u w t st = (st i).getD (Classical.arbitrary A) := by
  simp [fwdSend, h]

theorem fwdStep_of_some {w : V} {t : ℕ} {st : Fin k → Option A} {msgs : V → Option A}
    {i : Fin k} {a : A} (h : st i = some a) : σ.fwdStep A w t st msgs i = some a := by
  simp [fwdStep, h]

theorem fwdStep_of_none_pos {w : V} {t : ℕ} {st : Fin k → Option A} {msgs : V → Option A}
    {i : Fin k} (h : st i = none) (hex : ∃ u a, msgs u = some a ∧ σ.send u w t = some i) :
    ∃ u a, msgs u = some a ∧ σ.send u w t = some i ∧ σ.fwdStep A w t st msgs i = some a := by
  classical
  refine ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.1,
    hex.choose_spec.choose_spec.2, ?_⟩
  simp only [fwdStep, h]
  rw [dif_pos hex]

theorem fwdStep_of_none_neg {w : V} {t : ℕ} {st : Fin k → Option A} {msgs : V → Option A}
    {i : Fin k} (h : st i = none) (hno : ¬ ∃ u a, msgs u = some a ∧ σ.send u w t = some i) :
    σ.fwdStep A w t st msgs i = none := by
  classical
  simp only [fwdStep, h]
  rw [dif_neg hno]

theorem toProtocol_run_succ (X : Fin k → A) (t : ℕ) (w : V) :
    (σ.toProtocol A).run G s X (t + 1) w =
      σ.fwdStep A w t ((σ.toProtocol A).run G s X t w)
        (fun u => if G.Adj u w then some (σ.fwdSend A u w t ((σ.toProtocol A).run G s X t u))
          else none) := rfl

/-- During the valid part of the schedule the protocol state is exactly the set of held packets,
with their correct values. -/
theorem run_toProtocol {R : ℕ} (hvalid : σ.IsValid G s R) (X : Fin k → A) :
    ∀ t ≤ R, ∀ u i, (σ.Knows G s t u i → (σ.toProtocol A).run G s X t u i = some (X i)) ∧
      (¬ σ.Knows G s t u i → (σ.toProtocol A).run G s X t u i = none) := by
  intro t
  induction t with
  | zero =>
    intro _ u i
    by_cases hu : u = s
    · subst hu; simp [Protocol.run, toProtocol, Knows]
    · simp [Protocol.run, toProtocol, Knows, hu]
  | succ t ih =>
    intro ht w i
    have ih' := ih (Nat.le_of_succ_le ht)
    rw [toProtocol_run_succ]
    by_cases hk : σ.Knows G s t w i
    · exact ⟨fun _ => σ.fwdStep_of_some ((ih' w i).1 hk), fun h => absurd (Or.inl hk) h⟩
    · have h0 : (σ.toProtocol A).run G s X t w i = none := (ih' w i).2 hk
      constructor
      · rintro (hk' | ⟨u, hadj, hsend⟩)
        · exact absurd hk' hk
        · have hex : ∃ u a, (fun u => if G.Adj u w then
                some (σ.fwdSend A u w t ((σ.toProtocol A).run G s X t u)) else none) u = some a ∧
              σ.send u w t = some i := ⟨u, _, if_pos hadj, hsend⟩
          obtain ⟨u', a, hm, hsend', he⟩ := σ.fwdStep_of_none_pos h0 hex
          rw [he]
          split_ifs at hm with hadj'
          cases hm
          simp only [fwdSend, hsend']
          rw [(ih' u' i).1 (hvalid u' w t i ht hsend').2]
          rfl
      · intro hk'
        refine σ.fwdStep_of_none_neg h0 ?_
        rintro ⟨u, a, hm, hsend⟩
        split_ifs at hm with hadj
        exact hk' (Or.inr ⟨u, hadj, hsend⟩)

/-- A valid routing schedule completing by time `R` broadcasts every input by time `R`. -/
theorem broadcasts_toProtocol {R : ℕ} (hvalid : σ.IsValid G s R) (hcomp : σ.Completes G s R)
    (X : Fin k → A) : (σ.toProtocol A).Broadcasts G s X R := by
  intro v
  funext i
  have := (σ.run_toProtocol hvalid X R le_rfl v i).1 (hcomp v i)
  change ((σ.toProtocol A).run G s X R v i).getD (Classical.arbitrary A) = X i
  rw [this]
  rfl

end RoutingSchedule

/-- **`CODE ≤ ROUTE`.** A routing schedule is a special coding scheme, so the coded broadcast
time is at most the routing broadcast time (whenever some routing schedule exists). -/
theorem codedTime_le_routingTime (A : Type) [Nonempty A] {s : V}
    (hne : ∃ R, ∃ σ : RoutingSchedule V k, σ.IsValid G s R ∧ σ.Completes G s R) :
    codedTime G s A k ≤ routingTime G s k := by
  obtain ⟨σ, hvalid, hcomp⟩ := Nat.sInf_mem (s := {R | ∃ σ : RoutingSchedule V k,
    σ.IsValid G s R ∧ σ.Completes G s R}) hne
  exact Nat.sInf_le ⟨σ.toProtocol A, σ.broadcasts_toProtocol hvalid hcomp⟩

end CodingGap
