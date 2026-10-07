import CodingGap.Model

/-!
# The temporal-cut lower bound (`thm:lower`)

* `Protocol.run_eq_of_transcript_eq`: outside the source side of a finite temporal cut, the state
  of every space-time vertex is determined by the transcript of the cut arcs.
* `Protocol.ncard_recovers_le`: for a fixed deterministic protocol, the receiver decodes correctly
  on at most `Q ^ c` inputs, where `c` is the cut capacity.
* `tau_le_of_broadcasts` (**Theorem `thm:lower`**): a correct coding scheme completing by time `T`
  has `T ≥ τ(G,s,k)`.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Type} {k : ℕ}
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Temporal cuts exist -/

/-- For `v ≠ s`, the set of all time copies of vertices other than `v` is a finite temporal
cut. -/
theorem isTemporalCut_ne {s v : V} (hv : v ≠ s) (T : ℕ) :
    IsTemporalCut s v T {x | x.1 ≠ v} where
  source_mem := hv.symm
  sink_not_mem := by simp
  storage_closed _ _ _ h := h

theorem temporalMinCut_nonempty {s v : V} (hv : v ≠ s) (T : ℕ) :
    {c | ∃ S, IsTemporalCut s v T S ∧ cutCapacity G T S = c}.Nonempty :=
  ⟨_, _, isTemporalCut_ne hv T, rfl⟩

/-- Every finite temporal cut has capacity at least `C_T(s,v)`. -/
theorem temporalMinCut_le {s v : V} {T : ℕ} {S : Set (V × ℕ)} (hS : IsTemporalCut s v T S) :
    temporalMinCut G s v T ≤ cutCapacity G T S :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- `C_T(s,v)` is attained by some finite temporal cut. -/
theorem exists_cut_temporalMinCut {s v : V} (hv : v ≠ s) (T : ℕ) :
    ∃ S, IsTemporalCut s v T S ∧ cutCapacity G T S = temporalMinCut G s v T :=
  Nat.sInf_mem (temporalMinCut_nonempty G hv T)

/-- To bound `C_T(s,v)` from below it suffices to bound every finite cut. -/
theorem le_temporalMinCut {s v : V} (hv : v ≠ s) {T c : ℕ}
    (h : ∀ S, IsTemporalCut s v T S → c ≤ cutCapacity G T S) : c ≤ temporalMinCut G s v T := by
  obtain ⟨S, hS, hc⟩ := exists_cut_temporalMinCut G hv T
  exact hc ▸ h S hS

theorem tau_le {s : V} {k T : ℕ} (h : ∀ v, v ≠ s → k ≤ temporalMinCut G s v T) :
    tau G s k ≤ T :=
  Nat.sInf_le h

/-! ### The receiver's state is determined by the cut transcript -/

namespace Protocol

variable (P : Protocol V A k)

/-- The transcript `Z(X)`: the symbols sent on the communication arcs leaving `S`. -/
def transcript (s : V) (T : ℕ) (S : Set (V × ℕ)) (X : Fin k → A) : cutArcs G T S → A :=
  fun a => P.send a.1.1 a.1.2.1 a.1.2.2 (P.run G s X a.1.2.2 a.1.1)

theorem mem_cutArcs {T : ℕ} {S : Set (V × ℕ)} {u w : V} {t : ℕ} (ht : t < T) (hadj : G.Adj u w)
    (hu : (u, t) ∈ S) (hw : (w, t + 1) ∉ S) : (u, w, t) ∈ cutArcs G T S := by
  classical
  simp [cutArcs, commArcs, ht, hadj, hu, hw]

/-- The induction in the proof of `thm:lower`: two inputs with the same cut transcript produce the same
state at every space-time vertex outside the source side of the cut. -/
theorem run_eq_of_transcript_eq {s v : V} {T : ℕ} {S : Set (V × ℕ)} (hS : IsTemporalCut s v T S)
    {X X' : Fin k → A} (h : P.transcript G s T S X = P.transcript G s T S X') :
    ∀ t ≤ T, ∀ u, (u, t) ∉ S → P.run G s X t u = P.run G s X' t u := by
  intro t
  induction t with
  | zero =>
    intro _ u hu
    have : u ≠ s := by rintro rfl; exact hu hS.source_mem
    simp [run, this]
  | succ t ih =>
    intro ht u hu
    have hu' : (u, t) ∉ S := fun h' => hu (hS.storage_closed u t ht h')
    simp only [run]
    congr 1
    · exact ih (Nat.le_of_succ_le ht) u hu'
    · funext w
      split_ifs with hadj
      · congr 1
        by_cases hw : (w, t) ∈ S
        · have hmem := mem_cutArcs G ht hadj hw hu
          exact congrFun h ⟨_, hmem⟩
        · rw [ih (Nat.le_of_succ_le ht) w hw]
      · rfl

/-- For a fixed deterministic protocol, the receiver behind a finite temporal cut of capacity `c`
decodes correctly on at most `Q ^ c` inputs. -/
theorem ncard_recovers_le [Fintype A] {s v : V} {T : ℕ} {S : Set (V × ℕ)}
    (hS : IsTemporalCut s v T S) :
    {X : Fin k → A | P.Recovers G s X v T}.ncard ≤ Fintype.card A ^ cutCapacity G T S := by
  classical
  have hinj : Set.InjOn (P.transcript G s T S) {X | P.Recovers G s X v T} := by
    intro X hX X' hX' h
    have := P.run_eq_of_transcript_eq G hS h T le_rfl v hS.sink_not_mem
    simp only [Set.mem_ofPred_eq, Recovers] at hX hX'
    rw [← hX, ← hX', this]
  calc {X : Fin k → A | P.Recovers G s X v T}.ncard
      = (P.transcript G s T S '' {X | P.Recovers G s X v T}).ncard := hinj.ncard_image.symm
    _ ≤ (Set.univ : Set (cutArcs G T S → A)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = Fintype.card A ^ cutCapacity G T S := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe,
        cutCapacity]

end Protocol

/-! ### The lower bound -/

/-- If `v` recovers every input at time `T`, then every finite temporal cut separating `v` from
the source has capacity at least `k`: otherwise the `Q ^ k` inputs would be decoded from at most
`Q ^ c < Q ^ k` cut transcripts. -/
theorem le_cutCapacity_of_recovers [Fintype A] (hA : 2 ≤ Fintype.card A) (P : Protocol V A k)
    {s v : V} {T : ℕ} (hrec : ∀ X, P.Recovers G s X v T) {S : Set (V × ℕ)}
    (hS : IsTemporalCut s v T S) : k ≤ cutCapacity G T S := by
  have h := P.ncard_recovers_le G hS
  have huniv : {X | P.Recovers G s X v T} = Set.univ := Set.eq_univ_of_forall hrec
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right hA).1 h

/-- If `v ≠ s` recovers every input at time `T`, then `C_T(s,v) ≥ k`. -/
theorem le_temporalMinCut_of_recovers [Fintype A] (hA : 2 ≤ Fintype.card A) (P : Protocol V A k)
    {s v : V} (hv : v ≠ s) {T : ℕ} (hrec : ∀ X, P.Recovers G s X v T) :
    k ≤ temporalMinCut G s v T :=
  le_temporalMinCut G hv fun _ hS => le_cutCapacity_of_recovers G hA P hrec hS

/-- **Theorem `thm:lower`.** Over an alphabet with at least two symbols, every correct coding
scheme that completes broadcast by time `T` has `T ≥ τ(G,s,k)`. -/
theorem tau_le_of_broadcasts [Fintype A] (hA : 2 ≤ Fintype.card A) (P : Protocol V A k)
    {s : V} {T : ℕ} (h : ∀ X, P.Broadcasts G s X T) : tau G s k ≤ T :=
  tau_le G fun v hv => le_temporalMinCut_of_recovers G hA P hv fun X => h X v

end CodingGap
