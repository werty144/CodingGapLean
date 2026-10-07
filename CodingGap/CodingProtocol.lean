import CodingGap.LinearCode
import CodingGap.Simulation

/-!
# Coding attains the temporal benchmark (`thm:coded`)

A valid linear code `g` for horizon `T` (see `CodingGap.LinearCode`) is run as a protocol over the
alphabet `F`: every vertex stores its input (the source) and all received symbols; on the arc
`a = (u, w, t)` it sends the linear combination of its stored symbols given by a representation of
`g a` in its knowledge space, which evaluates to `⟨g a, X⟩`. At time `T` a vertex whose knowledge is
all of `F^k` recovers every `X i = ⟨eᵢ, X⟩` in the same way. The local coefficients are fixed in
advance (offline advice); no encoding vectors are transmitted.

* `codedTime_le_of_code`: a valid code whose receivers know `F^k` at time `T` gives
  `CODE(G,s,k) ≤ T`.
* `codedTime_eq_tau` (**Theorem `thm:coded`**): over a finite field with `|F| ≥ n`,
  `CODE(G,s,k) = τ(G,s,k)`.
-/

namespace CodingGap

open Finset Submodule

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {F : Type} [Field F] {k : ℕ} {s : V}

/-- The symbol `⟨x, X⟩ = ∑ᵢ xᵢ Xᵢ`. -/
def pair (x X : Fin k → F) : F := ∑ i, x i * X i

theorem pair_sum {ι : Type*} [Fintype ι] (c : ι → F) (v : ι → Fin k → F) (X : Fin k → F) :
    pair (∑ j, c j • v j) X = ∑ j, c j * pair (v j) X := by
  simp only [pair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem pair_single (i : Fin k) (X : Fin k → F) : pair (Pi.single i 1) X = X i := by
  simp [pair, Pi.single_apply]

theorem pair_zero (X : Fin k → F) : pair (0 : Fin k → F) X = 0 := by simp [pair]

variable (G s) (g : Code V F k) (T : ℕ)

/-- The value of a generator of the knowledge space in a stored state. -/
def genVal {t : ℕ} (st : (Fin k → F) × (V → ℕ → F)) : Fin k ⊕ (V × Fin t) → F
  | .inl i => st.1 i
  | .inr p => st.2 p.1 p.2

open Classical in
/-- Coefficients representing `x` in the knowledge of `u` at time `t` (zero if impossible). -/
noncomputable def coeffs (u : V) (t : ℕ) (x : Fin k → F) : Fin k ⊕ (V × Fin t) → F :=
  if h : ∃ c : Fin k ⊕ (V × Fin t) → F, ∑ j, c j • gen G s g u t j = x then h.choose else 0

theorem sum_coeffs {u : V} {t : ℕ} {x : Fin k → F} (hx : x ∈ knowledge G s g u t) :
    ∑ j, coeffs G s g u t x j • gen G s g u t j = x := by
  classical
  have h := (mem_span_range_iff_exists_fun F).1 hx
  simp only [coeffs, dif_pos h]
  exact h.choose_spec

/-- The protocol running the linear code `g` with horizon `T`. -/
noncomputable def codeProtocol : Protocol V F k where
  State := (Fin k → F) × (V → ℕ → F)
  initSource X := (X, 0)
  init _ := (0, 0)
  send u w t st := ∑ j, coeffs G s g u t (g (u, w, t)) j * genVal (t := t) st j
  step _ t st msgs := (st.1, fun u' t' => if t' = t then (msgs u').getD 0 else st.2 u' t')
  output v st := fun i => ∑ j, coeffs G s g v T (Pi.single i 1) j * genVal (t := T) st j

variable {G s g T}

/-- In the expected state, the value of a generator is its symbol. -/
theorem genVal_eq {X : Fin k → F} {u : V} {t : ℕ} :
    ∀ j : Fin k ⊕ (V × Fin t), genVal (t := t) ((if u = s then X else 0),
      fun u' t' => if t' < t ∧ G.Adj u' u then pair (g (u', u, t')) X else 0) j =
      pair (gen G s g u t j) X := by
  intro j
  rcases j with i | ⟨u'', t'⟩
  · by_cases hu : u = s
    · subst hu; simp [genVal, gen, pair_single]
    · simp [genVal, gen, hu, pair_zero]
  · by_cases hadj : G.Adj u'' u
    · simp [genVal, gen, hadj]
    · simp [genVal, gen, hadj, pair_zero]

/-- The protocol state: the input at the source, and the symbols `⟨g (u', u, t'), X⟩` received
before time `t`. -/
theorem codeProtocol_run (hg : IsValidCode G s T g) (X : Fin k → F) :
    ∀ t ≤ T, ∀ u, (codeProtocol G s g T).run G s X t u =
      ((if u = s then X else 0), fun u' t' =>
        if t' < t ∧ G.Adj u' u then pair (g (u', u, t')) X else 0) := by
  intro t
  induction t with
  | zero =>
    intro _ u
    by_cases hu : u = s
    · subst hu; simp [Protocol.run, codeProtocol]; rfl
    · simp [Protocol.run, codeProtocol, hu]; rfl
  | succ t ih =>
    intro ht u
    have ih' := ih (Nat.le_of_succ_le ht)
    have hstep : (codeProtocol G s g T).run G s X (t + 1) u =
        (((codeProtocol G s g T).run G s X t u).1, fun u' t' => if t' = t then
          ((if G.Adj u' u then some ((codeProtocol G s g T).send u' u t
            ((codeProtocol G s g T).run G s X t u')) else none).getD 0)
          else ((codeProtocol G s g T).run G s X t u).2 u' t') := rfl
    rw [hstep, ih' u]
    refine Prod.ext rfl (funext fun u' => funext fun t' => ?_)
    simp only
    by_cases htt : t' = t
    · subst htt
      by_cases hadj : G.Adj u' u
      · simp only [if_pos hadj, Option.getD_some, lt_add_one, true_and, if_true]
        show ∑ j, coeffs G s g u' t' (g (u', u, t')) j *
          genVal ((codeProtocol G s g T).run G s X t' u') j = _
        rw [ih' u']
        simp_rw [genVal_eq]
        rw [← pair_sum, sum_coeffs G s g (hg (u', u, t') (by simpa using ht))]
      · simp [hadj]
    · have : t' < t + 1 ↔ t' < t := by omega
      simp [htt, this]

/-- If every vertex knows `F^k` at time `T`, the protocol broadcasts every input by time `T`. -/
theorem broadcasts_codeProtocol (hg : IsValidCode G s T g) (hK : ∀ v, knowledge G s g v T = ⊤)
    (X : Fin k → F) : (codeProtocol G s g T).Broadcasts G s X T := by
  intro v
  funext i
  show ∑ j, coeffs G s g v T (Pi.single i 1) j *
    genVal ((codeProtocol G s g T).run G s X T v) j = X i
  rw [codeProtocol_run hg X T le_rfl v]
  simp_rw [genVal_eq]
  rw [← pair_sum, sum_coeffs G s g (by rw [hK v]; trivial), pair_single]

/-- A valid code whose receivers know `F^k` at time `T` gives `CODE(G,s,k) ≤ T`. -/
theorem codedTime_le_of_code (hg : IsValidCode G s T g) (hK : ∀ v, knowledge G s g v T = ⊤) :
    codedTime G s F k ≤ T :=
  Nat.sInf_le ⟨codeProtocol G s g T, broadcasts_codeProtocol hg hK⟩

/-- `τ ≤ CODE` for a connected graph and an alphabet of size at least two (`thm:lower`). -/
theorem tau_le_codedTime_of_connected (hG : G.Connected) (s : V) (k : ℕ)
    {A : Type} [Fintype A] (hA : 1 < Fintype.card A) : tau G s k ≤ codedTime G s A k := by
  have : Nonempty A := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨R, σ, hvalid, hcomp⟩ := exists_routingSchedule hG s k
  exact le_csInf ⟨R, σ.toProtocol A, σ.broadcasts_toProtocol hvalid hcomp⟩ fun _ ⟨P, hP⟩ =>
    tau_le_of_broadcasts G hA P hP

/-- **Theorem `thm:coded`.** Over a finite field `F` with `|F| ≥ n`, a preinstalled scalar linear
code completes broadcast in `τ(G,s,k)` rounds, so `CODE(G,s,k) = τ(G,s,k)`. -/
theorem codedTime_eq_tau [Fintype F] [DecidableEq F] (hG : G.Connected)
    (hF : Fintype.card V ≤ Fintype.card F) {k : ℕ} (hk : 1 ≤ k) :
    codedTime G s F k = tau G s k := by
  refine le_antisymm ?_ ?_
  · have sys : ∀ v : {v // v ≠ s}, TemporalPathSystem G s v (tau G s k) k := fun v =>
      Classical.choice (exists_temporalPathSystem v.2 (tau_mem hG hk v v.2))
    obtain ⟨g, hg, hK⟩ := exists_code sys hF
    exact codedTime_le_of_code hg hK
  · exact tau_le_codedTime_of_connected hG s k (A := F) Fintype.one_lt_card

end CodingGap
