import CodingGap.FlowOverTime

/-!
# Path characterizations of `C_T` and `τ`; the short-path certificate (`lem:short`)

* `temporalMinCut_eq_sup'` (equation (5)): `C_T(s,v) = max_{0 ≤ q ≤ λ_v} (q (T + 1) - L_v(q))`.
* `temporalMinCut_mono`: temporal capacity is nondecreasing in the horizon.
* `tau_eq_formula` (an explicit formula for `τ`, not used in the paper):
  `τ(G,s,k) = max_{v ≠ s} min_{1 ≤ q ≤ λ_v} (⌈(k + L_v(q)) / q⌉ - 1)`.
* `one_le_tau`, `tau_le_of_walks`: `1 ≤ τ ≤ k + D - 1` when every receiver is within distance `D`.
* `exists_short_disjointPaths` (**`lem:short`**): if `T ≥ 1` and `C_T(s,v) ≥ k` then there are
  `⌈k / T⌉` edge-disjoint `s`–`v` paths, each of length at most `min T (n - 1)`.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {s v : V}

/-! ### Equation (5) -/

theorem DisjointPaths.value_eq {q : ℕ} (P : DisjointPaths G s v q) (T : ℕ) :
    P.value T = q * (T + 1) - P.totalLength := rfl

/-- Every `q ≤ λ_v` gives a lower bound `q (T + 1) - L_v(q) ≤ C_T(s,v)`. -/
theorem mul_sub_minTotalLength_le (hv : v ≠ s) (T : ℕ) {q : ℕ}
    (hq : q ≤ maxDisjointPaths G s v) :
    (q : ℤ) * (T + 1) - minTotalLength G s v q ≤ temporalMinCut G s v T := by
  obtain ⟨P, hP⟩ := exists_totalLength_eq_minTotalLength
    ((nonempty_disjointPaths_iff (G := G) hv.symm).2 hq)
  have := value_le_temporalMinCut hv T P
  rwa [DisjointPaths.value_eq, hP] at this

/-- The maximum in equation (5) is attained. -/
theorem exists_temporalMinCut_eq (hv : v ≠ s) (T : ℕ) :
    ∃ q ≤ maxDisjointPaths G s v,
      (temporalMinCut G s v T : ℤ) = q * (T + 1) - minTotalLength G s v q := by
  obtain ⟨q, P, hP⟩ := exists_value_eq_temporalMinCut (G := G) hv T
  have hq := le_maxDisjointPaths hv.symm P
  refine ⟨q, hq, le_antisymm ?_ (mul_sub_minTotalLength_le hv T hq)⟩
  rw [← hP, DisjointPaths.value_eq]
  have := minTotalLength_le P
  omega

/-- **Equation (5).** `C_T(s,v) = max_{0 ≤ q ≤ λ_v} (q (T + 1) - L_v(q))`. -/
theorem temporalMinCut_eq_sup' (hv : v ≠ s) (T : ℕ) :
    (temporalMinCut G s v T : ℤ) = (range (maxDisjointPaths G s v + 1)).sup' ⟨0, by simp⟩
      fun q : ℕ => (q : ℤ) * (T + 1) - minTotalLength G s v q := by
  refine le_antisymm ?_ (sup'_le _ _ fun q hq =>
    mul_sub_minTotalLength_le hv T (Nat.lt_succ_iff.1 (mem_range.1 hq)))
  obtain ⟨q, hq, he⟩ := exists_temporalMinCut_eq (G := G) hv T
  rw [he]
  exact le_sup' (fun q : ℕ => (q : ℤ) * (T + 1) - minTotalLength G s v q)
    (mem_range.2 (Nat.lt_succ_of_le hq))

/-! ### Monotonicity -/

/-- Temporal capacity is nondecreasing in the horizon. -/
theorem temporalMinCut_mono (hv : v ≠ s) {T T' : ℕ} (h : T ≤ T') :
    temporalMinCut G s v T ≤ temporalMinCut G s v T' := by
  obtain ⟨q, P, hP⟩ := exists_value_eq_temporalMinCut (G := G) hv T
  have h1 := value_le_temporalMinCut hv T' P
  have h2 : P.value T ≤ P.value T' := by
    simp only [DisjointPaths.value_eq]
    have : (T : ℤ) ≤ T' := by exact_mod_cast h
    have : (0 : ℤ) ≤ q := by positivity
    nlinarith
  have : (temporalMinCut G s v T : ℤ) ≤ temporalMinCut G s v T' := by linarith
  exact_mod_cast this

/-! ### Receiver thresholds -/

theorem le_temporalMinCut_iff (hv : v ≠ s) {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    k ≤ temporalMinCut G s v T ↔
      ∃ q, 1 ≤ q ∧ q ≤ maxDisjointPaths G s v ∧ k + minTotalLength G s v q ≤ q * (T + 1) := by
  constructor
  · intro h
    obtain ⟨q, hq, he⟩ := exists_temporalMinCut_eq (G := G) hv T
    refine ⟨q, ?_, hq, ?_⟩
    · rcases Nat.eq_zero_or_pos q with rfl | hq0
      · simp at he; omega
      · exact hq0
    · have : (k : ℤ) ≤ temporalMinCut G s v T := by exact_mod_cast h
      have : (k : ℤ) + minTotalLength G s v q ≤ q * (T + 1) := by linarith
      exact_mod_cast this
  · rintro ⟨q, -, hq, hle⟩
    have h1 := mul_sub_minTotalLength_le hv T hq
    have : ((k + minTotalLength G s v q : ℕ) : ℤ) ≤ ((q * (T + 1) : ℕ) : ℤ) := by exact_mod_cast hle
    push_cast at this
    have : (k : ℤ) ≤ temporalMinCut G s v T := by linarith
    exact_mod_cast this

/-- For `q ≥ 1`: `q (T + 1) - L ≥ k` iff `T ≥ ⌈(k + L) / q⌉ - 1`. -/
theorem add_le_mul_iff_ceil {k L q T : ℕ} (hq : 1 ≤ q) :
    k + L ≤ q * (T + 1) ↔ ⌈((k + L : ℕ) : ℚ) / q⌉₊ - 1 ≤ T := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  rw [show ⌈((k + L : ℕ) : ℚ) / q⌉₊ - 1 ≤ T ↔ ⌈((k + L : ℕ) : ℚ) / q⌉₊ ≤ T + 1 by omega,
    Nat.ceil_le, div_le_iff₀ hq']
  constructor
  · intro h; exact_mod_cast (by rw [mul_comm]; exact_mod_cast h : ((k + L : ℕ) : ℚ) ≤ ((T + 1 : ℕ) : ℚ) * q)
  · intro h
    have : ((k + L : ℕ) : ℚ) ≤ ((q * (T + 1) : ℕ) : ℚ) := by push_cast at h ⊢; linarith
    exact_mod_cast this

theorem le_temporalMinCut_iff_ceil (hv : v ≠ s) {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    k ≤ temporalMinCut G s v T ↔ ∃ q ∈ Set.Icc 1 (maxDisjointPaths G s v),
      ⌈((k + minTotalLength G s v q : ℕ) : ℚ) / q⌉₊ - 1 ≤ T := by
  rw [le_temporalMinCut_iff hv hk]
  constructor
  · rintro ⟨q, hq1, hq, h⟩; exact ⟨q, ⟨hq1, hq⟩, (add_le_mul_iff_ceil hq1).1 h⟩
  · rintro ⟨q, ⟨hq1, hq⟩, h⟩; exact ⟨q, hq1, hq, (add_le_mul_iff_ceil hq1).2 h⟩

/-- The infimum of an up-set generated by the values `f q`, `q ∈ I`, is the least value. -/
theorem sInf_upperClosure_eq (f : ℕ → ℕ) (I : Set ℕ) :
    sInf {T | ∃ q ∈ I, f q ≤ T} = sInf (f '' I) := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp
  · have hne : (f '' I).Nonempty := hI.image f
    obtain ⟨q, hq, hfq⟩ := Nat.sInf_mem hne
    apply le_antisymm
    · exact Nat.sInf_le ⟨q, hq, hfq.le⟩
    · have hne' : {T | ∃ q ∈ I, f q ≤ T}.Nonempty := ⟨f q, q, hq, le_rfl⟩
      obtain ⟨q', hq', hle⟩ := Nat.sInf_mem hne'
      exact (Nat.sInf_le (Set.mem_image_of_mem f hq')).trans hle

/-- The first horizon at which the single receiver `v` has capacity `k`. -/
theorem receiver_threshold_eq (hv : v ≠ s) {k : ℕ} (hk : 1 ≤ k) :
    sInf {T | k ≤ temporalMinCut G s v T} =
      sInf ((fun q => ⌈((k + minTotalLength G s v q : ℕ) : ℚ) / q⌉₊ - 1) ''
        Set.Icc 1 (maxDisjointPaths G s v)) := by
  rw [← sInf_upperClosure_eq]
  congr 1
  ext T
  exact le_temporalMinCut_iff_ceil hv hk T

/-! ### An explicit formula for `τ` -/

/-- In a connected graph some horizon has capacity at least `k` at `v`. -/
theorem exists_le_temporalMinCut (hG : G.Connected) (hv : v ≠ s) (k : ℕ) :
    ∃ T, k ≤ temporalMinCut G s v T := by
  obtain ⟨p⟩ := hG.preconnected s v
  let P : DisjointPaths G s v 1 :=
    ⟨fun _ => p.bypass, fun _ => p.bypass_isPath, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  refine ⟨k + p.bypass.length, ?_⟩
  have := value_le_temporalMinCut hv (k + p.bypass.length) P
  simp only [DisjointPaths.value_eq, DisjointPaths.totalLength, P, Finset.univ_unique,
    Finset.sum_singleton] at this
  push_cast at this
  have : (k : ℤ) ≤ temporalMinCut G s v (k + p.bypass.length) := by linarith
  exact_mod_cast this

theorem le_temporalMinCut_iff_threshold_le (hG : G.Connected) (hv : v ≠ s) {k T : ℕ} :
    k ≤ temporalMinCut G s v T ↔ sInf {T | k ≤ temporalMinCut G s v T} ≤ T := by
  constructor
  · exact fun h => Nat.sInf_le h
  · intro h
    obtain ⟨T₀, hT₀⟩ := exists_le_temporalMinCut hG hv k
    exact (Nat.sInf_mem (s := {T | k ≤ temporalMinCut G s v T}) ⟨T₀, hT₀⟩).trans
      (temporalMinCut_mono hv h)

/-- `τ` is the largest receiver threshold. -/
theorem tau_eq_sSup_threshold (hG : G.Connected) (k : ℕ) :
    tau G s k = sSup ((fun v => sInf {T | k ≤ temporalMinCut G s v T}) '' {v | v ≠ s}) := by
  set M := sSup ((fun v => sInf {T | k ≤ temporalMinCut G s v T}) '' {v | v ≠ s})
  have hbdd : BddAbove ((fun v => sInf {T | k ≤ temporalMinCut G s v T}) '' {v | v ≠ s}) :=
    (Set.toFinite _).bddAbove
  have key : ∀ T, (∀ v, v ≠ s → k ≤ temporalMinCut G s v T) ↔ M ≤ T := by
    intro T
    constructor
    · intro h
      exact csSup_le' (by rintro _ ⟨v, hv, rfl⟩; exact Nat.sInf_le (h v hv))
    · intro hM v hv
      rw [le_temporalMinCut_iff_threshold_le hG hv]
      exact (le_csSup hbdd ⟨v, hv, rfl⟩).trans hM
  unfold tau
  simp_rw [key]
  have hM : M ∈ {T | M ≤ T} := Set.mem_setOf.2 le_rfl
  exact le_antisymm (Nat.sInf_le hM) (le_csInf ⟨M, hM⟩ fun _ h => h)

/-- **Explicit benchmark.** In a connected graph and for `k ≥ 1`,
`τ(G,s,k) = max_{v ≠ s} min_{1 ≤ q ≤ λ_v} (⌈(k + L_v(q)) / q⌉ - 1)`. -/
theorem tau_eq_formula (hG : G.Connected) {k : ℕ} (hk : 1 ≤ k) :
    tau G s k = sSup ((fun v => sInf ((fun q => ⌈((k + minTotalLength G s v q : ℕ) : ℚ) / q⌉₊ - 1)
      '' Set.Icc 1 (maxDisjointPaths G s v))) '' {v | v ≠ s}) := by
  rw [tau_eq_sSup_threshold hG k]
  congr 1
  exact Set.image_congr fun v hv => receiver_threshold_eq hv hk

/-! ### Elementary bounds on `τ` -/

theorem temporalMinCut_zero (hv : v ≠ s) : temporalMinCut G s v 0 = 0 := by
  refine Nat.eq_zero_of_le_zero ((temporalMinCut_le G (isTemporalCut_ne hv 0)).trans ?_)
  simp [cutCapacity, cutArcs, commArcs]

/-- A single walk of length `ℓ` gives `C_T(s,v) ≥ T + 1 - ℓ`. -/
theorem sub_length_le_temporalMinCut (hv : v ≠ s) (p : G.Walk s v) (T : ℕ) :
    (T + 1 : ℤ) - p.length ≤ temporalMinCut G s v T := by
  let P : DisjointPaths G s v 1 :=
    ⟨fun _ => p.bypass, fun _ => p.bypass_isPath, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  have h1 := value_le_temporalMinCut hv T P
  have h2 : (p.bypass.length : ℤ) ≤ p.length := by exact_mod_cast p.length_bypass_le_length
  simp only [DisjointPaths.value_eq, DisjointPaths.totalLength, P, Finset.univ_unique,
    Finset.sum_singleton] at h1
  push_cast at h1
  linarith

/-- If every receiver is joined to `s` by a walk of length at most `D`, then every receiver has
temporal capacity at least `k` at horizon `k + D - 1`. -/
theorem le_temporalMinCut_of_walks {k D : ℕ} (hk : 1 ≤ k)
    (h : ∀ v, v ≠ s → ∃ p : G.Walk s v, p.length ≤ D) :
    ∀ v, v ≠ s → k ≤ temporalMinCut G s v (k + D - 1) := by
  intro v hv
  obtain ⟨p, hp⟩ := h v hv
  have := sub_length_le_temporalMinCut hv p (k + D - 1)
  have hkD : ((k + D - 1 : ℕ) : ℤ) = k + D - 1 := by omega
  rw [hkD] at this
  have : (k : ℤ) ≤ temporalMinCut G s v (k + D - 1) := by
    have : (p.length : ℤ) ≤ D := by exact_mod_cast hp
    linarith
  exact_mod_cast this

/-- If every receiver is joined to `s` by a walk of length at most `D`, then
`τ(G,s,k) ≤ k + D - 1`. -/
theorem tau_le_of_walks {k D : ℕ} (hk : 1 ≤ k) (h : ∀ v, v ≠ s → ∃ p : G.Walk s v, p.length ≤ D) :
    tau G s k ≤ k + D - 1 :=
  tau_le G (le_temporalMinCut_of_walks hk h)

theorem walks_le_card (hG : G.Connected) :
    ∀ v, v ≠ s → ∃ p : G.Walk s v, p.length ≤ Fintype.card V - 1 := fun v _ => by
  obtain ⟨p⟩ := hG.preconnected s v
  exact ⟨p.bypass, Nat.le_sub_one_of_lt p.bypass_isPath.length_lt⟩

/-- In a connected graph, `τ(G,s,k) ≤ k + n - 2`. -/
theorem tau_le_card (hG : G.Connected) {k : ℕ} (hk : 1 ≤ k) :
    tau G s k ≤ k + (Fintype.card V - 1) - 1 :=
  tau_le_of_walks hk (walks_le_card hG)

/-- In a connected graph, the horizon `τ` itself has capacity at least `k` at every receiver. -/
theorem tau_mem (hG : G.Connected) {k : ℕ} (hk : 1 ≤ k) :
    ∀ v, v ≠ s → k ≤ temporalMinCut G s v (tau G s k) :=
  Nat.sInf_mem (s := {T | ∀ v, v ≠ s → k ≤ temporalMinCut G s v T})
    ⟨_, le_temporalMinCut_of_walks hk (walks_le_card hG)⟩

/-- `τ ≥ 1` as soon as there is a receiver and `k ≥ 1`. -/
theorem one_le_tau (hG : G.Connected) {k : ℕ} (hk : 1 ≤ k) (hn : ∃ v, v ≠ s) :
    1 ≤ tau G s k := by
  obtain ⟨v, hv⟩ := hn
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have := tau_mem hG hk v hv
  rw [h0, temporalMinCut_zero hv] at this
  omega

/-! ### The short-path certificate (`lem:short`) -/

/-- **`lem:short` (short disjoint paths).** If `T ≥ 1` and `C_T(s,v) ≥ k`, there are `r` edge-disjoint
`s`–`v` paths with `k ≤ r T` (so `r ≥ ⌈k / T⌉`), each of length at most `T` and at most `n - 1`. -/
theorem exists_short_disjointPaths' (hv : v ≠ s) {T k : ℕ} (hk : k ≤ temporalMinCut G s v T) :
    ∃ (r : ℕ) (P : DisjointPaths G s v r), k ≤ r * T ∧
      ∀ i, (P.path i).length ≤ T ∧ (P.path i).length ≤ Fintype.card V - 1 := by
  obtain ⟨r, P, hP, hshort⟩ := exists_value_eq_temporalMinCut_short (G := G) hv T
  refine ⟨r, P, ?_, fun i => ⟨hshort i, Nat.le_sub_one_of_lt (P.isPath i).length_lt⟩⟩
  have hpos : ∀ i, 1 ≤ (P.path i).length := by
    intro i
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hv.symm (SimpleGraph.Walk.eq_of_length_eq_zero h)
  have hsum : P.totalLength ≥ r := by
    unfold DisjointPaths.totalLength
    calc r = ∑ _i : Fin r, 1 := by simp
      _ ≤ _ := sum_le_sum fun i _ => hpos i
  have : (k : ℤ) ≤ r * (T + 1) - P.totalLength := by
    rw [← DisjointPaths.value_eq, hP]; exact_mod_cast hk
  have : (k : ℤ) ≤ r * T := by nlinarith
  exact_mod_cast this

/-- **`lem:short`**, in the paper's form: `⌈k / T⌉` edge-disjoint `s`–`v` paths, each of length at
most `min T (n - 1)`. -/
theorem exists_short_disjointPaths (hv : v ≠ s) {T k : ℕ} (hT : 1 ≤ T)
    (hk : k ≤ temporalMinCut G s v T) :
    ∃ P : DisjointPaths G s v ⌈(k : ℚ) / T⌉₊,
      ∀ i, (P.path i).length ≤ min T (Fintype.card V - 1) := by
  obtain ⟨r, P, hr, hshort⟩ := exists_short_disjointPaths' hv hk
  have hceil : ⌈(k : ℚ) / T⌉₊ ≤ r := by
    rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hT)]
    exact_mod_cast hr
  exact ⟨P.restrict hceil, fun i => le_min (hshort _).1 (hshort _).2⟩

end CodingGap
