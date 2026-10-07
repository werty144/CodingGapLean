import CodingGap.Benchmark

/-!
# Temporal path systems

A *temporal path* from `s` to `v` within horizon `T` is a sequence of communication arcs
`(u₀,w₀,t₀), (u₁,w₁,t₁), …` of `G[T]` with `u₀ = s`, `wᵢ = uᵢ₊₁`, `tᵢ < tᵢ₊₁` (waiting is free)
and final head `v`. A *temporal path system* of size `k` for `v` is a family of `k` temporal paths
without a common arc.

`exists_temporalPathSystem`: if `C_T(s,v) ≥ k`, such a system exists. This is the temporal flow of
`eq:ff-cut-value` (and of the proof of `thm:coded`): every path `Pᵢ` of length `ℓᵢ ≤ T` of an optimal
family is repeated at the departure times `0, …, T - ℓᵢ`.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A temporal path from `s` to `v` in `G[T]`. -/
structure TemporalPath (G : SimpleGraph V) (s v : V) (T : ℕ) where
  len : ℕ
  arc : ℕ → V × V × ℕ
  len_pos : 0 < len
  adj : ∀ i < len, G.Adj (arc i).1 (arc i).2.1
  time_lt : ∀ i < len, (arc i).2.2 < T
  first : (arc 0).1 = s
  chain : ∀ i, i + 1 < len → (arc i).2.1 = (arc (i + 1)).1 ∧ (arc i).2.2 < (arc (i + 1)).2.2
  last : (arc (len - 1)).2.1 = v

/-- `k` temporal paths from `s` to `v` without a common arc. -/
structure TemporalPathSystem (G : SimpleGraph V) (s v : V) (T k : ℕ) where
  path : Fin k → TemporalPath G s v T
  disjoint : ∀ j j' i i', i < (path j).len → i' < (path j').len →
    (path j).arc i = (path j').arc i' → j = j' ∧ i = i'

namespace TemporalPath

variable {s v : V} {T : ℕ} (π : TemporalPath G s v T)

/-- Times strictly increase along a temporal path. -/
theorem time_strictMono {i i' : ℕ} (h : i < i') (hi' : i' < π.len) :
    (π.arc i).2.2 < (π.arc i').2.2 := by
  induction i', h using Nat.le_induction with
  | base => exact (π.chain i hi').2
  | succ n hn ih => exact (ih (by omega)).trans (π.chain n hi').2

theorem time_lt_iff {i i' : ℕ} (hi : i < π.len) (hi' : i' < π.len) :
    (π.arc i).2.2 < (π.arc i').2.2 ↔ i < i' := by
  constructor
  · intro h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | rfl
    · exact absurd (π.time_strictMono h'' hi) (not_lt.2 h.le)
    · exact lt_irrefl _ h
  · exact fun h => π.time_strictMono h hi'

/-- A walk of length `ℓ ≤ T - d` from `s` to `v`, started at time `d`. -/
def ofWalk (p : G.Walk s v) (hsv : s ≠ v) (d : ℕ) (hd : d + p.length ≤ T) :
    TemporalPath G s v T where
  len := p.length
  arc t := (p.getVert t, p.getVert (t + 1), d + t)
  len_pos := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    exact hsv (SimpleGraph.Walk.eq_of_length_eq_zero h)
  adj i hi := p.adj_getVert_succ hi
  time_lt i hi := by simp only; omega
  first := p.getVert_zero
  chain i _ := ⟨rfl, by simp⟩
  last := by
    simp only
    rw [Nat.sub_add_cancel (by
      rw [Nat.one_le_iff_ne_zero]; intro h; exact hsv (SimpleGraph.Walk.eq_of_length_eq_zero h))]
    exact p.getVert_length

end TemporalPath

/-- If `C_T(s,v) ≥ k`, then `v` has a temporal path system of size `k`. -/
theorem exists_temporalPathSystem {s v : V} [DecidableRel G.Adj] (hv : v ≠ s) {T k : ℕ}
    (hk : k ≤ temporalMinCut G s v T) : Nonempty (TemporalPathSystem G s v T k) := by
  classical
  obtain ⟨q, P, hP, hshort⟩ := exists_value_eq_temporalMinCut_short (G := G) hv T
  -- the index set of all repetitions `(i, d)` with `d ≤ T - ℓᵢ`
  let S : Finset (Σ _ : Fin q, ℕ) := univ.sigma fun i => range (T + 1 - (P.path i).length)
  have hS : k ≤ S.card := by
    rw [card_sigma]
    simp only [card_range]
    have h1 : ((∑ i, (T + 1 - (P.path i).length) : ℕ) : ℤ) = P.value T := by
      rw [DisjointPaths.value_eq, DisjointPaths.totalLength, Nat.cast_sum, Nat.cast_sum]
      rw [show (q : ℤ) * (T + 1) = ∑ _i : Fin q, ((T : ℤ) + 1) by simp, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      have := hshort i
      omega
    have : (k : ℤ) ≤ ∑ i, (T + 1 - (P.path i).length : ℕ) := by rw [h1, hP]; exact_mod_cast hk
    exact_mod_cast this
  obtain ⟨S', hS'sub, hS'card⟩ := exists_subset_card_eq hS
  let e : Fin k ≃ S' := (S'.equivFin.trans (finCongr hS'card)).symm
  have he : ∀ j, ((e j : Σ _ : Fin q, ℕ)).2 + (P.path (e j : Σ _ : Fin q, ℕ).1).length ≤ T := by
    intro j
    have := hS'sub (e j).2
    simp only [S, mem_sigma, mem_univ, mem_range, true_and] at this
    omega
  refine ⟨⟨fun j => TemporalPath.ofWalk (P.path (e j : Σ _ : Fin q, ℕ).1) hv.symm _ (he j),
    fun j j' i i' hi hi' h => ?_⟩⟩
  simp only [TemporalPath.ofWalk, Prod.mk.injEq] at h hi hi'
  obtain ⟨h1, h2, h3⟩ := h
  set a := (e j : Σ _ : Fin q, ℕ)
  set b := (e j' : Σ _ : Fin q, ℕ)
  by_cases hab : a.1 = b.1
  · -- the same static path: equal vertices at equal positions, hence equal departures
    have hpath : (P.path a.1).IsPath := P.isPath _
    rw [← hab] at h1 hi'
    have hii : i = i' := hpath.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) h1
    subst hii
    have hd : a.2 = b.2 := by omega
    have : a = b := Sigma.ext hab (heq_of_eq hd)
    exact ⟨e.injective (Subtype.ext this), rfl⟩
  · -- different static paths share no edge
    exfalso
    have hmem : s((P.path a.1).getVert i, (P.path a.1).getVert (i + 1)) ∈ (P.path a.1).edges :=
      (SimpleGraph.Walk.mk_mem_edges_iff_exists _).2 ⟨i, hi, rfl⟩
    have hmem' : s((P.path a.1).getVert i, (P.path a.1).getVert (i + 1)) ∈ (P.path b.1).edges := by
      rw [h1, h2]
      exact (SimpleGraph.Walk.mk_mem_edges_iff_exists _).2 ⟨i', hi', rfl⟩
    exact P.disjoint hab hmem hmem'

end CodingGap
