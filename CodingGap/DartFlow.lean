import CodingGap.Paths

/-!
# Unit flows on darts and their path decompositions

An integer function `f` on the darts (directed edges) of `G` is a *unit `s`–`v` flow of value `q`*
if it takes values in `{0, 1}` and its net outflow is `q` at `s`, `-q` at `v` and `0` elsewhere.

* `pathFlow P`: the unit flow of an edge-disjoint path family, of value `q` and size equal to the
  total length of the family.
* `exists_disjointPaths_of_isUnitFlow`: conversely, every unit flow of value `q` contains `q`
  edge-disjoint `s`–`v` paths of total length at most its size (antiparallel pairs are cancelled
  first; then a flow path from `s` to `v` exists by a cut-counting argument and is removed).

This is the flow-decomposition step in the proof of `max_flow_over_time` (`eq:ff-cut-value`).
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `bdry a b x = [a = x] - [b = x]`: the boundary of a unit of flow from `a` to `b`. -/
def bdry (a b x : V) : ℤ := (if a = x then 1 else 0) - (if b = x then 1 else 0)

/-- Net outflow of an integer dart flow at `x`. -/
def excess (f : G.Dart → ℤ) (x : V) : ℤ := ∑ d, f d * bdry d.fst d.snd x

/-- `f` is a `{0,1}`-valued `s`–`v` flow of value `q`. -/
structure IsUnitFlow (s v : V) (f : G.Dart → ℤ) (q : ℤ) : Prop where
  zero_or_one : ∀ d, f d = 0 ∨ f d = 1
  conservation : ∀ x, excess f x = q * bdry s v x

/-- No dart carries flow together with its reverse. -/
def NoAntiparallel (f : G.Dart → ℤ) : Prop := ∀ d, f d = 1 → f d.symm = 0

theorem excess_sub (f g : G.Dart → ℤ) (x : V) : excess (f - g) x = excess f x - excess g x := by
  simp [excess, sub_mul, sum_sub_distrib]

/-- Telescoping along a walk. -/
theorem sum_bdry_darts {a b : V} (p : G.Walk a b) (x : V) :
    (p.darts.map fun d => bdry d.fst d.snd x).sum = bdry a b x := by
  induction p with
  | nil => simp [bdry]
  | cons h p ih => simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]; simp [bdry]

theorem sum_indicator_list {β : Type*} [AddCommMonoid β] {l : List G.Dart} (hl : l.Nodup)
    (g : G.Dart → β) : ∑ d, (if d ∈ l then g d else 0) = (l.map g).sum := by
  rw [← sum_filter, ← List.sum_toFinset g hl]
  congr 1
  ext; simp

/-- The flow of a single walk. -/
def walkFlow {a b : V} (p : G.Walk a b) (d : G.Dart) : ℤ := if d ∈ p.darts then 1 else 0

theorem excess_walkFlow {a b : V} (p : G.Walk a b) (hp : p.darts.Nodup) (x : V) :
    excess (walkFlow p) x = bdry a b x := by
  unfold excess walkFlow
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [sum_indicator_list hp, sum_bdry_darts]

theorem sum_walkFlow {a b : V} (p : G.Walk a b) (hp : p.darts.Nodup) :
    ∑ d, walkFlow p d = p.length := by
  unfold walkFlow
  have := sum_indicator_list hp (fun _ => (1 : ℤ))
  simp only [List.map_const', List.sum_replicate] at this
  rw [this, SimpleGraph.Walk.length_darts]
  simp

/-! ### The flow of a path family -/

namespace DisjointPaths

variable {s v : V} {q : ℕ}

/-- The unit flow carried by an edge-disjoint path family. -/
def pathFlow (P : DisjointPaths G s v q) : G.Dart → ℤ := fun d => ∑ i, walkFlow (P.path i) d

theorem pathFlow_eq (P : DisjointPaths G s v q) (d : G.Dart) :
    P.pathFlow d = if ∃ i, d ∈ (P.path i).darts then 1 else 0 := by
  unfold pathFlow walkFlow
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have : d ∉ (P.path j).darts := fun hj => P.edge_ne_of_mem_darts hji hj hi rfl
      simp [this]
    · simp
  · push Not at h
    simp [h]

theorem pathFlow_zero_or_one (P : DisjointPaths G s v q) (d : G.Dart) :
    P.pathFlow d = 0 ∨ P.pathFlow d = 1 := by
  rw [pathFlow_eq]; split_ifs <;> simp

theorem excess_pathFlow (P : DisjointPaths G s v q) (x : V) :
    excess P.pathFlow x = q * bdry s v x := by
  unfold excess pathFlow
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [← excess.eq_def, excess_walkFlow _ (P.darts_nodup _)]
  simp

theorem isUnitFlow_pathFlow (P : DisjointPaths G s v q) : IsUnitFlow s v P.pathFlow q :=
  ⟨P.pathFlow_zero_or_one, P.excess_pathFlow⟩

theorem sum_pathFlow (P : DisjointPaths G s v q) : ∑ d, P.pathFlow d = P.totalLength := by
  unfold pathFlow totalLength
  rw [sum_comm]
  push_cast
  exact sum_congr rfl fun i _ => sum_walkFlow _ (P.darts_nodup i)

theorem noAntiparallel_pathFlow (P : DisjointPaths G s v q) : NoAntiparallel P.pathFlow := by
  intro d hd
  rw [pathFlow_eq] at hd ⊢
  split_ifs at hd with h
  · obtain ⟨i, hi⟩ := h
    rw [if_neg]
    rintro ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      -- `d` and its reverse would both be darts of one path, repeating the edge `d.edge`
      have hnd := P.edges_nodup i
      unfold SimpleGraph.Walk.edges at hnd
      have := List.inj_on_of_nodup_map hnd hi hj (SimpleGraph.Dart.edge_symm d).symm
      exact d.symm_ne this.symm
    · exact P.edge_ne_of_mem_darts hij hi hj (SimpleGraph.Dart.edge_symm d).symm
  · simp at hd

end DisjointPaths

/-! ### Cancelling antiparallel flow -/

/-- Remove flow from every pair of opposite darts that both carry flow. -/
def cancelFlow (f : G.Dart → ℤ) (d : G.Dart) : ℤ := if f d = 1 ∧ f d.symm = 1 then 0 else f d

theorem excess_symm_invariant (g : G.Dart → ℤ) (hg : ∀ d, g d.symm = g d) (x : V) :
    excess g x = 0 := by
  unfold excess
  have h1 : ∑ d, g d * bdry d.fst d.snd x = ∑ d : G.Dart, g d.symm * bdry d.symm.fst d.symm.snd x :=
    (Equiv.sum_comp (SimpleGraph.Dart.symm_involutive.toPerm _)
      fun d : G.Dart => g d * bdry d.fst d.snd x).symm
  have h2 : ∀ d : G.Dart, g d.symm * bdry d.symm.fst d.symm.snd x = -(g d * bdry d.fst d.snd x) := by
    intro d; rw [hg]; simp [bdry]; ring
  simp_rw [h2, sum_neg_distrib] at h1
  linarith

theorem isUnitFlow_cancelFlow {s v : V} {f : G.Dart → ℤ} {q : ℤ} (hf : IsUnitFlow s v f q) :
    IsUnitFlow s v (cancelFlow f) q := by
  refine ⟨fun d => ?_, fun x => ?_⟩
  · unfold cancelFlow; split_ifs; · simp
    · exact hf.zero_or_one d
  · have : cancelFlow f = f - fun d => if f d = 1 ∧ f d.symm = 1 then 1 else 0 := by
      funext d; unfold cancelFlow; split_ifs with h <;> simp [h]
    rw [this, excess_sub, hf.conservation, excess_symm_invariant, sub_zero]
    intro d
    simp only [SimpleGraph.Dart.symm_symm]
    by_cases h : f d = 1 ∧ f d.symm = 1
    · rw [if_pos ⟨h.2, h.1⟩, if_pos h]
    · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h]

theorem cancelFlow_eq_one {f : G.Dart → ℤ} {d : G.Dart} (h : cancelFlow f d = 1) : f d = 1 := by
  unfold cancelFlow at h; split_ifs at h; · simp at h
  · exact h

theorem noAntiparallel_cancelFlow {s v : V} {f : G.Dart → ℤ} {q : ℤ} (hf : IsUnitFlow s v f q) :
    NoAntiparallel (cancelFlow f) := by
  intro d hd
  have hd1 : f d = 1 := cancelFlow_eq_one hd
  have hnot : ¬ (f d = 1 ∧ f d.symm = 1) := by
    intro h; unfold cancelFlow at hd; rw [if_pos h] at hd; exact zero_ne_one hd
  have hs : f d.symm = 0 := by
    rcases hf.zero_or_one d.symm with h | h
    · exact h
    · exact absurd ⟨hd1, h⟩ hnot
  unfold cancelFlow
  rw [if_neg]
  · exact hs
  · rintro ⟨h, _⟩; rw [hs] at h; exact zero_ne_one h

theorem cancelFlow_le (f : G.Dart → ℤ) (d : G.Dart) :
    cancelFlow f d ≤ f d := by
  unfold cancelFlow; split_ifs with h
  · rw [h.1]; norm_num
  · exact le_rfl


/-! ### Decomposition -/

/-- Flow cannot leave the set of vertices reachable from `s` along flow-carrying darts, so it must
reach `v`. -/
theorem exists_flow_walk {s v : V} {f : G.Dart → ℤ} {q : ℕ}
    (hf : IsUnitFlow s v f (q + 1)) : ∃ W : G.Walk s v, ∀ d ∈ W.darts, f d = 1 := by
  classical
  by_contra hno
  push Not at hno
  let R : Finset V := univ.filter fun x => ∃ W : G.Walk s x, ∀ d ∈ W.darts, f d = 1
  have hsR : s ∈ R := by simp only [R, mem_filter, mem_univ, true_and]; exact ⟨.nil, by simp⟩
  have hvR : v ∉ R := by
    simp only [R, mem_filter, mem_univ, true_and, not_exists]
    intro W hW; obtain ⟨d, hd, hne⟩ := hno W; exact hne (hW d hd)
  -- total excess of `R` computed from conservation
  have h1 : ∑ x ∈ R, excess f x = q + 1 := by
    simp_rw [hf.conservation]
    rw [← mul_sum]
    have : ∑ x ∈ R, bdry s v x = 1 := by
      simp [bdry, sum_sub_distrib, hsR, hvR]
    rw [this, mul_one]
  -- total excess of `R` computed dart by dart
  have h2 : ∑ x ∈ R, excess f x ≤ 0 := by
    unfold excess
    rw [sum_comm]
    refine sum_nonpos fun d _ => ?_
    rw [← mul_sum]
    rcases hf.zero_or_one d with h | h
    · simp [h]
    · rw [h, one_mul]
      simp only [bdry, sum_sub_distrib, sum_ite_eq, R]
      by_cases hfst : d.fst ∈ R
      · have hsnd : d.snd ∈ R := by
          simp only [R, mem_filter, mem_univ, true_and] at hfst ⊢
          obtain ⟨W, hW⟩ := hfst
          refine ⟨W.concat d.adj, fun d' hd' => ?_⟩
          simp only [SimpleGraph.Walk.darts_concat, List.concat_eq_append, List.mem_append,
            List.mem_singleton] at hd'
          rcases hd' with hd' | rfl
          · exact hW d' hd'
          · exact h
        simp only [R] at hfst hsnd
        rw [if_pos hfst, if_pos hsnd]; norm_num
      · simp only [R] at hfst
        rw [if_neg hfst]; split_ifs <;> norm_num
  omega

/-- **Flow decomposition.** A unit `s`–`v` flow of value `q` without antiparallel flow contains `q`
edge-disjoint `s`–`v` paths, of total length at most the size of the flow, using only
flow-carrying darts. -/
theorem exists_disjointPaths_of_isUnitFlow' {s v : V} :
    ∀ (q : ℕ) (f : G.Dart → ℤ), IsUnitFlow s v f q → NoAntiparallel f →
      ∃ P : DisjointPaths G s v q, (P.totalLength : ℤ) ≤ ∑ d, f d ∧
        ∀ i, ∀ d ∈ (P.path i).darts, f d = 1 := by
  intro q
  induction q with
  | zero =>
    intro f hf _
    refine ⟨DisjointPaths.empty G s v, ?_, fun i => i.elim0⟩
    simp only [DisjointPaths.totalLength_empty, Nat.cast_zero]
    exact sum_nonneg fun d _ => by rcases hf.zero_or_one d with h | h <;> simp [h]
  | succ q ih =>
    intro f hf hanti
    obtain ⟨W, hW⟩ := exists_flow_walk (by exact_mod_cast hf)
    set p := W.bypass
    have hp : p.IsPath := W.bypass_isPath
    have hpnd : p.darts.Nodup := List.Nodup.of_map _ hp.isTrail.edges_nodup
    have hpf : ∀ d ∈ p.darts, f d = 1 := fun d hd => hW d (W.darts_bypass_subset_darts hd)
    let f' := f - walkFlow p
    have hf'val : ∀ d, f' d = if d ∈ p.darts then 0 else f d := by
      intro d; simp only [f', Pi.sub_apply, walkFlow]; split_ifs with h
      · rw [hpf d h]; norm_num
      · simp
    have hf' : IsUnitFlow s v f' q := by
      refine ⟨fun d => ?_, fun x => ?_⟩
      · rw [hf'val]; split_ifs; · simp
        · exact hf.zero_or_one d
      · simp only [f']
        rw [excess_sub, hf.conservation, excess_walkFlow p hpnd]; push_cast; ring
    have hanti' : NoAntiparallel f' := by
      intro d hd
      rw [hf'val] at hd ⊢
      by_cases h1 : d ∈ p.darts
      · rw [if_pos h1] at hd; exact absurd hd zero_ne_one
      · rw [if_neg h1] at hd
        split_ifs
        · rfl
        · exact hanti d hd
    obtain ⟨P, hPlen, hPf⟩ := ih f' hf' hanti'
    have hdisj : ∀ i, p.edges.Disjoint (P.path i).edges := by
      intro i e he he'
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
      obtain ⟨d', hd', hde⟩ := List.mem_map.1 he'
      have h1 := hPf i d' hd'
      rcases (SimpleGraph.dart_edge_eq_iff d' d).1 hde with rfl | rfl
      · rw [hf'val, if_pos hd] at h1; exact zero_ne_one h1
      · rw [hf'val] at h1
        split_ifs at h1 with h
        · exact zero_ne_one h1
        · exact absurd (hanti d (hpf d hd)) (by rw [h1]; norm_num)
    refine ⟨P.cons p hp hdisj, ?_, fun i => ?_⟩
    · rw [DisjointPaths.totalLength_cons]
      have hsum : ∑ d, f' d = ∑ d, f d - p.length := by
        simp only [f', Pi.sub_apply, sum_sub_distrib, sum_walkFlow p hpnd]
      push_cast
      linarith
    · induction i using Fin.cases with
      | zero => simpa [DisjointPaths.cons] using hpf
      | succ i =>
        intro d hd
        have := hPf i d (by simpa [DisjointPaths.cons] using hd)
        rw [hf'val] at this; split_ifs at this; · simp at this
        · exact this

/-- Every unit `s`–`v` flow of value `q ≥ 0` contains `q` edge-disjoint `s`–`v` paths of total
length at most its size. -/
theorem exists_disjointPaths_of_isUnitFlow {s v : V} {q : ℕ} {f : G.Dart → ℤ}
    (hf : IsUnitFlow s v f q) :
    ∃ P : DisjointPaths G s v q, (P.totalLength : ℤ) ≤ ∑ d, f d := by
  obtain ⟨P, hP, -⟩ := exists_disjointPaths_of_isUnitFlow' q (cancelFlow f)
    (isUnitFlow_cancelFlow hf) (noAntiparallel_cancelFlow hf)
  exact ⟨P, hP.trans (sum_le_sum fun d _ => cancelFlow_le f d)⟩

end CodingGap
