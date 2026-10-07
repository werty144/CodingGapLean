import Mathlib

/-!
# Feasible potentials from the absence of negative cycles

A generic Bellman–Ford lemma used in the proof of `eq:ff-cut-value` (residual potentials).

Let `ι` be a finite set of arcs on a finite vertex set `α`, with tails `src`, heads `dst` and
integer costs `cost`. If every *simple* closed walk has nonnegative total cost, then there is a
potential `p : α → ℤ` with `p (dst i) ≤ p (src i) + cost i` for every arc `i`.

The potential is the Bellman–Ford value after `|α|` rounds (equivalently, the shortest-walk
distance from a virtual source joined to every vertex by a zero-cost arc). If one more round still
improved some value, following the improvements backwards would produce a walk with a repeated
vertex; the closest repetition is a simple cycle of negative cost.
-/

namespace CodingGap.Potentials

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
  (src dst : ι → α) (cost : ι → ℤ)

/-- Every simple closed walk has nonnegative cost. A closed walk of length `m` visits the vertices
`x 0, …, x m = x 0` using the arcs `e 0, …, e (m - 1)`; it is simple when `x 0, …, x (m - 1)` are
distinct. -/
def NoNegSimpleCycle : Prop :=
  ∀ (m : ℕ) (x : ℕ → α) (e : ℕ → ι), 0 < m →
    (∀ t < m, src (e t) = x t ∧ dst (e t) = x (t + 1)) → x m = x 0 →
    (∀ a < m, ∀ b < m, x a = x b → a = b) → 0 ≤ ∑ t ∈ range m, cost (e t)

/-- Bellman–Ford values: `bf j y` is the minimum cost of a walk with at most `j` arcs ending at `y`
(starting anywhere, the empty walk having cost `0`). -/
noncomputable def bf : ℕ → α → ℤ
  | 0 => fun _ => 0
  | j + 1 => fun y =>
      (insert (bf j y) ((univ.filter fun i => dst i = y).image fun i => bf j (src i) + cost i)).min'
        (insert_nonempty _ _)

variable {src dst cost}

theorem bf_succ_le (j : ℕ) (y : α) : bf src dst cost (j + 1) y ≤ bf src dst cost j y :=
  min'_le _ _ (mem_insert_self _ _)

theorem bf_succ_le_arc (j : ℕ) (i : ι) :
    bf src dst cost (j + 1) (dst i) ≤ bf src dst cost j (src i) + cost i :=
  min'_le _ _ (mem_insert_of_mem (mem_image.2 ⟨i, by simp, rfl⟩))

theorem exists_arc_of_bf_succ_lt {j : ℕ} {y : α}
    (h : bf src dst cost (j + 1) y < bf src dst cost j y) :
    ∃ i, dst i = y ∧ bf src dst cost (j + 1) y = bf src dst cost j (src i) + cost i := by
  have hmem := min'_mem (insert (bf src dst cost j y)
    ((univ.filter fun i => dst i = y).image fun i => bf src dst cost j (src i) + cost i))
    (insert_nonempty _ _)
  change bf src dst cost (j + 1) y ∈ _ at hmem
  rcases mem_insert.1 hmem with h' | h'
  · exact absurd h' h.ne
  · obtain ⟨i, hi, he⟩ := mem_image.1 h'
    exact ⟨i, (mem_filter.1 hi).2, he.symm⟩

theorem bf_antitone {j j' : ℕ} (h : j ≤ j') (y : α) :
    bf src dst cost j' y ≤ bf src dst cost j y := by
  induction j', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (bf_succ_le n y).trans ih

/-- Following improvements backwards: if round `j + 1` improves `y`, there is a chain of arcs
`e 0, …, e j` through `x 0, …, x (j + 1) = y` along which every round improves. -/
theorem exists_improving_chain {j : ℕ} {y : α}
    (h : bf src dst cost (j + 1) y < bf src dst cost j y) :
    ∃ (x : ℕ → α) (e : ℕ → ι), x (j + 1) = y ∧ ∀ l ≤ j,
      src (e l) = x l ∧ dst (e l) = x (l + 1) ∧
      bf src dst cost (l + 1) (x (l + 1)) = bf src dst cost l (x l) + cost (e l) ∧
      bf src dst cost (l + 1) (x (l + 1)) < bf src dst cost l (x (l + 1)) := by
  induction j generalizing y with
  | zero =>
    obtain ⟨i, hi, he⟩ := exists_arc_of_bf_succ_lt h
    refine ⟨fun l => if l = 0 then src i else y, fun _ => i, by simp, fun l hl => ?_⟩
    obtain rfl : l = 0 := by omega
    simp only [zero_add, if_neg one_ne_zero]
    exact ⟨rfl, hi, he, h⟩
  | succ j ih =>
    obtain ⟨i, hi, he⟩ := exists_arc_of_bf_succ_lt h
    have himp : bf src dst cost (j + 1) (src i) < bf src dst cost j (src i) := by
      have := bf_succ_le_arc (src := src) (dst := dst) (cost := cost) j i
      have := bf_succ_le (src := src) (dst := dst) (cost := cost) (j + 1) y
      rw [hi] at *
      omega
    obtain ⟨x, e, hx, hchain⟩ := ih himp
    refine ⟨fun l => if l = j + 2 then y else x l, fun l => if l = j + 1 then i else e l,
      by simp, fun l hl => ?_⟩
    rcases Nat.lt_or_ge l (j + 1) with hl' | hl'
    · have := hchain l (by omega)
      simpa [show l ≠ j + 2 by omega, show l + 1 ≠ j + 2 by omega, show l ≠ j + 1 by omega]
        using this
    · obtain rfl : l = j + 1 := by omega
      simp only [if_neg (show j + 1 ≠ j + 2 by omega)]
      exact ⟨hx.symm, hi, hx ▸ he, h⟩

/-- **Feasible potentials.** If no simple cycle has negative cost, some potential satisfies
`p (dst i) ≤ p (src i) + cost i` for every arc `i`. -/
theorem exists_potential (h : NoNegSimpleCycle src dst cost) :
    ∃ p : α → ℤ, ∀ i, p (dst i) ≤ p (src i) + cost i := by
  set N := Fintype.card α
  suffices hstab : ∀ y, bf src dst cost (N + 1) y = bf src dst cost N y by
    exact ⟨bf src dst cost N, fun i => hstab (dst i) ▸ bf_succ_le_arc N i⟩
  intro y
  refine le_antisymm (bf_succ_le N y) (not_lt.1 fun hlt => ?_)
  obtain ⟨x, e, -, hchain⟩ := exists_improving_chain hlt
  -- two of the `N + 1` improved vertices `x 1, …, x (N + 1)` coincide
  have hrep : ∃ d, 0 < d ∧ ∃ a, 1 ≤ a ∧ a + d ≤ N + 1 ∧ x a = x (a + d) := by
    obtain ⟨a, ha, b, hb, hab, hx⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Icc 1 (N + 1)) (t := (univ : Finset α)) (f := x) (by simp [N])
      (fun _ _ => mem_univ _)
    simp only [mem_Icc] at ha hb
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · exact ⟨b - a, by omega, a, ha.1, by omega, by rw [hx]; congr 1; omega⟩
    · exact ⟨a - b, by omega, b, hb.1, by omega, by rw [← hx]; congr 1; omega⟩
  classical
  let d := Nat.find hrep
  obtain ⟨hd, a, ha1, had, hxa⟩ := Nat.find_spec hrep
  have hmin : ∀ d' < d, ¬ (0 < d' ∧ ∃ a, 1 ≤ a ∧ a + d' ≤ N + 1 ∧ x a = x (a + d')) :=
    fun d' hd' => Nat.find_min hrep hd'
  -- telescoping the cost along the cycle
  have htel : ∀ d' ≤ d, ∑ t ∈ range d', cost (e (a + t)) =
      bf src dst cost (a + d') (x (a + d')) - bf src dst cost a (x a) := by
    intro d' hd'
    induction d' with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih (by omega)]
      have := (hchain (a + n) (by omega)).2.2.1
      rw [show a + (n + 1) = a + n + 1 by ring, this]
      ring
  have hneg : ∑ t ∈ range d, cost (e (a + t)) < 0 := by
    rw [htel d le_rfl]
    have himp := (hchain (a + d - 1) (by omega)).2.2.2
    rw [show a + d - 1 + 1 = a + d by omega] at himp
    have hmono := bf_antitone (src := src) (dst := dst) (cost := cost)
      (show a ≤ a + d - 1 by omega) (x (a + d))
    rw [← hxa] at himp hmono ⊢
    omega
  refine absurd (h d (fun t => x (a + t)) (fun t => e (a + t)) hd (fun t ht => ?_) ?_ ?_) (not_le.2 hneg)
  · have := hchain (a + t) (by omega)
    exact ⟨this.1, by simpa [add_assoc] using this.2.1⟩
  · simpa using hxa.symm
  · intro t₁ ht₁ t₂ ht₂ hx
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hmin (t₂ - t₁) (by omega) ⟨by omega, a + t₁, by omega, by omega,
        by rw [hx]; congr 1; omega⟩
    · exact hmin (t₁ - t₂) (by omega) ⟨by omega, a + t₂, by omega, by omega,
        by rw [← hx]; congr 1; omega⟩

end CodingGap.Potentials
