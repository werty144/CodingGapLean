import Mathlib

/-!
# Integral maximum flows

The integral max-flow min-cut theorem on a finite directed network, in the direction used by the
multi-source reduction for coding (Appendix `app:multiple-sources`): if every `a`–`b` cut has
capacity at least `k`, there is an integral flow of value at least `k` (`exists_flow`).

The proof is the Ford–Fulkerson augmenting-path argument. The vertices reachable from `a` in the
residual network are explored in rounds (`ReachIn n`); a unit of flow can be pushed from `a` to
every vertex reachable within `n` rounds while only changing arcs between such vertices
(`exists_augment`). If `b` is unreachable, the reachable set is a saturated cut.
-/

namespace CodingGap.MaxFlow

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The net outflow of `x`. -/
def outflow (f : N → N → ℤ) (x : N) : ℤ := ∑ y, f x y - ∑ y, f y x

/-- `f` is a feasible integral `a`–`b` flow for the capacities `c`. -/
structure IsFlow (c : N → N → ℤ) (a b : N) (f : N → N → ℤ) : Prop where
  nonneg : ∀ x y, 0 ≤ f x y
  le_cap : ∀ x y, f x y ≤ c x y
  conserve : ∀ x, x ≠ a → x ≠ b → outflow f x = 0

/-- The capacity of the cut with source side `S`. -/
def cutCap (c : N → N → ℤ) (S : Finset N) : ℤ := ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y

/-- Summing net outflows over `S` leaves only the arcs crossing the boundary of `S`. -/
theorem sum_outflow (f : N → N → ℤ) (S : Finset N) :
    ∑ x ∈ S, outflow f x = ∑ x ∈ S, ∑ y ∈ Sᶜ, f x y - ∑ x ∈ S, ∑ y ∈ Sᶜ, f y x := by
  unfold outflow
  rw [sum_sub_distrib]
  have e1 : ∑ x ∈ S, ∑ y, f x y = ∑ x ∈ S, ∑ y ∈ S, f x y + ∑ x ∈ S, ∑ y ∈ Sᶜ, f x y := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun x _ => (sum_add_sum_compl S _).symm
  have e2 : ∑ x ∈ S, ∑ y, f y x = ∑ x ∈ S, ∑ y ∈ S, f y x + ∑ x ∈ S, ∑ y ∈ Sᶜ, f y x := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun x _ => (sum_add_sum_compl S _).symm
  have e3 : ∑ x ∈ S, ∑ y ∈ S, f y x = ∑ x ∈ S, ∑ y ∈ S, f x y := sum_comm
  rw [e1, e2, e3]
  ring

variable {c : N → N → ℤ} {a b : N}

/-- The value of a flow is the net flow across any cut. -/
theorem outflow_eq_cut {f : N → N → ℤ} (hf : IsFlow c a b f) {S : Finset N} (ha : a ∈ S)
    (hb : b ∉ S) :
    outflow f a = ∑ x ∈ S, ∑ y ∈ Sᶜ, f x y - ∑ x ∈ S, ∑ y ∈ Sᶜ, f y x := by
  rw [← sum_outflow, sum_eq_single a]
  · intro x hx hxa
    exact hf.conserve x hxa fun h => hb (h ▸ hx)
  · exact fun h => absurd ha h

/-! ### Augmenting paths -/

section Augment

variable (c) (a) (f : N → N → ℤ)

/-- The residual network: flow can be pushed from `x` to `y`. -/
def Residual (x y : N) : Prop := f x y < c x y ∨ 0 < f y x

/-- `y` is reachable from `a` in the residual network within `n` steps. -/
def ReachIn : ℕ → N → Prop
  | 0, y => y = a
  | n + 1, y => ReachIn n y ∨ ∃ x, ReachIn n x ∧ Residual c f x y

/-- Adding `d` to the flow on the arc `(x, y)`. -/
def addArc (g : N → N → ℤ) (x y : N) (d : ℤ) : N → N → ℤ :=
  fun u v => g u v + if u = x ∧ v = y then d else 0

variable {c a f}

theorem outflow_addArc (g : N → N → ℤ) (x y : N) (d : ℤ) (u : N) :
    outflow (addArc g x y d) u =
      outflow g u + (if u = x then d else 0) - (if u = y then d else 0) := by
  unfold outflow addArc
  rw [sum_add_distrib, sum_add_distrib]
  have h1 : ∑ v, (if u = x ∧ v = y then d else 0) = if u = x then d else 0 := by
    by_cases hu : u = x <;> simp [hu]
  have h2 : ∑ v, (if v = x ∧ u = y then d else 0) = if u = y then d else 0 := by
    by_cases hu : u = y <;> simp [hu]
  rw [h1, h2]
  ring

/-- A unit of flow can be pushed from `a` to every vertex reachable within `n` steps, changing
only arcs between vertices reachable within `n` steps. -/
theorem exists_augment (hf0 : ∀ x y, 0 ≤ f x y) (hfc : ∀ x y, f x y ≤ c x y) (n : ℕ) :
    ∀ y, ReachIn c a f n y → ∃ g : N → N → ℤ, (∀ u v, 0 ≤ g u v) ∧ (∀ u v, g u v ≤ c u v) ∧
      (∀ u, outflow g u = outflow f u + (if u = a then 1 else 0) - (if u = y then 1 else 0)) ∧
      (∀ u v, g u v ≠ f u v → ReachIn c a f n u ∧ ReachIn c a f n v) := by
  induction n with
  | zero =>
    intro y hy
    change y = a at hy
    subst hy
    exact ⟨f, hf0, hfc, fun u => by ring, fun u v h => absurd rfl h⟩
  | succ n ih =>
    intro y hy
    by_cases hyn : ReachIn c a f n y
    · obtain ⟨g, h0, hc, ho, hch⟩ := ih y hyn
      exact ⟨g, h0, hc, ho, fun u v h => ⟨Or.inl (hch u v h).1, Or.inl (hch u v h).2⟩⟩
    rcases hy with hy | ⟨x, hx, hR⟩
    · exact absurd hy hyn
    obtain ⟨g, h0, hc, ho, hch⟩ := ih x hx
    have hxy : g x y = f x y := by
      by_contra h; exact hyn (hch x y h).2
    have hyx : g y x = f y x := by
      by_contra h; exact hyn (hch y x h).1
    have hch' : ∀ (p q : N) (d : ℤ), (p = x ∧ q = y) ∨ (p = y ∧ q = x) →
        ∀ u v, addArc g p q d u v ≠ f u v →
          ReachIn c a f (n + 1) u ∧ ReachIn c a f (n + 1) v := by
      intro p q d hpq u v h
      by_cases huv : u = p ∧ v = q
      · obtain ⟨rfl, rfl⟩ := huv
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inl hx, Or.inr ⟨u, hx, hR⟩⟩
        · exact ⟨Or.inr ⟨v, hx, hR⟩, Or.inl hx⟩
      · have : g u v ≠ f u v := by simpa [addArc, huv] using h
        exact ⟨Or.inl (hch u v this).1, Or.inl (hch u v this).2⟩
    by_cases hp : 0 < f y x
    · refine ⟨addArc g y x (-1), fun u v => ?_, fun u v => ?_, fun u => ?_,
        hch' y x (-1) (Or.inr ⟨rfl, rfl⟩)⟩
      · unfold addArc
        split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; omega
        · simpa using h0 u v
      · unfold addArc
        split_ifs <;> linarith [hc u v]
      · rw [outflow_addArc, ho]
        split_ifs <;> ring
    · have hlt : f x y < c x y := hR.resolve_right hp
      refine ⟨addArc g x y 1, fun u v => ?_, fun u v => ?_, fun u => ?_,
        hch' x y 1 (Or.inl ⟨rfl, rfl⟩)⟩
      · unfold addArc
        split_ifs <;> linarith [h0 u v]
      · unfold addArc
        split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; omega
        · simpa using hc u v
      · rw [outflow_addArc, ho]
        split_ifs <;> ring

end Augment

/-- **Integral max-flow min-cut (the direction used here).** If every `a`–`b` cut has capacity at
least `k`, there is an integral `a`–`b` flow of value at least `k`. -/
theorem exists_flow (hc : ∀ x y, 0 ≤ c x y) (hab : a ≠ b) (k : ℕ)
    (hcut : ∀ S : Finset N, a ∈ S → b ∉ S → (k : ℤ) ≤ cutCap c S) :
    ∃ f, IsFlow c a b f ∧ (k : ℤ) ≤ outflow f a := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, hc, fun x _ _ => by simp [outflow]⟩, ?_⟩
    simp [outflow]
  | succ k ih =>
    obtain ⟨f, hf, hk⟩ := ih fun S ha hb => by have := hcut S ha hb; push_cast at this; linarith
    by_cases hdone : ((k + 1 : ℕ) : ℤ) ≤ outflow f a
    · exact ⟨f, hf, hdone⟩
    by_cases hb : ∃ n, ReachIn c a f n b
    · obtain ⟨n, hn⟩ := hb
      obtain ⟨g, h0, hcap, ho, -⟩ := exists_augment hf.nonneg hf.le_cap n b hn
      refine ⟨g, ⟨h0, hcap, fun x hxa hxb => ?_⟩, ?_⟩
      · rw [ho, hf.conserve x hxa hxb]; simp [hxa, hxb]
      · rw [ho]; simp [hab]; linarith
    · exfalso
      push Not at hb
      let S : Finset N := univ.filter fun y => ∃ n, ReachIn c a f n y
      have haS : a ∈ S := by simp only [S, mem_filter, mem_univ, true_and]; exact ⟨0, rfl⟩
      have hbS : b ∉ S := by simpa [S] using hb
      have hcross : ∀ x ∈ S, ∀ y ∈ Sᶜ, f x y = c x y ∧ f y x = 0 := by
        intro x hx y hy
        simp only [S, mem_filter, mem_univ, true_and] at hx
        simp only [S, mem_compl, mem_filter, mem_univ, true_and, not_exists] at hy
        obtain ⟨n, hn⟩ := hx
        have hnR : ¬ Residual c f x y := fun h => hy (n + 1) (Or.inr ⟨x, hn, h⟩)
        simp only [Residual, not_or, not_lt] at hnR
        exact ⟨le_antisymm (hf.le_cap x y) hnR.1, le_antisymm hnR.2 (hf.nonneg y x)⟩
      have hval : outflow f a = cutCap c S := by
        rw [outflow_eq_cut hf haS hbS, cutCap]
        have h1 : ∑ x ∈ S, ∑ y ∈ Sᶜ, f x y = ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y :=
          sum_congr rfl fun x hx => sum_congr rfl fun y hy => (hcross x hx y hy).1
        have h2 : ∑ x ∈ S, ∑ y ∈ Sᶜ, f y x = 0 :=
          sum_eq_zero fun x hx => sum_eq_zero fun y hy => (hcross x hx y hy).2
        rw [h1, h2, sub_zero]
      exact hdone (hval ▸ hcut S haS hbS)

end CodingGap.MaxFlow
