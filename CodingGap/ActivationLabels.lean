import CodingGap.LowerBound

/-!
# Cuts as activation labels (`eq:temporal-label-capacity`)

A finite temporal cut is upward closed along every time chain, so it is described by an
*activation label* `a u ∈ {0, …, T+1}` for every vertex `u`: `(u,t)` lies on the source side iff
`t ≥ a u`. The communication arc `(u,t) → (w,t+1)` crosses the cut iff `a u ≤ t < a w - 1`, so
the directed pair `(u,w)` contributes `[a w - a u - 1]₊` crossing arcs.

* `labelCost G a = ∑_{(u,w) adjacent} [a w - a u - 1]₊` (the sum over ordered pairs, i.e. both
  directions of every edge; for an undirected edge the two terms add up to `[|a u - a w| - 1]₊`).
* `temporalMinCut_eq_sInf_labelCost` (**`eq:temporal-label-capacity`**):
  `C_T(s,v) = min {labelCost a : a s = 0, a v = T + 1, a ≤ T + 1}`.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered pairs of adjacent vertices (the directed arcs of the bidirected graph). -/
def adjPairs : Finset (V × V) :=
  (univ ×ˢ univ).filter fun p => G.Adj p.1 p.2

@[simp] theorem mem_adjPairs {p : V × V} : p ∈ adjPairs G ↔ G.Adj p.1 p.2 := by
  simp [adjPairs]

/-- The cut cost of an activation labelling: `∑_{(u,w) adjacent} [a w - a u - 1]₊`. -/
def labelCost (a : V → ℕ) : ℕ :=
  ∑ p ∈ adjPairs G, (a p.2 - (a p.1 + 1))

/-- `a` is an admissible activation labelling for an `(s,0)`–`(v,T)` cut. -/
structure IsCutLabel (s v : V) (T : ℕ) (a : V → ℕ) : Prop where
  source : a s = 0
  sink : a v = T + 1
  le : ∀ u, a u ≤ T + 1

/-- The source side of the cut defined by a labelling. -/
def labelSet (a : V → ℕ) : Set (V × ℕ) := {x | a x.1 ≤ x.2}

variable {G}

theorem IsCutLabel.isTemporalCut {s v : V} {T : ℕ} {a : V → ℕ} (h : IsCutLabel s v T a) :
    IsTemporalCut s v T (labelSet a) where
  source_mem := by simp [labelSet, h.source]
  sink_not_mem := by simp [labelSet, h.sink]
  storage_closed u t _ hu := by simp only [labelSet, Set.mem_ofPred_eq] at hu ⊢; omega

variable (G)

open Classical in
/-- The cut capacity, organised by directed pairs of adjacent vertices. -/
theorem cutCapacity_eq_sum (T : ℕ) (S : Set (V × ℕ)) :
    cutCapacity G T S =
      ∑ p ∈ adjPairs G, ((range T).filter fun t => (p.1, t) ∈ S ∧ (p.2, t + 1) ∉ S).card := by
  unfold cutCapacity
  rw [card_eq_sum_card_fiberwise (f := fun x : V × V × ℕ => (x.1, x.2.1)) (t := adjPairs G)]
  · refine sum_congr rfl fun p hp => ?_
    have hinj : Function.Injective fun t : ℕ => (p.1, p.2, t) := fun t t' h => by simpa using h
    rw [← card_image_of_injective
      ((range T).filter fun t => (p.1, t) ∈ S ∧ (p.2, t + 1) ∉ S) hinj]
    apply congrArg Finset.card
    ext ⟨u, w, t⟩
    unfold cutArcs
    simp only [commArcs, mem_filter, mem_product, mem_univ, mem_range, true_and,
      mem_image, Prod.mk.injEq]
    rw [mem_adjPairs] at hp
    constructor
    · rintro ⟨⟨⟨ht, _⟩, hS⟩, rfl⟩
      exact ⟨t, ⟨ht, hS⟩, rfl, rfl, rfl⟩
    · rintro ⟨t, ⟨ht, hS⟩, rfl, rfl, rfl⟩
      exact ⟨⟨⟨ht, hp⟩, hS⟩, rfl⟩
  · intro x hx
    unfold cutArcs at hx
    rw [mem_coe, mem_filter] at hx
    have := (mem_filter.1 hx.1).2
    simpa using this

/-- The number of rounds in which the arc `u → w` crosses the cut defined by a labelling. -/
theorem card_crossing_labelSet {T : ℕ} {a : V → ℕ} (ha : ∀ u, a u ≤ T + 1) (u w : V) :
    ((range T).filter fun t => a u ≤ t ∧ ¬ a w ≤ t + 1).card = a w - (a u + 1) := by
  have : ((range T).filter fun t => a u ≤ t ∧ ¬ a w ≤ t + 1) = Ico (a u) (a w - 1) := by
    ext t
    simp only [mem_filter, mem_range, mem_Ico]
    have := ha w
    omega
  rw [this, Nat.card_Ico]
  omega

/-- The capacity of the cut defined by a labelling is its label cost. -/
theorem cutCapacity_labelSet {T : ℕ} {a : V → ℕ} (ha : ∀ u, a u ≤ T + 1) :
    cutCapacity G T (labelSet a) = labelCost G a := by
  classical
  rw [cutCapacity_eq_sum, labelCost]
  refine sum_congr rfl fun p _ => ?_
  simpa [labelSet] using card_crossing_labelSet ha p.1 p.2

/-- The capacity of a cut depends only on the time copies `0, …, T`. -/
theorem cutCapacity_congr {T : ℕ} {S S' : Set (V × ℕ)}
    (h : ∀ u t, t ≤ T → ((u, t) ∈ S ↔ (u, t) ∈ S')) : cutCapacity G T S = cutCapacity G T S' := by
  classical
  unfold cutCapacity cutArcs
  congr 1
  refine filter_congr fun x hx => ?_
  simp only [commArcs, mem_filter, mem_product, mem_range] at hx
  rw [h _ _ hx.1.2.2.le, h _ _ hx.1.2.2]

/-- Upward closure of a finite temporal cut along a time chain. -/
theorem IsTemporalCut.mono {s v : V} {T : ℕ} {S : Set (V × ℕ)} (hS : IsTemporalCut s v T S)
    {u : V} {t t' : ℕ} (htt' : t ≤ t') (ht' : t' ≤ T) (hu : (u, t) ∈ S) : (u, t') ∈ S := by
  induction t', htt' using Nat.le_induction with
  | base => exact hu
  | succ n hn ih => exact hS.storage_closed u n ht' (ih (by omega))

/-- The activation label of a vertex with respect to a cut: its first time copy on the source
side, or `T + 1` if there is none. -/
noncomputable def cutLabel (T : ℕ) (S : Set (V × ℕ)) (u : V) : ℕ :=
  sInf ({t | t ≤ T ∧ (u, t) ∈ S} ∪ {T + 1})

theorem cutLabel_le (T : ℕ) (S : Set (V × ℕ)) (u : V) : cutLabel T S u ≤ T + 1 :=
  Nat.sInf_le (Or.inr rfl)

theorem mem_iff_cutLabel_le {s v : V} {T : ℕ} {S : Set (V × ℕ)} (hS : IsTemporalCut s v T S)
    {u : V} {t : ℕ} (ht : t ≤ T) : (u, t) ∈ S ↔ cutLabel T S u ≤ t := by
  constructor
  · intro hu; exact Nat.sInf_le (Or.inl ⟨ht, hu⟩)
  · intro hle
    rcases Nat.sInf_mem (s := {t | t ≤ T ∧ (u, t) ∈ S} ∪ {T + 1}) ⟨T + 1, Or.inr rfl⟩ with
      h | h
    · exact hS.mono hle ht h.2
    · have : cutLabel T S u = T + 1 := h
      omega

theorem isCutLabel_cutLabel {s v : V} {T : ℕ} {S : Set (V × ℕ)} (hS : IsTemporalCut s v T S) :
    IsCutLabel s v T (cutLabel T S) where
  source := by
    have := (mem_iff_cutLabel_le hS (u := s) (Nat.zero_le T)).1 hS.source_mem
    omega
  sink := by
    have h1 := cutLabel_le T S v
    by_contra hne
    exact hS.sink_not_mem ((mem_iff_cutLabel_le hS le_rfl).2 (by omega))
  le := cutLabel_le T S

theorem cutCapacity_eq_labelCost_cutLabel {s v : V} {T : ℕ} {S : Set (V × ℕ)}
    (hS : IsTemporalCut s v T S) : cutCapacity G T S = labelCost G (cutLabel T S) := by
  rw [← cutCapacity_labelSet G (cutLabel_le T S)]
  exact cutCapacity_congr G fun u t ht => by
    rw [mem_iff_cutLabel_le hS ht]; rfl

/-- The set of cut capacities equals the set of label costs. -/
theorem cutCapacities_eq_labelCosts (s v : V) (T : ℕ) :
    {c | ∃ S, IsTemporalCut s v T S ∧ cutCapacity G T S = c} =
      {c | ∃ a, IsCutLabel s v T a ∧ labelCost G a = c} := by
  ext c
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨_, isCutLabel_cutLabel hS, (cutCapacity_eq_labelCost_cutLabel G hS).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ha.isTemporalCut, cutCapacity_labelSet G ha.le⟩

/-- **Activation-label formula** (`eq:temporal-label-capacity`).
`C_T(s,v) = min_{a s = 0, a v = T + 1, a ≤ T + 1} ∑_{(u,w) adjacent} [a w - a u - 1]₊`. -/
theorem temporalMinCut_eq_sInf_labelCost (s v : V) (T : ℕ) :
    temporalMinCut G s v T = sInf {c | ∃ a, IsCutLabel s v T a ∧ labelCost G a = c} := by
  rw [temporalMinCut, cutCapacities_eq_labelCosts]

theorem temporalMinCut_le_labelCost {s v : V} {T : ℕ} {a : V → ℕ} (ha : IsCutLabel s v T a) :
    temporalMinCut G s v T ≤ labelCost G a := by
  rw [← cutCapacity_labelSet G ha.le]
  exact temporalMinCut_le G ha.isTemporalCut

theorem exists_isCutLabel_labelCost_eq {s v : V} (hv : v ≠ s) (T : ℕ) :
    ∃ a, IsCutLabel s v T a ∧ labelCost G a = temporalMinCut G s v T := by
  obtain ⟨S, hS, h⟩ := exists_cut_temporalMinCut G hv T
  exact ⟨_, isCutLabel_cutLabel hS, (cutCapacity_eq_labelCost_cutLabel G hS).symm.trans h⟩

/-- Lower bounds on `C_T(s,v)` may be checked on labellings. -/
theorem le_temporalMinCut_of_labelCost {s v : V} (hv : v ≠ s) {T c : ℕ}
    (h : ∀ a, IsCutLabel s v T a → c ≤ labelCost G a) : c ≤ temporalMinCut G s v T := by
  obtain ⟨a, ha, he⟩ := exists_isCutLabel_labelCost_eq G hv T
  exact he ▸ h a ha

end CodingGap
