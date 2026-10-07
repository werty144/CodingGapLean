import CodingGap.ActivationLabels
import CodingGap.DartFlow
import CodingGap.Potentials

/-!
# The discrete maximum flow over time (`eq:ff-cut-value`, in path form)

For a family `P` of `q` edge-disjoint `s`–`v` paths, its *value at horizon `T`* is
`∑ᵢ (T + 1 - |Pᵢ|) = q (T + 1) - L(P)`: repeating every path of length `ℓ ≤ T` at the departure
times `0, …, T - ℓ` delivers `T + 1 - ℓ` packets by time `T`.

* `value_le_temporalMinCut` (the flow side, `C_T(s,v) ≥ J`): every temporal cut has capacity at
  least the value of every path family.
* `exists_value_eq_temporalMinCut` (the cut side, `C_T(s,v) ≤ J`): for a path family of maximum
  value, the shortest-path potentials of the residual network, truncated to `{0, …, T + 1}`, form an
  activation labelling (`eq:temporal-label-capacity`) of cost at most its value. Optimality of the family excludes
  negative residual cycles: augmenting along one and decomposing the result (`DartFlow`) would give
  a family of larger value.
* `exists_value_eq_temporalMinCut_short`: the maximum can be attained by a family all of whose
  paths have length at most `T` (the tie-breaking step of the paper).
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The value `∑ᵢ (T + 1 - |Pᵢ|) = q (T + 1) - L(P)` of a path family at horizon `T`. -/
def DisjointPaths.value {s v : V} {q : ℕ} (T : ℕ) (P : DisjointPaths G s v q) : ℤ :=
  q * (T + 1) - P.totalLength

/-! ### Sums over darts -/

omit [DecidableEq V] in
theorem sum_adjPairs {β : Type*} [AddCommMonoid β] (g : V × V → β) :
    ∑ p ∈ adjPairs G, g p = ∑ d : G.Dart, g d.toProd := by
  classical
  have : adjPairs G = univ.image fun d : G.Dart => d.toProd := by
    ext ⟨u, w⟩
    simp only [mem_adjPairs, mem_image, mem_univ, true_and]
    refine ⟨fun h => ⟨⟨(u, w), h⟩, rfl⟩, ?_⟩
    rintro ⟨d, hd⟩
    have := d.adj
    rwa [show d.fst = u from congrArg Prod.fst hd, show d.snd = w from congrArg Prod.snd hd]
      at this
  rw [this, sum_image fun d _ d' _ h => SimpleGraph.Dart.ext _ _ h]

theorem labelCost_eq_sum_darts (a : V → ℕ) :
    (labelCost G a : ℤ) = ∑ d : G.Dart, ((a d.snd - (a d.fst + 1) : ℕ) : ℤ) := by
  rw [labelCost, sum_adjPairs (fun p => a p.2 - (a p.1 + 1))]
  push_cast
  rfl

/-- Summation by parts for dart flows. -/
theorem sum_flow_potential (f : G.Dart → ℤ) (p : V → ℤ) :
    ∑ d, f d * (p d.snd - p d.fst) = -∑ x, p x * excess f x := by
  unfold excess
  simp_rw [mul_sum]
  rw [sum_comm]
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun d _ => ?_
  have : ∑ x, p x * (f d * bdry d.fst d.snd x) = f d * (p d.fst - p d.snd) := by
    simp only [bdry, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq, mem_univ,
      if_true]
    ring
  rw [this]; ring

theorem sum_flow_potential_of_isUnitFlow {s v : V} {f : G.Dart → ℤ} {q : ℤ}
    (hf : IsUnitFlow s v f q) (p : V → ℤ) :
    ∑ d, f d * (p d.snd - p d.fst) = q * (p v - p s) := by
  rw [sum_flow_potential]
  simp_rw [hf.conservation]
  simp only [bdry, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq, mem_univ,
    if_true]
  ring

/-! ### The flow side: `C_T(s,v) ≥ J` -/

section FlowSide

variable {s v : V} {q : ℕ}

/-- Every activation labelling costs at least the value of every path family. -/
theorem value_le_labelCost (P : DisjointPaths G s v q) {T : ℕ} {a : V → ℕ}
    (ha : IsCutLabel s v T a) : P.value T ≤ labelCost G a := by
  rw [labelCost_eq_sum_darts]
  have hval : P.value T = ∑ d, P.pathFlow d * ((a d.snd : ℤ) - a d.fst - 1) := by
    have h1 := sum_flow_potential_of_isUnitFlow P.isUnitFlow_pathFlow (fun x => (a x : ℤ))
    have h2 := P.sum_pathFlow
    simp only [mul_sub, mul_one, sum_sub_distrib] at h1 ⊢
    rw [h1, h2, ha.sink, ha.source, DisjointPaths.value]
    push_cast; ring
  rw [hval]
  refine sum_le_sum fun d _ => ?_
  rcases P.pathFlow_zero_or_one d with h | h <;> rw [h] <;> omega

/-- **Maximum flow over time, flow side.** `C_T(s,v) ≥ ∑ᵢ (T + 1 - |Pᵢ|)` for every family of edge-disjoint
`s`–`v` paths. -/
theorem value_le_temporalMinCut (hv : v ≠ s) (T : ℕ) (P : DisjointPaths G s v q) :
    P.value T ≤ temporalMinCut G s v T := by
  obtain ⟨a, ha, he⟩ := exists_isCutLabel_labelCost_eq G hv T
  rw [← he]
  exact value_le_labelCost P ha

end FlowSide

/-! ### The residual network of a unit flow -/

section Residual

/-- Residual arcs: `inl d` is the forward copy of the dart `d` (usable when `d` carries no flow),
`inr (inl d)` is the reverse of the dart `d` (usable when `d` carries flow), `inr (inr true)` is
the artificial return arc `v → s` of cost `-H`, and `inr (inr false)` is its reverse `s → v`
(usable when the return arc carries flow). -/
abbrev RArc (G : SimpleGraph V) := G.Dart ⊕ G.Dart ⊕ Bool

variable (s v : V)

def RArc.src : RArc G → V
  | .inl d => d.fst
  | .inr (.inl d) => d.snd
  | .inr (.inr true) => v
  | .inr (.inr false) => s

def RArc.dst : RArc G → V
  | .inl d => d.snd
  | .inr (.inl d) => d.fst
  | .inr (.inr true) => s
  | .inr (.inr false) => v

def RArc.cost (H : ℤ) : RArc G → ℤ
  | .inl _ => 1
  | .inr (.inl _) => -1
  | .inr (.inr true) => -H
  | .inr (.inr false) => H

/-- The residual arcs of the flow `f` with `q` units on the return arc. -/
def RArc.valid (f : G.Dart → ℤ) (q : ℤ) : RArc G → Prop
  | .inl d => f d = 0
  | .inr (.inl d) => f d = 1
  | .inr (.inr true) => True
  | .inr (.inr false) => 0 < q

/-- The change of the dart flow when augmenting along a residual arc. -/
def RArc.delta (a : RArc G) (d : G.Dart) : ℤ :=
  (if a = .inl d then 1 else 0) - (if a = .inr (.inl d) then 1 else 0)

/-- The change of the return-arc flow when augmenting along a residual arc. -/
def RArc.qdelta (a : RArc G) : ℤ :=
  (if a = .inr (.inr true) then 1 else 0) - (if a = .inr (.inr false) then 1 else 0)

instance RArc.decidableValid (f : G.Dart → ℤ) (q : ℤ) : DecidablePred (RArc.valid f q) :=
  fun a => match a with
  | .inl d => inferInstanceAs (Decidable (f d = 0))
  | .inr (.inl d) => inferInstanceAs (Decidable (f d = 1))
  | .inr (.inr true) => inferInstanceAs (Decidable True)
  | .inr (.inr false) => inferInstanceAs (Decidable (0 < q))

variable {s v}

theorem RArc.excess_delta (a : RArc G) (x : V) :
    excess a.delta x - a.qdelta * bdry s v x = bdry (a.src s v) (a.dst s v) x := by
  rcases a with d | d | _ | _ <;>
    simp [excess, RArc.delta, RArc.qdelta, RArc.src, RArc.dst, bdry] <;> split_ifs <;> simp_all

theorem RArc.sum_delta (H : ℤ) (a : RArc G) : ∑ d, a.delta d - H * a.qdelta = a.cost H := by
  rcases a with d | d | _ | _ <;> simp [RArc.delta, RArc.qdelta, RArc.cost]

end Residual

/-! ### Optimal families admit no negative residual cycle -/

section Optimal

variable {s v : V} {T q : ℕ} (P : DisjointPaths G s v q)

/-- `P` has maximum value among all edge-disjoint path families. -/
def IsOptimal (T : ℕ) : Prop := ∀ (q' : ℕ) (P' : DisjointPaths G s v q'), P'.value T ≤ P.value T

/-- Augmenting an optimal family along a simple residual cycle cannot decrease the cost. -/
theorem noNegSimpleCycle_of_isOptimal (hopt : IsOptimal P T) :
    Potentials.NoNegSimpleCycle (α := V) (ι := {a : RArc G // a.valid P.pathFlow q})
      (fun a => a.1.src s v) (fun a => a.1.dst s v) (fun a => a.1.cost (T + 1)) := by
  intro m x e hm harc hclosed hsimple
  beta_reduce at harc
  by_contra hneg
  push Not at hneg
  -- the arcs of the cycle, as a finset
  obtain ⟨E, hE⟩ : ∃ E : Finset (RArc G), E = (range m).image fun t => (e t).1 := ⟨_, rfl⟩
  have hinj : Set.InjOn (fun t => (e t).1) (range m) := by
    intro t₁ h₁ t₂ h₂ h
    have h' : (e t₁).1 = (e t₂).1 := h
    have : x t₁ = x t₂ := by
      rw [← (harc t₁ (by simpa using h₁)).1, ← (harc t₂ (by simpa using h₂)).1, h']
    exact hsimple t₁ (by simpa using h₁) t₂ (by simpa using h₂) this
  have hsumE : ∀ g : RArc G → ℤ, ∑ a ∈ E, g a = ∑ t ∈ range m, g (e t).1 := by
    intro g; rw [hE]; exact sum_image hinj
  have hvalid : ∀ a ∈ E, a.valid P.pathFlow q := by
    intro a ha
    rw [hE] at ha
    obtain ⟨t, -, rfl⟩ := mem_image.1 ha
    exact (e t).2
  -- the augmented flow
  obtain ⟨f', hf'⟩ : ∃ f' : G.Dart → ℤ, f' = fun d => P.pathFlow d + ∑ a ∈ E, a.delta d :=
    ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : ℤ, q' = q + ∑ a ∈ E, a.qdelta := ⟨_, rfl⟩
  have hf'd : ∀ d, f' d = P.pathFlow d + (if .inl d ∈ E then 1 else 0) -
      (if .inr (.inl d) ∈ E then 1 else 0) := by
    intro d
    simp only [hf', RArc.delta, sum_sub_distrib, sum_ite_eq', add_sub_assoc]
  have hq'' : q' = q + (if .inr (.inr true) ∈ E then 1 else 0) -
      (if .inr (.inr false) ∈ E then 1 else 0) := by
    simp only [hq', RArc.qdelta, sum_sub_distrib, sum_ite_eq', add_sub_assoc]
  have hf'unit : IsUnitFlow s v f' q' := by
    refine ⟨fun d => ?_, fun y => ?_⟩
    · rw [hf'd]
      have h1 : (.inl d : RArc G) ∈ E → P.pathFlow d = 0 := fun h => hvalid _ h
      have h2 : (.inr (.inl d) : RArc G) ∈ E → P.pathFlow d = 1 := fun h => hvalid _ h
      have h0 := P.pathFlow_zero_or_one d
      split_ifs with ha hb hb
      · have := h1 ha; have := h2 hb; omega
      · have := h1 ha; omega
      · have := h2 hb; omega
      · omega
    · have hexc : excess f' y = excess P.pathFlow y + ∑ a ∈ E, excess a.delta y := by
        simp only [excess, hf', add_mul, sum_add_distrib, sum_mul]
        rw [sum_comm (s := univ)]
      have htel : ∑ a ∈ E, (excess a.delta y - a.qdelta * bdry s v y) = 0 := by
        simp_rw [RArc.excess_delta]
        rw [hsumE (fun a => bdry (a.src s v) (a.dst s v) y)]
        have : ∀ t ∈ range m, bdry ((e t).1.src s v) ((e t).1.dst s v) y =
            (if x t = y then 1 else 0) - (if x (t + 1) = y then 1 else 0) := by
          intro t ht
          rw [(harc t (by simpa using ht)).1, (harc t (by simpa using ht)).2]; rfl
        rw [sum_congr rfl this, sum_range_sub' (fun t => if x t = y then (1 : ℤ) else 0), hclosed]
        simp
      rw [sum_sub_distrib, ← sum_mul] at htel
      rw [hexc, P.isUnitFlow_pathFlow.conservation, hq', add_mul]
      linarith
  have hq'nn : 0 ≤ q' := by
    have h2 : (.inr (.inr false) : RArc G) ∈ E → 0 < (q : ℤ) := fun h => hvalid _ h
    rw [hq'']
    by_cases h3 : (.inr (.inr false) : RArc G) ∈ E
    · have := h2 h3; split_ifs <;> omega
    · split_ifs <;> omega
  -- the cost changes by the cost of the cycle
  have hcost : ∑ d, f' d - (T + 1) * q' =
      ∑ d, P.pathFlow d - (T + 1) * q + ∑ t ∈ range m, (e t).1.cost (T + 1) := by
    rw [← hsumE, ← sum_congr rfl fun a _ => RArc.sum_delta ((T : ℤ) + 1) a]
    simp only [hf', hq', sum_add_distrib, sum_sub_distrib, mul_add, mul_sum]
    rw [sum_comm (s := univ)]
    ring
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q' = n := ⟨q'.toNat, (Int.toNat_of_nonneg hq'nn).symm⟩
  rw [hn] at hf'unit hcost
  obtain ⟨P', hP'⟩ := exists_disjointPaths_of_isUnitFlow hf'unit
  have := hopt n P'
  simp only [DisjointPaths.value] at this
  rw [P.sum_pathFlow] at hcost
  linarith

/-- The cut side of the maximum flow over time: an optimal family's value is at least `C_T(s,v)`. -/
theorem temporalMinCut_le_value_of_isOptimal (hopt : IsOptimal P T) :
    (temporalMinCut G s v T : ℤ) ≤ P.value T := by
  obtain ⟨p, hp⟩ := Potentials.exists_potential (noNegSimpleCycle_of_isOptimal P hopt)
  have hfwd : ∀ d, P.pathFlow d = 0 → p d.snd ≤ p d.fst + 1 := fun d h => hp ⟨.inl d, h⟩
  have hbwd : ∀ d, P.pathFlow d = 1 → p d.fst ≤ p d.snd - 1 := fun d h => by
    have := hp ⟨.inr (.inl d), h⟩; simp only [RArc.src, RArc.dst, RArc.cost] at this; linarith
  have hret : p s ≤ p v - (T + 1) := by
    have := hp ⟨.inr (.inr true), trivial⟩; simp only [RArc.src, RArc.dst, RArc.cost] at this
    linarith
  have hretRev : 0 < q → p v ≤ p s + (T + 1) := fun h => by
    have := hp ⟨.inr (.inr false), show (0 : ℤ) < q from by exact_mod_cast h⟩
    simpa only [RArc.src, RArc.dst, RArc.cost] using this
  -- truncated, shifted potentials
  let A : V → ℤ := fun x => min ((T : ℤ) + 1) (max 0 (p x - p s))
  have hA0 : ∀ x, 0 ≤ A x := fun x => le_min (by omega) (le_max_left _ _)
  let a : V → ℕ := fun x => (A x).toNat
  have ha : ∀ x, (a x : ℤ) = A x := fun x => Int.toNat_of_nonneg (hA0 x)
  have hlabel : IsCutLabel s v T a := by
    refine ⟨?_, ?_, fun x => ?_⟩
    · have := ha s; simp only [A, sub_self, max_self] at this; omega
    · have := ha v; simp only [A] at this; omega
    · have := ha x; simp only [A] at this; omega
  have hcost : (labelCost G a : ℤ) ≤ ∑ d, P.pathFlow d * (p d.snd - p d.fst - 1) := by
    rw [labelCost_eq_sum_darts]
    refine sum_le_sum fun d _ => ?_
    have h1 := ha d.fst
    have h2 := ha d.snd
    simp only [A] at h1 h2
    rcases P.pathFlow_zero_or_one d with h | h
    · have := hfwd d h; rw [h]; omega
    · have := hbwd d h; rw [h]; omega
  have hval : ∑ d, P.pathFlow d * (p d.snd - p d.fst - 1) = P.value T := by
    have h1 := sum_flow_potential_of_isUnitFlow P.isUnitFlow_pathFlow p
    have h2 := P.sum_pathFlow
    simp only [mul_sub, mul_one, sum_sub_distrib] at h1 ⊢
    rw [h1, h2, DisjointPaths.value]
    have : (q : ℤ) * p v - q * p s = q * (T + 1) := by
      rcases Nat.eq_zero_or_pos q with hq | hq
      · subst hq; simp
      · have := hretRev hq
        have : p v - p s = T + 1 := by omega
        rw [← mul_sub, this]
    rw [this]
  calc (temporalMinCut G s v T : ℤ) ≤ labelCost G a := by
        exact_mod_cast temporalMinCut_le_labelCost G hlabel
    _ ≤ _ := hcost
    _ = _ := hval

end Optimal

/-! ### The maximum flow over time -/

section Main

variable {s v : V}

/-- An optimal family exists: values are bounded by `deg(s) (T + 1)`. -/
theorem exists_isOptimal (hv : v ≠ s) (T : ℕ) :
    ∃ (q : ℕ) (P : DisjointPaths G s v q), IsOptimal P T := by
  obtain ⟨x, ⟨q, P, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun x => ∃ (q : ℕ) (P : DisjointPaths G s v q), P.value T = x)
    ⟨G.degree s * (T + 1), by
      rintro _ ⟨q, P, rfl⟩
      have := P.card_le_degree hv.symm
      simp only [DisjointPaths.value]
      have : (q : ℤ) * (T + 1) ≤ G.degree s * (T + 1) := by gcongr
      omega⟩
    ⟨0, 0, DisjointPaths.empty G s v, by simp [DisjointPaths.value]⟩
  exact ⟨q, P, fun q' P' => hmax _ ⟨q', P', rfl⟩⟩

/-- **Discrete maximum flow over time.** `C_T(s,v)` is the maximum over families of
edge-disjoint `s`–`v` paths of `∑ᵢ (T + 1 - |Pᵢ|)`. -/
theorem exists_value_eq_temporalMinCut (hv : v ≠ s) (T : ℕ) :
    ∃ (q : ℕ) (P : DisjointPaths G s v q), P.value T = temporalMinCut G s v T := by
  obtain ⟨q, P, hopt⟩ := exists_isOptimal (G := G) hv T
  exact ⟨q, P, le_antisymm (value_le_temporalMinCut hv T P)
    (temporalMinCut_le_value_of_isOptimal P hopt)⟩

/-- **Maximum flow over time, short paths.** The maximum is attained by a family whose paths all have
length at most `T`. -/
theorem exists_value_eq_temporalMinCut_short (hv : v ≠ s) (T : ℕ) :
    ∃ (q : ℕ) (P : DisjointPaths G s v q), P.value T = temporalMinCut G s v T ∧
      ∀ i, (P.path i).length ≤ T := by
  classical
  have hex : ∃ q, ∃ P : DisjointPaths G s v q, P.value T = temporalMinCut G s v T :=
    exists_value_eq_temporalMinCut hv T
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  refine ⟨_, P, hP, fun i => ?_⟩
  by_contra hlong
  push Not at hlong
  -- removing a path of length `≥ T + 1` does not decrease the value, but decreases `q`
  obtain ⟨q', hq'⟩ : ∃ q', Nat.find hex = q' + 1 := by
    rcases h : Nat.find hex with _ | q'
    · rw [h] at i; exact i.elim0
    · exact ⟨q', rfl⟩
  revert P i
  rw [hq']
  intro P hP i hlong
  have h2 := value_le_temporalMinCut hv T (P.erase i)
  have h3 : (P.erase i).value T = temporalMinCut G s v T := by
    refine le_antisymm h2 ?_
    rw [← hP]
    simp only [DisjointPaths.value] at *
    rw [← (P.totalLength_erase i)]
    push_cast
    linarith [show ((P.path i).length : ℤ) ≥ T + 1 by exact_mod_cast hlong]
  exact absurd (Nat.find_min hex (by omega : q' < Nat.find hex)) (not_not.2 ⟨_, h3⟩)

end Main

end CodingGap
