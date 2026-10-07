import CodingGap.Model

/-!
# Edge-disjoint path families

Basic constructions and bounds for `DisjointPaths G s v q` (families of `q` pairwise
edge-disjoint `s`–`v` paths), `λ_v = maxDisjointPaths G s v` and `L_v(q) = minTotalLength G s v q`.
-/

namespace CodingGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {s v : V}

namespace DisjointPaths

/-- The empty family. -/
def empty (G : SimpleGraph V) (s v : V) : DisjointPaths G s v 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

@[simp] theorem totalLength_empty : (empty G s v).totalLength = 0 := by
  simp [totalLength]

/-- The first `q'` paths of a family. -/
def restrict {q q' : ℕ} (P : DisjointPaths G s v q) (h : q' ≤ q) : DisjointPaths G s v q' :=
  ⟨fun i => P.path (Fin.castLE h i), fun _ => P.isPath _,
    fun _ _ hij => P.disjoint fun h' => hij (Fin.castLE_injective h h')⟩

/-- Add a path, edge-disjoint from all others, in front of a family. -/
def cons {q : ℕ} (p : G.Walk s v) (hp : p.IsPath) (P : DisjointPaths G s v q)
    (h : ∀ i, p.edges.Disjoint (P.path i).edges) : DisjointPaths G s v (q + 1) where
  path := Fin.cons p P.path
  isPath i := Fin.cases hp (fun i => P.isPath i) i
  disjoint i j hij := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simpa using h j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using (h i).symm
      | succ j => simpa using P.disjoint fun h' => hij (by rw [h'])

theorem totalLength_cons {q : ℕ} (p : G.Walk s v) (hp : p.IsPath) (P : DisjointPaths G s v q)
    (h : ∀ i, p.edges.Disjoint (P.path i).edges) :
    (P.cons p hp h).totalLength = p.length + P.totalLength := by
  simp [totalLength, cons, Fin.sum_univ_succ]

/-- Remove the `i`-th path of a family. -/
def erase {q : ℕ} (P : DisjointPaths G s v (q + 1)) (i : Fin (q + 1)) : DisjointPaths G s v q :=
  ⟨fun j => P.path (i.succAbove j), fun _ => P.isPath _,
    fun _ _ hjk => P.disjoint fun h' => hjk (Fin.succAbove_right_injective h')⟩

theorem totalLength_erase {q : ℕ} (P : DisjointPaths G s v (q + 1)) (i : Fin (q + 1)) :
    (P.erase i).totalLength + (P.path i).length = P.totalLength := by
  simp only [totalLength, erase]
  rw [Fin.sum_univ_succAbove _ i]
  ring

theorem edges_nodup {q : ℕ} (P : DisjointPaths G s v q) (i : Fin q) : (P.path i).edges.Nodup :=
  (P.isPath i).isTrail.edges_nodup

theorem darts_nodup {q : ℕ} (P : DisjointPaths G s v q) (i : Fin q) : (P.path i).darts.Nodup :=
  List.Nodup.of_map _ (P.edges_nodup i)

/-- Darts of different paths are different (they even have different edges). -/
theorem edge_ne_of_mem_darts {q : ℕ} (P : DisjointPaths G s v q) {i j : Fin q} (hij : i ≠ j)
    {d d' : G.Dart} (hd : d ∈ (P.path i).darts) (hd' : d' ∈ (P.path j).darts) : d.edge ≠ d'.edge := by
  intro h
  have he : d.edge ∈ (P.path i).edges := List.mem_map_of_mem hd
  have he' : d.edge ∈ (P.path j).edges := h ▸ List.mem_map_of_mem hd'
  exact P.disjoint hij he he'

/-- A path from `s` to `v ≠ s` uses an edge `s(s, w)` at the source. -/
theorem exists_first_edge (hsv : s ≠ v) (p : G.Walk s v) :
    ∃ w, G.Adj s w ∧ s(s, w) ∈ p.edges := by
  cases p with
  | nil => exact absurd rfl hsv
  | cons h p => exact ⟨_, h, by simp⟩

/-- A family of edge-disjoint `s`–`v` paths has at most `deg(s)` members. -/
theorem card_le_degree [DecidableRel G.Adj] (hsv : s ≠ v) {q : ℕ} (P : DisjointPaths G s v q) :
    q ≤ G.degree s := by
  choose w hw hwe using fun i => exists_first_edge hsv (P.path i)
  have : (univ : Finset (Fin q)).card ≤ (G.neighborFinset s).card := by
    refine card_le_card_of_injOn w (fun i _ => by simpa using hw i) ?_
    intro i _ j _ hij
    by_contra hne
    exact P.disjoint hne (hwe i) (hij ▸ hwe j)
  simpa using this

end DisjointPaths

theorem nonempty_disjointPaths_zero : {q | Nonempty (DisjointPaths G s v q)}.Nonempty :=
  ⟨0, ⟨DisjointPaths.empty G s v⟩⟩

theorem bddAbove_disjointPaths [DecidableRel G.Adj] (hsv : s ≠ v) :
    BddAbove {q | Nonempty (DisjointPaths G s v q)} :=
  ⟨G.degree s, fun _ ⟨P⟩ => P.card_le_degree hsv⟩

theorem le_maxDisjointPaths [DecidableRel G.Adj] (hsv : s ≠ v) {q : ℕ}
    (P : DisjointPaths G s v q) : q ≤ maxDisjointPaths G s v :=
  le_csSup (bddAbove_disjointPaths hsv) ⟨P⟩

theorem maxDisjointPaths_le_degree [DecidableRel G.Adj] (hsv : s ≠ v) :
    maxDisjointPaths G s v ≤ G.degree s :=
  csSup_le nonempty_disjointPaths_zero fun _ ⟨P⟩ => P.card_le_degree hsv

/-- There are `q` edge-disjoint paths iff `q ≤ λ_v`. -/
theorem nonempty_disjointPaths_iff [DecidableRel G.Adj] (hsv : s ≠ v) {q : ℕ} :
    Nonempty (DisjointPaths G s v q) ↔ q ≤ maxDisjointPaths G s v := by
  refine ⟨fun ⟨P⟩ => le_maxDisjointPaths hsv P, fun hq => ?_⟩
  obtain ⟨P⟩ := Nat.sSup_mem (nonempty_disjointPaths_zero (G := G) (s := s) (v := v))
    (bddAbove_disjointPaths hsv)
  exact ⟨P.restrict hq⟩

/-- In a connected graph there is at least one `s`–`v` path. -/
theorem one_le_maxDisjointPaths [DecidableRel G.Adj] (hG : G.Connected) (hsv : s ≠ v) :
    1 ≤ maxDisjointPaths G s v := by
  obtain ⟨p⟩ := hG.preconnected s v
  exact le_maxDisjointPaths hsv
    ⟨fun _ => p.bypass, fun _ => p.bypass_isPath, fun i j hij => absurd (Subsingleton.elim i j) hij⟩

theorem minTotalLength_le {q : ℕ} (P : DisjointPaths G s v q) :
    minTotalLength G s v q ≤ P.totalLength :=
  Nat.sInf_le ⟨P, rfl⟩

/-- `L_v(q)` is attained whenever `q` edge-disjoint paths exist. -/
theorem exists_totalLength_eq_minTotalLength {q : ℕ} (h : Nonempty (DisjointPaths G s v q)) :
    ∃ P : DisjointPaths G s v q, P.totalLength = minTotalLength G s v q := by
  obtain ⟨P⟩ := h
  exact Nat.sInf_mem (s := {L | ∃ P : DisjointPaths G s v q, P.totalLength = L}) ⟨_, P, rfl⟩

@[simp] theorem minTotalLength_zero : minTotalLength G s v 0 = 0 :=
  Nat.eq_zero_of_le_zero ((minTotalLength_le (DisjointPaths.empty G s v)).trans (by simp))

end CodingGap
