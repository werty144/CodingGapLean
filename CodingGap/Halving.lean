import CodingGap.Doubling
import CodingGap.Cited

/-!
# The root-preserving halving step (`lem:halving`)

Suppose every vertex has `r ≥ 1` edge-disjoint source paths of length at most `h`, and let
`S ∋ s` with `|S| ≥ 2`. Using the terminal path system of Chuzhoy–Parter–Tan (`lem:cpt`) in `2G`
with terminals `S \ {s}`, we find `A ⊊ S` with `s ∈ A`, `|A| ≤ ⌈|S|/2⌉`, and for every
`v ∈ S \ A` exactly `q = ⌈r/2⌉` paths of `G` from vertices of `A` to `v`, of length at most `4h`,
such that every edge of `G` lies on at most four of all these paths.

The terminal paths form an auxiliary multigraph on `S` in which every non-source vertex has
degree at least `r`. A maximum cut of it is locally optimal, so every vertex has at least half of
its incident paths crossing. The side of `s` is kept if it is not larger; otherwise the smaller
side together with `s`.
-/

namespace CodingGap

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exists_mem_ne_of_two_le {S : Finset V} (hS : 2 ≤ S.card) (a : V) : ∃ b ∈ S, b ≠ a := by
  obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.1 hS
  by_cases hxa : x = a
  · exact ⟨y, hy, fun h => hxy (hxa.trans h.symm)⟩
  · exact ⟨x, hx, hxa⟩

namespace DoubledTerminalPaths

variable {s : V} {U : Finset V} {r D : ℕ} (F : DoubledTerminalPaths G s U r D)

/-- Every edge of `G` lies on at most four of the paths (two per parallel copy). -/
theorem physical_congestion (e : Sym2 V) :
    (univ.filter fun i => e ∈ (F.path i).edges).card ≤ 4 := by
  have hsub : (univ.filter fun i => e ∈ (F.path i).edges) ⊆
      (univ.filter fun i => e ∈ (F.path i).edges ∧ F.copy i e = 0) ∪
        (univ.filter fun i => e ∈ (F.path i).edges ∧ F.copy i e = 1) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
    rcases Fin.exists_fin_two.1 ⟨F.copy i e, rfl⟩ with h | h
    · exact Or.inl ⟨hi, h⟩
    · exact Or.inr ⟨hi, h⟩
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (by have := F.congestion e 0; have := F.congestion e 1; omega))

/-- The endpoint of path `i` other than `v`. -/
def other (i : Fin F.N) (v : V) : V := if F.src i = v then F.dst i else F.src i

/-- Path `i` oriented towards its endpoint `v`. -/
def orient (i : Fin F.N) (v : V) (hi : F.src i = v ∨ F.dst i = v) : G.Walk (F.other i v) v :=
  if h : F.src i = v then (F.path i).reverse.copy (by simp [other, h]) h
  else (F.path i).copy (by simp [other, h]) (hi.resolve_left h)

theorem orient_spec (i : Fin F.N) (v : V) (hi : F.src i = v ∨ F.dst i = v) :
    (F.orient i v hi).IsPath ∧ (F.orient i v hi).length ≤ D ∧
      ∀ e, e ∈ (F.orient i v hi).edges ↔ e ∈ (F.path i).edges := by
  unfold orient
  split_ifs
  · refine ⟨(SimpleGraph.Walk.isPath_copy _ _ _).2 (F.isPath i).reverse, ?_, fun e => ?_⟩
    · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse]; exact F.length_le i
    · rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse, List.mem_reverse]
  · refine ⟨(SimpleGraph.Walk.isPath_copy _ _ _).2 (F.isPath i), ?_, fun e => ?_⟩
    · rw [SimpleGraph.Walk.length_copy]; exact F.length_le i
    · rw [SimpleGraph.Walk.edges_copy]

/-- Path `i` crosses the cut `X`. -/
def Crossing (X : Finset V) (i : Fin F.N) : Prop := ¬ (F.src i ∈ X ↔ F.dst i ∈ X)

instance (X : Finset V) : DecidablePred (F.Crossing X) := fun i =>
  inferInstanceAs (Decidable (¬ (F.src i ∈ X ↔ F.dst i ∈ X)))

/-- The size of the cut `X` in the auxiliary multigraph. -/
def cross (X : Finset V) : ℕ := (univ.filter (F.Crossing X)).card

/-- A maximum cut is locally optimal: at every vertex at least half of the incident paths cross. -/
theorem local_opt {S X : Finset V} (hXS : X ⊆ S) (hmax : ∀ X' ⊆ S, F.cross X' ≤ F.cross X)
    {v : V} (hv : v ∈ S) :
    (univ.filter fun i => F.src i = v ∨ F.dst i = v).card ≤
      2 * ((univ.filter fun i => F.src i = v ∨ F.dst i = v).filter (F.Crossing X)).card := by
  set X' := if v ∈ X then X.erase v else insert v X
  have hX'S : X' ⊆ S := by
    simp only [X']; split_ifs
    · exact (erase_subset _ _).trans hXS
    · exact insert_subset hv hXS
  -- flipping `v` toggles exactly the incident paths
  have htoggle : ∀ i, F.Crossing X' i ↔
      if F.src i = v ∨ F.dst i = v then ¬ F.Crossing X i else F.Crossing X i := by
    intro i
    have hne := F.src_ne_dst i
    have hmem : ∀ x, x ≠ v → (x ∈ X' ↔ x ∈ X) := by
      intro x hx; simp only [X']; split_ifs <;> simp [hx]
    have hv' : v ∈ X' ↔ v ∉ X := by simp only [X']; split_ifs with h <;> simp [h]
    unfold Crossing
    split_ifs with hi
    · rcases hi with h | h
      · subst h; rw [hv', hmem _ (Ne.symm hne)]; tauto
      · subst h; rw [hv', hmem _ hne]; tauto
    · push Not at hi; rw [hmem _ hi.1, hmem _ hi.2]
  have h1 := hmax X' hX'S
  set I : Fin F.N → Prop := fun i => F.src i = v ∨ F.dst i = v with hI
  have hX : F.cross X = ∑ i ∈ univ.filter I, (if F.Crossing X i then 1 else 0) +
      ∑ i ∈ univ.filter (fun i => ¬ I i), (if F.Crossing X i then 1 else 0) := by
    unfold cross; rw [card_filter, sum_filter_add_sum_filter_not]
  have hX' : F.cross X' = ∑ i ∈ univ.filter I, (if F.Crossing X i then 0 else 1) +
      ∑ i ∈ univ.filter (fun i => ¬ I i), (if F.Crossing X i then 1 else 0) := by
    unfold cross
    rw [card_filter, ← sum_filter_add_sum_filter_not univ I]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      rw [if_congr ((htoggle i).trans (by rw [if_pos (mem_filter.1 hi).2])) rfl rfl]
      split_ifs <;> rfl
    · refine sum_congr rfl fun i hi => ?_
      rw [if_congr ((htoggle i).trans (by rw [if_neg (mem_filter.1 hi).2])) rfl rfl]
  have htot : ∑ i ∈ univ.filter I, (if F.Crossing X i then 1 else 0) +
      ∑ i ∈ univ.filter I, (if F.Crossing X i then 0 else 1) = (univ.filter I).card := by
    rw [← sum_add_distrib, card_eq_sum_ones]
    exact sum_congr rfl fun i _ => by split_ifs <;> rfl
  have hc : ((univ.filter I).filter (F.Crossing X)).card =
      ∑ i ∈ univ.filter I, (if F.Crossing X i then 1 else 0) := card_filter _ _
  change (univ.filter I).card ≤ 2 * ((univ.filter I).filter (F.Crossing X)).card
  rw [hc]
  omega

/-- Selecting `q` paths into every `v ∈ B` whose other endpoint lies in `A` gives a level of the
hierarchy (a path has only one endpoint in `B`, so it is selected at most once). -/
theorem levelPaths {A B : Finset V} {q : ℕ} (hAB : Disjoint A B)
    (hB : ∀ v ∈ B, q ≤ ((univ.filter fun i => F.src i = v ∨ F.dst i = v).filter
      fun i => F.other i v ∈ A).card) :
    Nonempty (LevelPaths G A B q D 4) := by
  classical
  have hsel : ∀ v ∈ B, ∃ f : Fin q → Fin F.N, Function.Injective f ∧
      ∀ j, (F.src (f j) = v ∨ F.dst (f j) = v) ∧ F.other (f j) v ∈ A := by
    intro v hv
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (hB v hv)
    let e : T ≃ Fin q := T.equivFin.trans (finCongr hTc)
    refine ⟨fun j => (e.symm j).1, fun j j' h => e.symm.injective (Subtype.ext h), fun j => ?_⟩
    have := hT (e.symm j).2
    simp only [mem_filter, mem_univ, true_and] at this
    exact this
  let sel : ∀ v, v ∈ B → Fin q → Fin F.N := fun v hv => (hsel v hv).choose
  have hsel_inj : ∀ v (hv : v ∈ B), Function.Injective (sel v hv) :=
    fun v hv => (hsel v hv).choose_spec.1
  have hsel_spec : ∀ v (hv : v ∈ B) j, (F.src (sel v hv j) = v ∨ F.dst (sel v hv j) = v) ∧
      F.other (sel v hv j) v ∈ A := fun v hv => (hsel v hv).choose_spec.2
  let st : V → Fin q → V := fun v j => if hv : v ∈ B then F.other (sel v hv j) v else v
  let pth : ∀ v j, G.Walk (st v j) v := fun v j =>
    if hv : v ∈ B then (F.orient (sel v hv j) v (hsel_spec v hv j).1).copy (by simp [st, hv]) rfl
    else SimpleGraph.Walk.nil.copy (by simp [st, hv]) rfl
  have hpth : ∀ v (hv : v ∈ B) j, (pth v j).IsPath ∧ (pth v j).length ≤ D ∧
      ∀ e, e ∈ (pth v j).edges ↔ e ∈ (F.path (sel v hv j)).edges := by
    intro v hv j
    have h := F.orient_spec (sel v hv j) v (hsel_spec v hv j).1
    simp only [pth, dif_pos hv, SimpleGraph.Walk.isPath_copy, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.edges_copy]
    exact h
  refine ⟨⟨st, fun v hv j => by simp only [st, dif_pos hv]; exact (hsel_spec v hv j).2, pth,
    fun v hv j => (hpth v hv j).1, fun v hv j => (hpth v hv j).2.1, fun e => ?_⟩⟩
  -- congestion: the selection is injective into the paths through `e`
  set T := (B ×ˢ (univ : Finset (Fin q))).filter fun p => e ∈ (pth p.1 p.2).edges
  rcases T.eq_empty_or_nonempty with hT | ⟨p₀, hp₀⟩
  · rw [hT]; simp
  have hp₀B : p₀.1 ∈ B := (mem_product.1 (mem_filter.1 hp₀).1).1
  let i₀ := sel p₀.1 hp₀B p₀.2
  let f : V × Fin q → Fin F.N := fun p => if hp : p.1 ∈ B then sel p.1 hp p.2 else i₀
  refine le_trans (card_le_card_of_injOn f (fun p hp => ?_) (fun p hp p' hp' h => ?_))
    (F.physical_congestion e)
  · have hp := mem_coe.1 hp
    have hpB : p.1 ∈ B := (mem_product.1 (mem_filter.1 hp).1).1
    have := (hpth p.1 hpB p.2).2.2 e
    simp only [f, dif_pos hpB, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact this.1 (mem_filter.1 hp).2
  · have hpB : p.1 ∈ B := (mem_product.1 (mem_filter.1 (mem_coe.1 hp)).1).1
    have hpB' : p'.1 ∈ B := (mem_product.1 (mem_filter.1 (mem_coe.1 hp')).1).1
    simp only [f, dif_pos hpB, dif_pos hpB'] at h
    have hv : p.1 = p'.1 := by
      by_contra hne
      have h1 := hsel_spec p.1 hpB p.2
      have h2 := hsel_spec p'.1 hpB' p'.2
      rw [h] at h1
      -- `p'.1` is the other endpoint of the path, which lies in `A`
      have hne' := F.src_ne_dst (sel p'.1 hpB' p'.2)
      have : F.other (sel p'.1 hpB' p'.2) p.1 = p'.1 := by
        unfold other
        rcases h1.1 with h1a | h1a <;> rcases h2.1 with h2a | h2a
        · exact absurd (h1a.symm.trans h2a) hne
        · rw [if_pos h1a, h2a]
        · rw [if_neg (fun h' => hne' (h'.trans h1a.symm)), h2a]
        · exact absurd (h1a.symm.trans h2a) hne
      exact Finset.disjoint_left.1 hAB (this ▸ h1.2) hpB'
    obtain ⟨v, j⟩ := p
    obtain ⟨v', j'⟩ := p'
    simp only at hv
    subst hv
    exact Prod.ext rfl (hsel_inj v hpB h)

end DoubledTerminalPaths

/-- **`lem:halving` (root-preserving halving step).** -/
theorem exists_halving (hcpt : CPTTerminalPaths.{u}) {s : V} {r h : ℕ} (hr : 1 ≤ r)
    (hP : ∀ v, v ≠ s → ∃ P : DisjointPaths G s v r, ∀ i, (P.path i).length ≤ h)
    {S : Finset V} (hs : s ∈ S) (hS : 2 ≤ S.card) :
    ∃ A : Finset V, A ⊆ S ∧ A ≠ S ∧ s ∈ A ∧ 2 * A.card ≤ S.card + 1 ∧
      Nonempty (LevelPaths G A (S \ A) ((r + 1) / 2) (4 * h) 4) := by
  classical
  obtain ⟨F⟩ := hcpt V G r (2 * h) (S.erase s) s (by simp) (doubledConnected_of_rooted hP)
  rw [show 2 * (2 * h) = 4 * h by ring] at F
  have hsrcS : ∀ i, F.src i ∈ S := fun i =>
    (F.src_mem i).elim (fun h => by rw [h]; exact hs) mem_of_mem_erase
  have hdstS : ∀ i, F.dst i ∈ S := fun i =>
    (F.dst_mem i).elim (fun h => by rw [h]; exact hs) mem_of_mem_erase
  obtain ⟨X, hXS, hXmax⟩ := S.powerset.exists_max_image F.cross ⟨∅, empty_mem_powerset S⟩
  rw [mem_powerset] at hXS
  have hmax : ∀ X' ⊆ S, F.cross X' ≤ F.cross X := fun X' h => hXmax X' (mem_powerset.2 h)
  -- every non-source vertex has at least `⌈r/2⌉` crossing paths
  have hcr : ∀ v ∈ S, v ≠ s → (r + 1) / 2 ≤
      ((univ.filter fun i => F.src i = v ∨ F.dst i = v).filter (F.Crossing X)).card := by
    intro v hv hvs
    have := F.local_opt hXS hmax hv
    have := F.endpoint v (mem_erase.2 ⟨hvs, hv⟩)
    omega
  -- the other endpoint of a crossing path lies on the other side
  have hopp : ∀ v i, (F.src i = v ∨ F.dst i = v) → F.Crossing X i →
      F.other i v ∈ S ∧ (F.other i v ∈ X ↔ v ∉ X) := by
    intro v i hi hc
    unfold DoubledTerminalPaths.Crossing at hc
    unfold DoubledTerminalPaths.other
    split_ifs with h
    · exact ⟨hdstS i, by subst h; tauto⟩
    · rw [hi.resolve_left h] at hc; exact ⟨hsrcS i, by tauto⟩
  let Z := S.filter fun x => (x ∈ X ↔ s ∈ X)
  let W := S.filter fun x => ¬ (x ∈ X ↔ s ∈ X)
  have hZW : Z.card + W.card = S.card := card_filter_add_card_filter_not _
  have hsZ : s ∈ Z := mem_filter.2 ⟨hs, Iff.rfl⟩
  -- the side not containing `s` is nonempty
  obtain ⟨w, hwW⟩ : W.Nonempty := by
    obtain ⟨u, huS, hus⟩ := exists_mem_ne_of_two_le hS s
    obtain ⟨i, hi⟩ := card_pos.1 (lt_of_lt_of_le (by omega) (hcr u huS hus))
    obtain ⟨hi1, hi2⟩ := mem_filter.1 hi
    have hiu := (mem_filter.1 hi1).2
    obtain ⟨hoS, hoX⟩ := hopp u i hiu hi2
    by_cases hu : u ∈ X ↔ s ∈ X
    · exact ⟨_, mem_filter.2 ⟨hoS, by tauto⟩⟩
    · exact ⟨u, mem_filter.2 ⟨huS, hu⟩⟩
  have hsel : ∀ A : Finset V, (∀ v ∈ S \ A, v ≠ s ∧ ∀ x ∈ S, (x ∈ X ↔ v ∉ X) → x ∈ A) →
      ∀ v ∈ S \ A, (r + 1) / 2 ≤ ((univ.filter fun i => F.src i = v ∨ F.dst i = v).filter
        fun i => F.other i v ∈ A).card := by
    intro A hA v hv
    refine (hcr v (mem_sdiff.1 hv).1 (hA v hv).1).trans (card_le_card fun i hi => ?_)
    obtain ⟨hi1, hi2⟩ := mem_filter.1 hi
    obtain ⟨hoS, hoX⟩ := hopp v i (mem_filter.1 hi1).2 hi2
    exact mem_filter.2 ⟨hi1, (hA v hv).2 _ hoS hoX⟩
  by_cases hcase : Z.card ≤ W.card
  · refine ⟨Z, filter_subset _ _, fun h => ?_, hsZ, by omega,
      F.levelPaths disjoint_sdiff (hsel Z fun v hv => ?_)⟩
    · have : w ∈ Z := h ▸ (mem_filter.1 hwW).1
      exact (mem_filter.1 hwW).2 (mem_filter.1 this).2
    · have hvS := (mem_sdiff.1 hv).1
      have hvW : ¬ (v ∈ X ↔ s ∈ X) := fun h' => (mem_sdiff.1 hv).2 (mem_filter.2 ⟨hvS, h'⟩)
      exact ⟨fun h' => hvW (h' ▸ Iff.rfl), fun x hx hxX => mem_filter.2 ⟨hx, by tauto⟩⟩
  · push Not at hcase
    obtain ⟨z, hzZ, hzs⟩ := exists_mem_ne_of_two_le (show 2 ≤ Z.card by
      have := card_pos.2 ⟨w, hwW⟩; omega) s
    refine ⟨insert s W, insert_subset hs (filter_subset _ _), fun h => ?_, mem_insert_self _ _,
      ?_, F.levelPaths disjoint_sdiff (hsel _ fun v hv => ?_)⟩
    · have : z ∈ insert s W := h ▸ (mem_filter.1 hzZ).1
      rcases mem_insert.1 this with h' | h'
      · exact hzs h'
      · exact (mem_filter.1 h').2 (mem_filter.1 hzZ).2
    · have := card_insert_le s W; omega
    · have hvS := (mem_sdiff.1 hv).1
      have hvA := (mem_sdiff.1 hv).2
      have hvs : v ≠ s := fun h' => hvA (h' ▸ mem_insert_self _ _)
      have hvZ : (v ∈ X ↔ s ∈ X) := by
        by_contra h'; exact hvA (mem_insert_of_mem (mem_filter.2 ⟨hvS, h'⟩))
      exact ⟨hvs, fun x hx hxX => mem_insert_of_mem (mem_filter.2 ⟨hx, by tauto⟩)⟩

end CodingGap
