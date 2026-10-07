import CodingGap.TemporalPaths

/-!
# A linear code attaining the temporal benchmark (Jaggi et al. for `G[T]`, `thm:coded`)

A *linear code* assigns to every communication arc `a = (u, w, t)` of `G[T]` a global encoding
vector `g a ∈ F^k`; the arc carries the symbol `⟨g a, X⟩`. The code is *valid* if `g a` lies in the
*knowledge* of the sender `u` at time `t`: the span of the unit vectors (if `u = s`) and of the
vectors of all arcs entering `u` before time `t`. (Memory is unrestricted, so no storage capacities
are needed.)

`exists_code` is the greedy construction of Jaggi et al. used in the proof of `thm:coded`: given a
temporal path system of size `k` for every receiver and `|F| ≥ n`, the arcs are processed in order
of time; each receiver maintains `k` linearly independent *frontier* vectors (one per path), and
the vector of the next arc is chosen in the sender's knowledge outside the at most `n - 1`
subspaces spanned by the other frontier vectors of the receivers whose paths use the arc. At the
end every receiver knows `k` independent vectors, hence all of `F^k`.
-/

namespace CodingGap

open Finset Submodule

/-! ### Two facts from linear algebra -/

section LinearAlgebra

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- Replacing one vector of an independent family by a vector outside the span of the others
keeps the family independent. -/
theorem linearIndependent_update_of_notMem_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → M} (hf : LinearIndependent F f) (j : ι) {x : M}
    (hx : x ∉ span F (f '' {j}ᶜ)) : LinearIndependent F (Function.update f j x) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc
  have hcj : c j = 0 := by
    by_contra hne
    apply hx
    have : x = -(c j)⁻¹ • ∑ i ∈ univ.erase j, c i • f i := by
      rw [← add_sum_erase _ _ (mem_univ j)] at hc
      simp only [Function.update_self] at hc
      have hrest : ∑ i ∈ univ.erase j, c i • Function.update f j x i =
          ∑ i ∈ univ.erase j, c i • f i :=
        sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
      rw [hrest] at hc
      have h1 : c j • x = -∑ i ∈ univ.erase j, c i • f i := eq_neg_of_add_eq_zero_left hc
      calc x = (c j)⁻¹ • (c j • x) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = -(c j)⁻¹ • ∑ i ∈ univ.erase j, c i • f i := by rw [h1, smul_neg, neg_smul]
    rw [this]
    refine smul_mem _ _ (sum_mem fun i hi => smul_mem _ _ (subset_span ?_))
    exact Set.mem_image_of_mem f (by simpa using ne_of_mem_erase hi)
  have hc' : ∑ i, c i • f i = 0 := by
    rw [← hc]
    refine sum_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · subst hij; simp [hcj]
    · rw [Function.update_of_ne hij]
  exact hf c hc'

/-- Over a finite field with more than `m` elements, a subspace `K` is not the union of `m`
subspaces which do not contain it. -/
theorem exists_mem_notMem_of_card_lt [Fintype F] [Fintype M] [DecidableEq M] {ι : Type*}
    (K : Submodule F M) (W : ι → Submodule F M) (S : Finset ι)
    (hW : ∀ i ∈ S, ∃ y ∈ K, y ∉ W i) (hS : S.card < Fintype.card F) :
    ∃ x ∈ K, ∀ i ∈ S, x ∉ W i := by
  classical
  let KF : Finset M := univ.filter (· ∈ K)
  let A : ι → Finset M := fun i => univ.filter fun x => x ∈ K ∧ x ∈ W i
  -- each `K ∩ W i` has at most `|K| / |F|` elements
  have hA : ∀ i ∈ S, Fintype.card F * (A i).card ≤ KF.card := by
    intro i hi
    obtain ⟨y, hyK, hyW⟩ := hW i hi
    have hmaps : Set.MapsTo (fun p : F × M => p.1 • y + p.2) ↑((univ : Finset F) ×ˢ A i) ↑KF := by
      intro p hp
      have hp2 := (mem_filter.1 (mem_product.1 (mem_coe.1 hp)).2).2.1
      exact mem_coe.2 (mem_filter.2 ⟨mem_univ _, add_mem (K.smul_mem _ hyK) hp2⟩)
    have hinj : Set.InjOn (fun p : F × M => p.1 • y + p.2) ↑((univ : Finset F) ×ˢ A i) := by
      intro p hp p' hp' h
      have hpW := (mem_filter.1 (mem_product.1 (mem_coe.1 hp)).2).2.2
      have hpW' := (mem_filter.1 (mem_product.1 (mem_coe.1 hp')).2).2.2
      simp only at h
      have hc : p.1 = p'.1 := by
        by_contra hne
        apply hyW
        have h2 : (p.1 - p'.1) • y = p'.2 - p.2 := by
          rw [sub_smul]; linear_combination (norm := module) h
        have hsub : p.1 - p'.1 ≠ 0 := sub_ne_zero.2 hne
        have : y = (p.1 - p'.1)⁻¹ • (p'.2 - p.2) := by
          rw [← h2, smul_smul, inv_mul_cancel₀ hsub, one_smul]
        rw [this]
        exact smul_mem _ _ (sub_mem hpW' hpW)
      have hw : p.2 = p'.2 := by rw [hc] at h; exact add_left_cancel h
      exact Prod.ext hc hw
    have := card_le_card_of_injOn _ hmaps hinj
    simpa [card_product] using this
  have hKF : 0 < KF.card := card_pos.2 ⟨0, by simp [KF]⟩
  have hunion : (S.biUnion A).card < KF.card := by
    have h1 : Fintype.card F * (S.biUnion A).card ≤ S.card * KF.card := by
      calc Fintype.card F * (S.biUnion A).card ≤ Fintype.card F * ∑ i ∈ S, (A i).card :=
            Nat.mul_le_mul_left _ card_biUnion_le
        _ = ∑ i ∈ S, Fintype.card F * (A i).card := mul_sum _ _ _
        _ ≤ ∑ _i ∈ S, KF.card := sum_le_sum hA
        _ = S.card * KF.card := by simp
    by_contra hge
    push Not at hge
    have : S.card * KF.card < Fintype.card F * KF.card := Nat.mul_lt_mul_of_pos_right hS hKF
    nlinarith
  obtain ⟨x, hxK, hxU⟩ := exists_mem_notMem_of_card_lt_card hunion
  refine ⟨x, by simpa [KF] using hxK, fun i hi hxW => hxU ?_⟩
  exact mem_biUnion.2 ⟨i, hi, by simp [A, hxW, show x ∈ K by simpa [KF] using hxK]⟩

end LinearAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {F : Type*} [Field F] {k : ℕ}

/-! ### Knowledge spaces -/

/-- A linear code: a global encoding vector for every (potential) arc `(u, w, t)`. -/
abbrev Code (V F : Type*) (k : ℕ) := V × V × ℕ → (Fin k → F)

/-- The generators of the knowledge of `u` at time `t`: the unit vectors if `u = s`, and the
vectors of the arcs into `u` sent before time `t`. -/
def gen (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (g : Code V F k) (u : V) (t : ℕ) :
    Fin k ⊕ (V × Fin t) → (Fin k → F)
  | .inl i => if u = s then Pi.single i 1 else 0
  | .inr p => if G.Adj p.1 u then g (p.1, u, p.2) else 0

/-- The knowledge of `u` at time `t`. -/
def knowledge (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (g : Code V F k) (u : V)
    (t : ℕ) : Submodule F (Fin k → F) :=
  span F (Set.range (gen G s g u t))

/-- The code is valid below the horizon `T`: every arc vector is known to its sender. -/
def IsValidCode (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (T : ℕ) (g : Code V F k) :
    Prop :=
  ∀ a : V × V × ℕ, a.2.2 < T → g a ∈ knowledge G s g a.1 a.2.2

variable {s : V}

theorem knowledge_congr {g g' : Code V F k} {u : V} {t : ℕ}
    (h : ∀ a : V × V × ℕ, a.2.2 < t → g a = g' a) : knowledge G s g u t = knowledge G s g' u t := by
  unfold knowledge
  congr 2
  funext p
  rcases p with i | ⟨u', t'⟩
  · rfl
  · simp only [gen]; rw [h (u', u, t') t'.isLt]

theorem single_mem_knowledge (g : Code V F k) (t : ℕ) (i : Fin k) :
    Pi.single i 1 ∈ knowledge G s g s t :=
  subset_span ⟨.inl i, by simp [gen]⟩

theorem mem_knowledge_of_adj (g : Code V F k) {u' u : V} (hadj : G.Adj u' u) {t' t : ℕ}
    (ht : t' < t) : g (u', u, t') ∈ knowledge G s g u t :=
  subset_span ⟨.inr (u', ⟨t', ht⟩), by simp [gen, hadj]⟩

theorem knowledge_source_eq_top (g : Code V F k) (t : ℕ) : knowledge G s g s t = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun F (Fin k)).span_eq, span_le]
  rintro _ ⟨i, rfl⟩
  simpa using single_mem_knowledge (G := G) g t i

/-! ### Processing arcs in order of time -/

section Rank

variable (V)

/-- A numbering of the arcs compatible with time. -/
noncomputable def arcRank (a : V × V × ℕ) : ℕ :=
  a.2.2 * Fintype.card (V × V) + (Fintype.equivFin (V × V) (a.1, a.2.1) : ℕ)

variable {V}

theorem arcRank_lt_of_time_lt {a b : V × V × ℕ} (h : a.2.2 < b.2.2) : arcRank V a < arcRank V b := by
  unfold arcRank
  have h1 := (Fintype.equivFin (V × V) (a.1, a.2.1)).isLt
  have : (a.2.2 + 1) * Fintype.card (V × V) ≤ b.2.2 * Fintype.card (V × V) :=
    Nat.mul_le_mul_right _ h
  nlinarith

theorem arcRank_injective : Function.Injective (arcRank V) := by
  intro a b h
  unfold arcRank at h
  have hN : 0 < Fintype.card (V × V) := Fintype.card_pos_iff.2 ⟨(a.1, a.1)⟩
  have h1 := (Fintype.equivFin (V × V) (a.1, a.2.1)).isLt
  have h2 := (Fintype.equivFin (V × V) (b.1, b.2.1)).isLt
  have key : ∀ t i : ℕ, i < Fintype.card (V × V) → (t * Fintype.card (V × V) + i) /
      Fintype.card (V × V) = t := fun t i hi => by
    rw [add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hi, zero_add]
  have ht : a.2.2 = b.2.2 := by
    rw [← key a.2.2 _ h1, ← key b.2.2 _ h2, h]
  rw [ht] at h
  have := (Fintype.equivFin (V × V)).injective (Fin.ext (Nat.add_left_cancel h))
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (Prod.ext this.2 ht)

theorem arcRank_lt_of_time_lt_bound {a : V × V × ℕ} {T : ℕ} (h : a.2.2 < T) :
    arcRank V a < T * Fintype.card (V × V) := by
  unfold arcRank
  have h1 := (Fintype.equivFin (V × V) (a.1, a.2.1)).isLt
  have : (a.2.2 + 1) * Fintype.card (V × V) ≤ T * Fintype.card (V × V) :=
    Nat.mul_le_mul_right _ h
  nlinarith

/-- The arc of rank `m` (for `V` nonempty). -/
noncomputable def arcOfRank (hV : 0 < Fintype.card (V × V)) (m : ℕ) : V × V × ℕ :=
  let p := (Fintype.equivFin (V × V)).symm ⟨m % Fintype.card (V × V), Nat.mod_lt _ hV⟩
  (p.1, p.2, m / Fintype.card (V × V))

theorem arcRank_arcOfRank (hV : 0 < Fintype.card (V × V)) (m : ℕ) :
    arcRank V (arcOfRank hV m) = m := by
  simp [arcRank, arcOfRank, Nat.div_add_mod']

end Rank

/-! ### Frontiers -/

namespace TemporalPath

variable {v : V} {T : ℕ} (π : TemporalPath G s v T)

theorem arcRank_strictMono {i i' : ℕ} (h : i < i') (hi' : i' < π.len) :
    arcRank V (π.arc i) < arcRank V (π.arc i') :=
  arcRank_lt_of_time_lt (π.time_strictMono h hi')

open Classical in
/-- The number of arcs of `π` among the first `m` processed arcs (these form a prefix of `π`). -/
noncomputable def processed (m : ℕ) : ℕ :=
  Nat.find (p := fun i => i = π.len ∨ m ≤ arcRank V (π.arc i)) ⟨π.len, Or.inl rfl⟩

theorem processed_le (m : ℕ) : π.processed m ≤ π.len := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

theorem lt_processed_iff {m i : ℕ} (hi : i < π.len) :
    i < π.processed m ↔ arcRank V (π.arc i) < m := by
  classical
  constructor
  · intro h
    have := Nat.find_min (p := fun i => i = π.len ∨ m ≤ arcRank V (π.arc i)) _ h
    push Not at this
    exact this.2
  · intro h
    by_contra hle
    push Not at hle
    have hspec := Nat.find_spec (p := fun i => i = π.len ∨ m ≤ arcRank V (π.arc i))
      ⟨π.len, Or.inl rfl⟩
    change π.processed m = π.len ∨ m ≤ arcRank V (π.arc (π.processed m)) at hspec
    rcases hspec with h' | h'
    · omega
    · rcases hle.lt_or_eq with hlt | heq
      · have := π.arcRank_strictMono hlt hi; omega
      · rw [heq] at h'; omega

theorem processed_eq {m c : ℕ} (hc : c ≤ π.len)
    (h : ∀ i < π.len, i < c ↔ arcRank V (π.arc i) < m) : π.processed m = c := by
  have h1 := π.processed_le m
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (π.lt_processed_iff (m := m) (by omega : π.processed m < π.len)).2
      ((h _ (by omega)).1 hlt)
    omega
  · have := (h _ (by omega : c < π.len)).2 ((π.lt_processed_iff (by omega)).1 hlt)
    omega

theorem processed_of_arc_eq {m i₀ : ℕ} (hi₀ : i₀ < π.len) (h : arcRank V (π.arc i₀) = m) :
    π.processed m = i₀ ∧ π.processed (m + 1) = i₀ + 1 := by
  constructor
  · refine π.processed_eq hi₀.le fun i hi => ?_
    rw [← h]
    constructor
    · exact fun h' => π.arcRank_strictMono h' hi₀
    · intro h'
      by_contra hge
      push Not at hge
      rcases hge.lt_or_eq with hlt | rfl
      · have := π.arcRank_strictMono hlt hi; omega
      · omega
  · refine π.processed_eq hi₀ fun i hi => ?_
    rw [← h]
    constructor
    · intro h'
      rcases (Nat.lt_succ_iff.1 h').lt_or_eq with hlt | rfl
      · have := π.arcRank_strictMono hlt hi₀; omega
      · omega
    · intro h'
      by_contra hge
      push Not at hge
      have := π.arcRank_strictMono (show i₀ < i by omega) hi
      omega

theorem processed_succ_of_ne {m : ℕ} (h : ∀ i < π.len, arcRank V (π.arc i) ≠ m) :
    π.processed (m + 1) = π.processed m :=
  π.processed_eq (π.processed_le m) fun i hi => by
    rw [π.lt_processed_iff hi]
    have := h i hi
    omega

theorem processed_all {M : ℕ} (hM : ∀ i < π.len, arcRank V (π.arc i) < M) :
    π.processed M = π.len :=
  π.processed_eq le_rfl fun i hi => ⟨fun _ => hM i hi, fun _ => hi⟩

/-- The frontier vector of path number `j` after processing the arcs of rank `< m`: the vector of
its last processed arc, or the `j`-th unit vector if none has been processed. -/
noncomputable def frontier (g : Code V F k) (m : ℕ) (j : Fin k) : Fin k → F :=
  if π.processed m = 0 then Pi.single j 1 else g (π.arc (π.processed m - 1))

end TemporalPath

/-! ### The greedy construction -/

section Greedy

variable {T : ℕ} (sys : ∀ v : {v // v ≠ s}, TemporalPathSystem G s v T k)

/-- The frontier vectors of receiver `v`. -/
noncomputable def frontiers (g : Code V F k) (m : ℕ) (v : {v // v ≠ s}) : Fin k → Fin k → F :=
  fun j => ((sys v).path j).frontier g m j

/-- The invariant after processing the arcs of rank `< m`. -/
def GreedyInv (m : ℕ) (g : Code V F k) : Prop :=
  (∀ a : V × V × ℕ, arcRank V a < m → g a ∈ knowledge G s g a.1 a.2.2) ∧
    ∀ v, LinearIndependent F (frontiers sys g m v)

theorem greedyInv_zero : GreedyInv sys 0 (fun _ => 0 : Code V F k) := by
  refine ⟨fun a h => absurd h (Nat.not_lt_zero _), fun v => ?_⟩
  have : frontiers sys (fun _ => 0 : Code V F k) 0 v = fun j => Pi.single j 1 := by
    funext j
    have : ((sys v).path j).processed 0 = 0 :=
      Nat.eq_zero_of_le_zero (by
        by_contra h
        push Not at h
        have := (((sys v).path j).lt_processed_iff (m := 0) (i := 0)
          ((sys v).path j).len_pos).1 h
        omega)
    simp [frontiers, TemporalPath.frontier, this]
  rw [this]
  have := (Pi.basisFun F (Fin k)).linearIndependent
  rwa [show ⇑(Pi.basisFun F (Fin k)) = fun j => Pi.single j 1 from
    funext fun j => Pi.basisFun_apply F (Fin k) j] at this

variable [Fintype F] [DecidableEq F]

/-- One greedy step. -/
theorem greedyInv_succ (hF : Fintype.card V ≤ Fintype.card F) {m : ℕ} {g : Code V F k}
    (hinv : GreedyInv sys m g) : ∃ g' : Code V F k, GreedyInv sys (m + 1) g' := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- with no packets every vector is zero and every family is empty
    subst hk
    refine ⟨g, fun b _ => ?_, fun v => linearIndependent_empty_type⟩
    rw [Subsingleton.elim (g b) 0]; exact zero_mem _
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hV : 0 < Fintype.card (V × V) := Fintype.card_pos_iff.2 ⟨(s, s)⟩
  obtain ⟨a, ha⟩ : ∃ a, arcRank V a = m := ⟨_, arcRank_arcOfRank hV m⟩
  -- receivers whose paths use the arc `a`
  let Uses : {v // v ≠ s} → Prop := fun v => ∃ j i, i < ((sys v).path j).len ∧
    ((sys v).path j).arc i = a
  let C : Finset {v // v ≠ s} := univ.filter Uses
  choose! jv iv hiv hav using fun v (hv : Uses v) => hv
  -- the frontier vector on the path through `a` is known to the sender of `a`
  have hy : ∀ v ∈ C, frontiers sys g m v (jv v) ∈ knowledge G s g a.1 a.2.2 := by
    intro v hv
    have hv' : Uses v := (mem_filter.1 hv).2
    have hi := hiv v hv'
    have harc := hav v hv'
    obtain ⟨hp, -⟩ := ((sys v).path (jv v)).processed_of_arc_eq hi (harc ▸ ha)
    show ((sys v).path (jv v)).frontier g m (jv v) ∈ knowledge G s g a.1 a.2.2
    unfold TemporalPath.frontier
    rw [hp]
    split_ifs with h0
    · rw [← harc, h0, ((sys v).path (jv v)).first]
      exact single_mem_knowledge g _ _
    · have hc := ((sys v).path (jv v)).chain (iv v - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hc
      rw [← harc, ← hc.1]
      exact mem_knowledge_of_adj g (((sys v).path (jv v)).adj _ (by omega)) hc.2
  have hyW : ∀ v ∈ C, frontiers sys g m v (jv v) ∉
      span F (frontiers sys g m v '' {jv v}ᶜ) :=
    fun v _ => (hinv.2 v).notMem_span_image (by simp)
  have hCcard : C.card < Fintype.card F := by
    calc C.card ≤ Fintype.card {v // v ≠ s} := card_le_univ _
      _ = Fintype.card V - 1 := by simp [Fintype.card_subtype_compl]
      _ < Fintype.card F := by have := Fintype.card_pos_iff.2 ⟨s⟩; omega
  obtain ⟨x, hxK, hxW⟩ := exists_mem_notMem_of_card_lt (knowledge G s g a.1 a.2.2)
    (fun v => span F (frontiers sys g m v '' {jv v}ᶜ)) C
    (fun v hv => ⟨_, hy v hv, hyW v hv⟩) hCcard
  refine ⟨Function.update g a x, ⟨fun b hb => ?_, fun v => ?_⟩⟩
  · -- validity
    have hcongr : knowledge G s (Function.update g a x) b.1 b.2.2 = knowledge G s g b.1 b.2.2 := by
      refine knowledge_congr fun c hc => ?_
      rw [Function.update_of_ne]
      rintro rfl
      have := arcRank_lt_of_time_lt (V := V) hc
      rcases Nat.lt_succ_iff.1 hb |>.lt_or_eq with h | h <;> omega
    rw [hcongr]
    by_cases hba : b = a
    · subst hba; rw [Function.update_self]; exact hxK
    · rw [Function.update_of_ne hba]
      refine hinv.1 b ?_
      rcases Nat.lt_succ_iff.1 hb |>.lt_or_eq with h | h
      · exact h
      · exact absurd (arcRank_injective (h.trans ha.symm)) hba
  · -- independence of the new frontiers
    have hnot : ∀ j, (∀ i < ((sys v).path j).len, ((sys v).path j).arc i ≠ a) →
        frontiers sys (Function.update g a x) (m + 1) v j = frontiers sys g m v j := by
      intro j hj
      have hne : ∀ i < ((sys v).path j).len, arcRank V (((sys v).path j).arc i) ≠ m :=
        fun i hi h => hj i hi (arcRank_injective (h.trans ha.symm))
      show ((sys v).path j).frontier (Function.update g a x) (m + 1) j =
        ((sys v).path j).frontier g m j
      unfold TemporalPath.frontier
      rw [((sys v).path j).processed_succ_of_ne hne]
      split_ifs with h0
      · rfl
      · rw [Function.update_of_ne (hj _ (by have := ((sys v).path j).processed_le m; omega))]
    by_cases hv : Uses v
    · have hvC : v ∈ C := mem_filter.2 ⟨mem_univ _, hv⟩
      have hupd : frontiers sys (Function.update g a x) (m + 1) v =
          Function.update (frontiers sys g m v) (jv v) x := by
        funext j
        by_cases hj : j = jv v
        · rw [hj, Function.update_self]
          obtain ⟨-, hp⟩ := ((sys v).path (jv v)).processed_of_arc_eq (hiv v hv)
            ((hav v hv) ▸ ha)
          show ((sys v).path (jv v)).frontier (Function.update g a x) (m + 1) (jv v) = x
          unfold TemporalPath.frontier
          rw [hp, if_neg (by omega), Nat.add_sub_cancel, hav v hv, Function.update_self]
        · rw [Function.update_of_ne hj]
          refine hnot j fun i hi h => hj ?_
          exact ((sys v).disjoint j (jv v) i (iv v) hi (hiv v hv) (h.trans (hav v hv).symm)).1
      rw [hupd]
      exact linearIndependent_update_of_notMem_span (hinv.2 v) _ (hxW v hvC)
    · have : frontiers sys (Function.update g a x) (m + 1) v = frontiers sys g m v := by
        funext j
        exact hnot j fun i hi h => hv ⟨j, i, hi, h⟩
      rw [this]
      exact hinv.2 v

include sys in
/-- **Jaggi et al. for the time-expanded network.** If `|F| ≥ n` and every receiver has a temporal
path system of size `k` within horizon `T`, there is a valid linear code after which every vertex
knows all of `F^k` at time `T`. -/
theorem exists_code (hF : Fintype.card V ≤ Fintype.card F) :
    ∃ g : Code V F k, IsValidCode G s T g ∧ ∀ v, knowledge G s g v T = ⊤ := by
  have hall : ∀ m, ∃ g : Code V F k, GreedyInv sys m g := by
    intro m
    induction m with
    | zero => exact ⟨_, greedyInv_zero sys⟩
    | succ m ih => obtain ⟨g, hg⟩ := ih; exact greedyInv_succ sys hF hg
  obtain ⟨g, hvalid, hind⟩ := hall (T * Fintype.card (V × V))
  refine ⟨g, fun a ha => hvalid a (arcRank_lt_of_time_lt_bound ha), fun v => ?_⟩
  by_cases hvs : v = s
  · subst hvs; exact knowledge_source_eq_top g T
  -- the final frontier vectors are vectors of arcs into `v`
  have hmem : ∀ j, frontiers sys g (T * Fintype.card (V × V)) ⟨v, hvs⟩ j ∈ knowledge G s g v T := by
    intro j
    set π := (sys ⟨v, hvs⟩).path j
    have hp := π.processed_all (M := T * Fintype.card (V × V))
      fun i hi => arcRank_lt_of_time_lt_bound (π.time_lt i hi)
    simp only [frontiers, TemporalPath.frontier]
    rw [hp, if_neg (by have := π.len_pos; omega)]
    have hlast := π.last
    have hadj := π.adj (π.len - 1) (by have := π.len_pos; omega)
    have htime := π.time_lt (π.len - 1) (by have := π.len_pos; omega)
    rw [hlast] at hadj
    have : π.arc (π.len - 1) = ((π.arc (π.len - 1)).1, v, (π.arc (π.len - 1)).2.2) :=
      Prod.ext rfl (Prod.ext hlast rfl)
    rw [this]
    exact mem_knowledge_of_adj g hadj htime
  rw [eq_top_iff]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    intro x _
    have : x = 0 := Subsingleton.elim _ _
    rw [this]; exact zero_mem _
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hspan := (hind ⟨v, hvs⟩).span_eq_top_of_card_eq_finrank (by simp)
  rw [← hspan, span_le]
  rintro _ ⟨j, rfl⟩
  exact hmem j

end Greedy

end CodingGap
