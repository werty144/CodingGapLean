import CodingGap.CodingProtocol

/-!
# Changing the alphabet; `B`-bit packets

Only the number of symbols of the alphabet matters: a protocol can be relabelled along a
bijection of alphabets (`Protocol.map`), so `CODE` is invariant under such bijections
(`codedTime_congr`). The paper's alphabet `Bits B` of `B`-bit strings has `2 ^ B` elements, as has
the finite field `GaloisField 2 B`; hence the results proved over finite fields transfer to `B`-bit
packets (`codedTime_bits_eq_tau`).
-/

namespace CodingGap

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} {A A' : Type}

namespace Protocol

/-- Relabel the alphabet of a protocol along a bijection `e : A ≃ A'`. -/
def map (e : A ≃ A') (P : Protocol V A k) : Protocol V A' k where
  State := P.State
  initSource X := P.initSource (e.symm ∘ X)
  init := P.init
  send u w t st := e (P.send u w t st)
  step w t st m := P.step w t st fun u => (m u).map e.symm
  output v st := e ∘ P.output v st

theorem run_map (e : A ≃ A') (P : Protocol V A k) (s : V) (X : Fin k → A') :
    ∀ t u, (P.map e).run G s X t u = P.run G s (e.symm ∘ X) t u := by
  intro t
  induction t with
  | zero => intro u; rfl
  | succ t ih =>
    intro w
    change P.step w t ((P.map e).run G s X t w) (fun u => Option.map e.symm
      (if G.Adj u w then some (e (P.send u w t ((P.map e).run G s X t u))) else none)) = _
    simp only [ih]
    congr 1
    funext u
    split_ifs <;> simp

theorem broadcasts_map (e : A ≃ A') (P : Protocol V A k) (s : V) (X : Fin k → A') (T : ℕ) :
    (P.map e).Broadcasts G s X T ↔ P.Broadcasts G s (e.symm ∘ X) T := by
  refine forall_congr' fun v => ?_
  change e ∘ P.output v ((P.map e).run G s X T v) = X ↔ _
  rw [run_map, Recovers]
  constructor
  · intro h; funext i; simpa using congrArg e.symm (congrFun h i)
  · intro h; rw [h]; funext i; simp

end Protocol

/-- `CODE` only depends on the alphabet up to bijection. -/
theorem codedTime_congr (e : A ≃ A') (s : V) (k : ℕ) :
    codedTime G s A k = codedTime G s A' k := by
  unfold codedTime
  congr 1
  ext T
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.map e, fun X => (P.broadcasts_map e s X T).2 (hP _)⟩
  · rintro ⟨P, hP⟩
    refine ⟨P.map e.symm, fun X => (P.broadcasts_map e.symm s X T).2 ?_⟩
    simpa using hP (e.symm.symm ∘ X)

/-- `B`-bit strings are in bijection with the field with `2 ^ B` elements. -/
noncomputable def bitsEquivGaloisField {B : ℕ} (hB : B ≠ 0) : Bits B ≃ GaloisField 2 B := by
  have : Fintype (GaloisField 2 B) := Fintype.ofFinite _
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_eq_nat_card (α := GaloisField 2 B), GaloisField.card 2 B hB]
  simp [Bits]

/-- **Theorem `thm:coded` for `B`-bit packets.** If `2 ^ B ≥ n`, then `CODE(G,s,k,B) = τ(G,s,k)`. -/
theorem codedTime_bits_eq_tau {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.Connected) (s : V) {k : ℕ} (hk : 1 ≤ k) {B : ℕ} (hB : 1 ≤ B)
    (hn : Fintype.card V ≤ 2 ^ B) : codedTime G s (Bits B) k = tau G s k := by
  have : Fintype (GaloisField 2 B) := Fintype.ofFinite _
  have : DecidableEq (GaloisField 2 B) := Classical.decEq _
  rw [codedTime_congr (bitsEquivGaloisField (by omega : B ≠ 0)) s k]
  refine codedTime_eq_tau hG ?_ hk
  rw [Fintype.card_eq_nat_card (α := GaloisField 2 B), GaloisField.card 2 B (by omega)]
  exact hn

theorem two_le_card_bits {B : ℕ} (hB : 1 ≤ B) : 2 ≤ Fintype.card (Bits B) := by
  simp only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB

end CodingGap
