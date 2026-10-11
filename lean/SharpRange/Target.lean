import SharpRange.Balanced
import SharpRange.Construction
import SharpRange.Packing

namespace Bipanchromatic
open Finset

private theorem range_nonempty (q : ℕ) : (range (q + 1)).Nonempty := ⟨0, by simp⟩

def minLoss (a q s r : ℕ) : ℕ :=
  (range (q + 1)).inf' (range_nonempty q) (fun t => loss a t (s * t + min t r))

/-- The maximum formulation used by the numerical development equals the
p-minus-minimum formulation in the written theorem. -/
theorem balancedLower_eq_sub_minLoss (a q s r : ℕ) :
    balancedLower a q s r = a + q - minLoss a q s r := by
  apply Nat.le_antisymm
  · unfold balancedLower
    apply Finset.sup_le
    intro t ht
    have h := Finset.inf'_le (s := range (q + 1)) (fun t => loss a t (s * t + min t r)) ht
    change minLoss a q s r ≤ loss a t (s * t + min t r) at h
    omega
  · obtain ⟨t, ht, heq⟩ := exists_mem_eq_inf' (range_nonempty q) (fun t => loss a t (s * t + min t r))
    change minLoss a q s r = loss a t (s * t + min t r) at heq
    have h := Finset.le_sup (s := range (q + 1))
      (f := fun t => a + q - loss a t (s * t + min t r)) ht
    simpa only [← heq, balancedLower] using h

def sharpLower (n p a : ℕ) : ℕ :=
  p - minLoss a (p - a) ((n - a) / (p - a)) ((n - a) % (p - a))

def sharpUpper (n p : ℕ) : ℕ := min (p - 1) (n / 2)

/-- Exact main statement, proved by `sharp_range` in SharpRange/Full.lean. -/
def SharpRangeStatement : Prop :=
  ∀ n p a : ℕ, 2 ≤ p → 1 ≤ a → a < p → 2 * p ≤ n + a →
    ∀ b : ℕ,
    (∃ H : Hypergraph (Fin n), HasPan H p ∧ HasAlpha H p a ∧ HasBipan H b) ↔
    sharpLower n p a ≤ b ∧ b ≤ sharpUpper n p

/-- Exact model statement for q ≥ 1, proved by `model_value`. -/
def ModelValueStatement : Prop :=
  ∀ (a q : ℕ) (d : Fin q → ℕ) (_hq : 0 < q) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i),
    HasBipan (Model.hypergraph a d ha hd) (sizeValue a d)

/-- Universal lower-bound statement, proved by `universal_lower`. -/
def UniversalLowerStatement : Prop :=
  ∀ (n p a : ℕ) (H : Hypergraph (Fin n)), 2 ≤ p → 1 ≤ a → a < p →
    HasPan H p → HasAlpha H p a →
    ∃ P, Bicoloring H P ∧ sharpLower n p a ≤ P.card

end Bipanchromatic
