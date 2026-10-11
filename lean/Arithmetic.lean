import Lean

/-!
Arithmetic pilot for the sharp bipanchromatic range proof.
This file does NOT formalize hypergraphs or prove the full range theorem.
Natural subtraction is truncated: `a - S` represents max(a - S, 0).
Checked with Lean 4.34.1; no external libraries are required.
-/

namespace Bipanchromatic

def loss (a t S : Nat) : Nat := t + (a - S + 1) / 2

/-- The number of classes in the dissolution construction. -/
theorem dissolution_count (a q t S : Nat) (ht : t ≤ q) :
    q - t + min a S + (a - min a S) / 2 = a + q - loss a t S := by
  unfold loss
  omega

/-- More available partners cannot increase the loss. -/
theorem loss_antitone (a t S S' : Nat) (h : S ≤ S') :
    loss a t S' ≤ loss a t S := by
  unfold loss
  omega

/-- Adding at most one partner changes the loss by at most one. -/
theorem loss_step (a t S S' : Nat) (h₀ : S ≤ S') (h₁ : S' ≤ S + 1) :
    loss a t S' ≤ loss a t S ∧ loss a t S ≤ loss a t S' + 1 := by
  unfold loss
  omega

/-- In a concentrated size vector, t = 1 minimizes the positive-index costs. -/
theorem concentrated_positive_min (a D t : Nat) (ht : 1 ≤ t) :
    loss a 1 D ≤ loss a t (D + 2 * (t - 1)) := by
  unfold loss
  omega

/-- The t = 1 cost also beats the t = 0 cost, when a ≥ 1 and D ≥ 2. -/
theorem concentrated_beats_pairing (a D : Nat) (ha : 1 ≤ a) (hD : 2 ≤ D) :
    loss a 1 D ≤ loss a 0 0 := by
  unfold loss
  omega

/-- The concentrated construction has the claimed upper endpoint. -/
theorem concentrated_endpoint (a q D n : Nat)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hD : 2 ≤ D)
    (hn : n = a + D + 2 * (q - 1)) :
    a + q - loss a 1 D = min (a + q - 1) (n / 2) := by
  unfold loss
  omega

/-- A finite integer path with upward jumps at most one cannot skip a value
between its endpoints. Monotonicity is not even needed for this statement. -/
theorem bounded_jump_intermediate (f : Nat → Nat) (m k : Nat)
    (hsteps : ∀ i, i < m → f (i + 1) ≤ f i + 1)
    (hlo : f 0 ≤ k) (hhi : k ≤ f m) :
    ∃ i, i ≤ m ∧ f i = k := by
  induction m with
  | zero =>
      exact ⟨0, Nat.le_refl 0, Nat.le_antisymm hlo hhi⟩
  | succ m ih =>
      by_cases hk : k ≤ f m
      · obtain ⟨i, hi, heq⟩ := ih (fun j hj => hsteps j (by omega)) hk
        exact ⟨i, by omega, heq⟩
      · have hlast := hsteps m (by omega)
        exact ⟨m + 1, Nat.le_refl _, by omega⟩

#print axioms dissolution_count
#print axioms loss_antitone
#print axioms loss_step
#print axioms concentrated_positive_min
#print axioms concentrated_beats_pairing
#print axioms concentrated_endpoint
#print axioms bounded_jump_intermediate

end Bipanchromatic
