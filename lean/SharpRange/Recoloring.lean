import SharpRange.Pairing
import SharpRange.SizeVectors

namespace Bipanchromatic
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

structure GoodPacking (H : Hypergraph V) (P : Finset (Finset V)) : Prop where
  disjoint : (↑P : Set (Finset V)).PairwiseDisjoint id
  trans : ∀ B ∈ P, Transversal H B
  size : ∀ B ∈ P, 2 ≤ B.card

lemma GoodPacking.union {H : Hypergraph V} {P Q : Finset (Finset V)}
    (hP : GoodPacking H P) (hQ : GoodPacking H Q)
    (hc : ∀ B ∈ P, ∀ D ∈ Q, Disjoint B D) :
    GoodPacking H (P ∪ Q) ∧ (P ∪ Q).card = P.card + Q.card := by
  have hPQ : Disjoint P Q := by
    apply disjoint_left.mpr
    intro B hB hD
    have hh := hc B hB B hD
    have hne : B.Nonempty := card_pos.mp (by have := hP.size B hB; omega)
    obtain ⟨v, hv⟩ := hne
    exact (disjoint_left.mp hh) hv hv
  refine ⟨⟨?_, ?_, ?_⟩, card_union_of_disjoint hPQ⟩
  · intro B hB D hD hBD
    rcases mem_union.mp hB with hB | hB <;> rcases mem_union.mp hD with hD | hD
    · exact hP.disjoint hB hD hBD
    · exact hc B hB D hD
    · exact (hc D hD B hB).symm
    · exact hQ.disjoint hB hD hBD
  · intro B hB
    rcases mem_union.mp hB with hB | hB
    · exact hP.trans B hB
    · exact hQ.trans B hB
  · intro B hB
    rcases mem_union.mp hB with hB | hB
    · exact hP.size B hB
    · exact hQ.size B hB

lemma GoodPacking.complete {H : Hypergraph V} {P : Finset (Finset V)}
    (hP : GoodPacking H P) (hne : 0 < P.card) :
    ∃ Q, Bicoloring H Q ∧ Q.card = P.card := by
  obtain ⟨Q, hQ, hcard, hsize⟩ := complete_packing H P 2 (card_pos.mp hne)
    (fun C hC => card_pos.mp (by have := hP.size C hC; omega)) hP.disjoint hP.trans hP.size
  exact ⟨Q, ⟨hQ, hsize⟩, hcard⟩

/-- Recolor an explicit disjoint collection of nonsingleton transversals and
singleton transversals. The sets need not exhaust V: completion adds leftovers. -/
theorem recolor_parts (H : Hypergraph V) (C : Finset V) (A : I → Finset V)
    (hC : C.Nonempty) (hI : 0 < Fintype.card I)
    (hcore : ∀ v ∈ C, Transversal H {v})
    (hApart : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hCA : ∀ i, Disjoint C (A i))
    (hAt : ∀ i, Transversal H (A i)) (hAs : ∀ i, 2 ≤ (A i).card)
    (S : Finset I) :
    ∃ Q, Bicoloring H Q ∧ Q.card =
      C.card + Fintype.card I - loss C.card S.card (∑ i ∈ S, (A i).card) := by
  classical
  let W := S.biUnion A
  have hCW : Disjoint C W := by
    apply disjoint_left.mpr
    intro v hvC hvW
    obtain ⟨i, _, hvi⟩ := mem_biUnion.mp hvW
    exact (disjoint_left.mp (hCA i)) hvC hvi
  have hWcard : W.card = ∑ i ∈ S, (A i).card := by
    exact card_biUnion (fun i _ j _ hij => hApart hij)
  obtain ⟨P, hP, hPcard⟩ := exists_pairPacking C W hCW
  have hPg : GoodPacking H P := by
    refine ⟨hP.disjoint, ?_, fun B hB => by rw [hP.size B hB]⟩
    intro B hB e he
    obtain ⟨v, hv⟩ := hP.core B hB
    have hvC := (mem_inter.mp hv).2
    have hve := (singleton_transversal_iff H v).mp (hcore v hvC) e he
    exact ⟨v, mem_inter.mpr ⟨(mem_inter.mp hv).1, hve⟩⟩
  have hAinj : Function.Injective A := by
    intro i j hij
    by_contra hne
    have hd := hApart hne
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (A i).card by have := hAs i; omega)
    exact (disjoint_left.mp hd) hv (hij ▸ hv)
  let R := Sᶜ.image A
  have hRcard : R.card = Fintype.card I - S.card := by
    dsimp only [R]
    rw [card_image_of_injective _ hAinj, card_compl]
  have hRg : GoodPacking H R := by
    constructor
    · intro B hB D hD hBD
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      obtain ⟨j, _, rfl⟩ := mem_image.mp hD
      exact hApart (fun hij => hBD (congrArg A hij))
    · intro B hB
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      exact hAt i
    · intro B hB
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      exact hAs i
  have hcross : ∀ B ∈ P, ∀ D ∈ R, Disjoint B D := by
    intro B hB D hD
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hD
    apply disjoint_left.mpr
    intro v hvB hvAj
    rcases mem_union.mp (hP.support B hB hvB) with hvC | hvW
    · exact (disjoint_left.mp (hCA j)) hvC hvAj
    · obtain ⟨i, hi, hvAi⟩ := mem_biUnion.mp hvW
      have hij : i ≠ j := fun heq => (mem_compl.mp hj) (heq ▸ hi)
      exact (disjoint_left.mp (hApart hij)) hvAi hvAj
  have hUR := hPg.union hRg hcross
  have hSc : S.card ≤ Fintype.card I := by simpa using card_le_card (subset_univ S)
  have htwo : 2 * S.card ≤ ∑ i ∈ S, (A i).card := by
    have hs := sum_le_sum (s := S) (f := fun _ => 2) (g := fun i => (A i).card) (fun i _ => hAs i)
    simpa [mul_comm] using hs
  have hCpos := card_pos.mpr hC
  have hcount : (P ∪ R).card = C.card + Fintype.card I - loss C.card S.card (∑ i ∈ S, (A i).card) := by
    rw [hUR.2, hPcard, hRcard, hWcard]
    unfold loss
    omega
  have hpos : 0 < (P ∪ R).card := by
    rw [hUR.2, hPcard, hRcard, hWcard]
    omega
  obtain ⟨Q, hQ, hQc⟩ := hUR.1.complete hpos
  exact ⟨Q, hQ, hQc.trans hcount⟩

/-- Maximizing the constructed recoloring gives the entire size-vector bound. -/
theorem recolor_sizeValue (H : Hypergraph V) (C : Finset V) (A : I → Finset V)
    (hC : C.Nonempty) (hI : 0 < Fintype.card I)
    (hcore : ∀ v ∈ C, Transversal H {v})
    (hApart : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hCA : ∀ i, Disjoint C (A i))
    (hAt : ∀ i, Transversal H (A i)) (hAs : ∀ i, 2 ≤ (A i).card) :
    ∃ Q, Bicoloring H Q ∧ Q.card = sizeValue C.card (fun i => (A i).card) := by
  obtain ⟨t, ht, hval⟩ := exists_mem_eq_sup (range (Fintype.card I + 1)) ⟨0, by simp⟩
    (fun t => C.card + Fintype.card I - loss C.card t (topSum (fun i => (A i).card) t))
  have ht' : t ≤ Fintype.card I := by have := mem_range.mp ht; omega
  obtain ⟨S, hSc, hsum⟩ := exists_topSum (fun i => (A i).card) t ht'
  obtain ⟨Q, hQ, hQc⟩ := recolor_parts H C A hC hI hcore hApart hCA hAt hAs S
  refine ⟨Q, hQ, ?_⟩
  simpa only [hSc, ← hsum, sizeValue, hval] using hQc

end Bipanchromatic
