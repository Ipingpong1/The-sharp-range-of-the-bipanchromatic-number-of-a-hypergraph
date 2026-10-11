import SharpRange.Target
import SharpRange.Recoloring

namespace Bipanchromatic
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def singletonVertices (P : Finset (Finset V)) : Finset V := univ.filter (fun v => {v} ∈ P)

lemma singletonVertices_card (P : Finset (Finset V)) : (singletonVertices P).card = singletonCount P := by
  have hset : (singletonVertices P).image (fun v => ({v} : Finset V)) = P.filter (fun B => B.card = 1) := by
    ext B
    constructor
    · intro hB
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hB
      exact mem_filter.mpr ⟨(mem_filter.mp hv).2, by simp⟩
    · intro hB
      obtain ⟨hBP, hcard⟩ := mem_filter.mp hB
      obtain ⟨v, rfl⟩ := card_eq_one.mp hcard
      exact mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ v, hBP⟩, rfl⟩
  have hinj : Function.Injective (fun v : V => ({v} : Finset V)) := by
    intro v w h
    simpa using h
  have hh := congrArg Finset.card hset
  rw [card_image_of_injective _ hinj] at hh
  exact hh

/-- Extract the genuine nonsingleton classes from a coloring and perform the
recoloring. No statement about the hypergraph's bipanchromatic number is assumed. -/
theorem lower_from_coloring (H : Hypergraph V) (P : Finset (Finset V))
    (hP : Panchromatic H P) (p a : ℕ) (hcard : P.card = p) (hcount : singletonCount P = a)
    (ha : 0 < a) (hap : a < p) :
    ∃ Q, Bicoloring H Q ∧ sharpLower (Fintype.card V) p a ≤ Q.card := by
  classical
  let S := P.filter (fun B => B.card = 1)
  let N := P \ S
  let C := singletonVertices P
  let A : N → Finset V := fun B => B.val
  have hSP : S ⊆ P := filter_subset _ _
  have hNP : N ⊆ P := sdiff_subset
  have hSc : S.card = a := hcount
  have hCc : C.card = a := (singletonVertices_card P).trans hcount
  have hNc : Fintype.card N = p - a := by
    have hh := card_sdiff_of_subset hSP
    change N.card = P.card - S.card at hh
    simpa [hcard, hSc] using hh
  have hAs : ∀ i : N, 2 ≤ (A i).card := by
    intro i
    have hpos := card_pos.mpr (hP.1.nonempty i.val (hNP i.property))
    have hnot : i.val.card ≠ 1 := by
      intro hh
      exact (mem_sdiff.mp i.property).2 (mem_filter.mpr ⟨hNP i.property, hh⟩)
    dsimp only [A]
    omega
  have hcore : ∀ v ∈ C, Transversal H {v} := by
    intro v hv
    exact hP.2 {v} (mem_filter.mp hv).2
  have hApart : Pairwise (fun i j : N => Disjoint (A i) (A j)) := by
    intro i j hij
    exact hP.1.disjoint (hNP i.property) (hNP j.property) (fun he => hij (Subtype.ext he))
  have hCA : ∀ i : N, Disjoint C (A i) := by
    intro i
    apply disjoint_left.mpr
    intro v hvC hvA
    have hvP : {v} ∈ P := (mem_filter.mp hvC).2
    have hne : ({v} : Finset V) ≠ A i := by
      intro he
      have hc := congrArg Finset.card he
      have hh := hAs i
      simp only [card_singleton] at hc
      omega
    exact (disjoint_left.mp (hP.1.disjoint hvP (hNP i.property) hne)) (mem_singleton_self v) hvA
  have hAt : ∀ i : N, Transversal H (A i) := fun i => hP.2 i.val (hNP i.property)
  have hC : C.Nonempty := card_pos.mp (by omega)
  have hN : 0 < Fintype.card N := by omega
  obtain ⟨Q, hQ, hQc⟩ := recolor_sizeValue H C A hC hN hcore hApart hCA hAt hAs
  have hsumS : (∑ B ∈ S, B.card) = a := by
    calc
      _ = ∑ _B ∈ S, 1 := sum_congr rfl (fun B hB => (mem_filter.mp hB).2)
      _ = a := by simpa using hSc
  have hsum := sum_sdiff (f := fun B : Finset V => B.card) hSP
  rw [hsumS, partition_card_sum hP.1] at hsum
  have htotal : (∑ i : N, (A i).card) = Fintype.card V - a := by
    have hcoe : (∑ i : N, (A i).card) = ∑ B ∈ N, B.card := sum_coe_sort N _
    change (∑ B ∈ N, B.card) + a = Fintype.card V at hsum
    omega
  let s := (Fintype.card V - a) / (p - a)
  let r := (Fintype.card V - a) % (p - a)
  have hr : r < Fintype.card N := by
    rw [hNc]
    exact Nat.mod_lt _ (by omega)
  have htotal' : (∑ i : N, (A i).card) = Fintype.card N * s + r := by
    rw [htotal, hNc]
    have hdiv := Nat.mod_add_div (Fintype.card V - a) (p - a)
    dsimp only [s, r]
    omega
  have hl := sizeValue_ge_balanced C.card (fun i : N => (A i).card) s r hr htotal'
  have hbound : balancedLower C.card (Fintype.card N) s r = sharpLower (Fintype.card V) p a := by
    rw [balancedLower_eq_sub_minLoss, hCc, hNc]
    have hpa : a + (p - a) = p := by omega
    rw [hpa]
    rfl
  exact ⟨Q, hQ, by rw [hQc, ← hbound]; exact hl⟩

/-- The universal lower-bound target, now proved. -/
theorem universal_lower : UniversalLowerStatement := by
  intro n p a H _hp ha hap _hpan halpha
  obtain ⟨P, hP, hcard, hcount⟩ := halpha.1
  simpa using lower_from_coloring H P hP p a hcard hcount ha hap

end Bipanchromatic
