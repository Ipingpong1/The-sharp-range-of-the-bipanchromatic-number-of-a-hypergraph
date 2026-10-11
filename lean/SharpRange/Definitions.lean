import Mathlib

/-! Faithful finite-set definitions. Parameters are specified by attained extrema,
rather than by an arbitrary choice of a coloring. No hypergraph claims are assumed. -/
namespace Bipanchromatic
open Finset

structure Hypergraph (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Finset V)
  nonempty_edges : edges.Nonempty
  nonempty_edge : ∀ e ∈ edges, e.Nonempty

variable {V : Type*} [Fintype V] [DecidableEq V]

def Transversal (H : Hypergraph V) (C : Finset V) : Prop :=
  ∀ e ∈ H.edges, (C ∩ e).Nonempty

structure Partition (P : Finset (Finset V)) : Prop where
  nonempty : ∀ C ∈ P, C.Nonempty
  disjoint : (↑P : Set (Finset V)).PairwiseDisjoint id
  cover : P.biUnion id = univ

def Panchromatic (H : Hypergraph V) (P : Finset (Finset V)) : Prop :=
  Partition P ∧ ∀ C ∈ P, Transversal H C

def Bicoloring (H : Hypergraph V) (P : Finset (Finset V)) : Prop :=
  Panchromatic H P ∧ ∀ C ∈ P, 2 ≤ C.card

def singletonCount (P : Finset (Finset V)) : ℕ :=
  (P.filter (fun C => C.card = 1)).card

/-- Attainment AND maximality of the panchromatic number. -/
def HasPan (H : Hypergraph V) (p : ℕ) : Prop :=
  (∃ P, Panchromatic H P ∧ P.card = p) ∧
  ∀ P, Panchromatic H P → P.card ≤ p

/-- The minimum singleton count is taken only among optimal p-colorings. -/
def HasAlpha (H : Hypergraph V) (p a : ℕ) : Prop :=
  (∃ P, Panchromatic H P ∧ P.card = p ∧ singletonCount P = a) ∧
  ∀ P, Panchromatic H P → P.card = p → a ≤ singletonCount P

/-- Attainment AND maximality of the bipanchromatic number. -/
def HasBipan (H : Hypergraph V) (b : ℕ) : Prop :=
  (∃ P, Bicoloring H P ∧ P.card = b) ∧
  ∀ P, Bicoloring H P → P.card ≤ b

theorem partition_card_sum {P : Finset (Finset V)} (h : Partition P) :
    ∑ C ∈ P, C.card = Fintype.card V := by
  have hc := Finset.card_biUnion h.disjoint
  rw [h.cover] at hc
  simpa using hc.symm

theorem bipan_card_le_half {H : Hypergraph V} {P : Finset (Finset V)}
    (h : Bicoloring H P) : P.card ≤ Fintype.card V / 2 := by
  have hs := Finset.sum_le_sum h.2
  have he := partition_card_sum h.1.1
  simp only [Finset.sum_const, smul_eq_mul] at hs
  omega

theorem bipan_singletonCount {H : Hypergraph V} {P : Finset (Finset V)}
    (h : Bicoloring H P) : singletonCount P = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hCP, hcard⟩ := Finset.mem_filter.mp hC
  have := h.2 C hCP
  omega

theorem panchromatic_bipan_iff {H : Hypergraph V} {P : Finset (Finset V)}
    (h : Panchromatic H P) : Bicoloring H P ↔ singletonCount P = 0 := by
  constructor
  · exact bipan_singletonCount
  · intro hz
    refine ⟨h, fun C hC => ?_⟩
    have hpos := Finset.card_pos.mpr (h.1.nonempty C hC)
    have hn : C.card ≠ 1 := by
      intro he
      have hm : C ∈ P.filter (fun C => C.card = 1) := mem_filter.mpr ⟨hC, he⟩
      have hh := Finset.card_pos.mpr ⟨C, hm⟩
      change 0 < singletonCount P at hh
      omega
    omega

theorem range_upper {H : Hypergraph V} {p a b : ℕ}
    (hp : HasPan H p) (ha : HasAlpha H p a) (hb : HasBipan H b)
    (ha_pos : 0 < a) : b ≤ min (p - 1) (Fintype.card V / 2) := by
  obtain ⟨P, hP, hcard⟩ := hb.1
  have hle := hp.2 P hP.1
  have hhalf := bipan_card_le_half hP
  have hne : b ≠ p := by
    intro he
    have hcount := ha.2 P hP.1 (hcard.trans he)
    have hz := bipan_singletonCount hP
    omega
  omega

theorem parameter_feasible {H : Hypergraph V} {p a : ℕ}
    (ha : HasAlpha H p a) : 2 * p ≤ Fintype.card V + a := by
  obtain ⟨P, hP, hcard, hcount⟩ := ha.1
  have hs : ∑ C ∈ P, 2 ≤ ∑ C ∈ P, (C.card + if C.card = 1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro C hC
    have := Finset.card_pos.mpr (hP.1.nonempty C hC)
    split_ifs <;> omega
  rw [Finset.sum_add_distrib, partition_card_sum hP.1] at hs
  have hi : (∑ C ∈ P, if C.card = 1 then 1 else 0) = singletonCount P := by
    simp [singletonCount]
  rw [hi, hcount] at hs
  simpa [hcard, mul_comm] using hs

theorem singleton_transversal_iff (H : Hypergraph V) (v : V) :
    Transversal H {v} ↔ ∀ e ∈ H.edges, v ∈ e := by
  constructor
  · intro h e he
    obtain ⟨x, hx⟩ := h e he
    have hh := Finset.mem_inter.mp hx
    simpa using (Finset.mem_singleton.mp hh.1) ▸ hh.2
  · intro h e he
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h e he⟩⟩

/-- A fixed edge bounds the number of classes, via distinct intersection witnesses. -/
theorem pan_card_le_edge {H : Hypergraph V} {P : Finset (Finset V)}
    (hP : Panchromatic H P) {e : Finset V} (he : e ∈ H.edges) : P.card ≤ e.card := by
  classical
  have hw : ∀ C : P, ∃ v : e, (v : V) ∈ C.val := by
    intro C
    obtain ⟨v, hv⟩ := hP.2 C.val C.property e he
    exact ⟨⟨v, (mem_inter.mp hv).2⟩, (mem_inter.mp hv).1⟩
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro C D heq
    by_contra hne
    have hval : C.val ≠ D.val := fun h => hne (Subtype.ext h)
    have hd := hP.1.disjoint C.property D.property hval
    have hD : (f C : V) ∈ D.val := by simpa [heq] using hf D
    exact (Finset.disjoint_left.mp hd) (hf C) hD
  have hh := Fintype.card_le_of_injective f hinj
  simpa using hh

end Bipanchromatic

namespace Bipanchromatic
open Finset
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]

def fiber (c : V → K) (k : K) : Finset V := univ.filter (fun v => c v = k)
def colorPartition (c : V → K) : Finset (Finset V) := univ.image (fiber c)

omit [DecidableEq V] [Fintype K] in
@[simp] theorem mem_fiber (c : V → K) (k : K) (v : V) :
    v ∈ fiber c k ↔ c v = k := by simp [fiber]

omit [DecidableEq V] [Fintype K] in
theorem fiber_nonempty (c : V → K) (hc : Function.Surjective c) (k : K) :
    (fiber c k).Nonempty := by
  obtain ⟨v, hv⟩ := hc k
  exact ⟨v, (mem_fiber c k v).mpr hv⟩

omit [DecidableEq V] [Fintype K] in
theorem fiber_injective (c : V → K) (hc : Function.Surjective c) :
    Function.Injective (fiber c) := by
  intro k l h
  obtain ⟨v, hv⟩ := fiber_nonempty c hc k
  have hv' : v ∈ fiber c l := h ▸ hv
  exact ((mem_fiber c k v).mp hv).symm.trans ((mem_fiber c l v).mp hv')

theorem colorPartition_card (c : V → K) (hc : Function.Surjective c) :
    (colorPartition c).card = Fintype.card K := by
  rw [colorPartition, card_image_of_injective _ (fiber_injective c hc)]
  simp

theorem colorPartition_partition (c : V → K) (hc : Function.Surjective c) :
    Partition (colorPartition c) := by
  constructor
  · intro C hC
    obtain ⟨k, _, rfl⟩ := mem_image.mp hC
    exact fiber_nonempty c hc k
  · intro C hC D hD hne
    obtain ⟨k, _, rfl⟩ := mem_image.mp hC
    obtain ⟨l, _, rfl⟩ := mem_image.mp hD
    apply disjoint_left.mpr
    intro v hv hw
    have heq : k = l := ((mem_fiber c k v).mp hv).symm.trans ((mem_fiber c l v).mp hw)
    exact hne (congrArg (fiber c) heq)
  · ext v
    simp only [mem_biUnion, mem_univ, iff_true]
    exact ⟨fiber c (c v), mem_image.mpr ⟨c v, mem_univ _, rfl⟩,
      (mem_fiber c (c v) v).mpr rfl⟩

end Bipanchromatic

namespace Bipanchromatic
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma partition_contains {P : Finset (Finset V)} (hP : Partition P) (v : V) :
    ∃ C : P, v ∈ C.val := by
  have hv : v ∈ P.biUnion id := by rw [hP.cover]; exact mem_univ v
  obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
  exact ⟨⟨C, hC⟩, hvC⟩

noncomputable def owner {P : Finset (Finset V)} (hP : Partition P) (v : V) : P :=
  Classical.choose (partition_contains hP v)

lemma mem_owner {P : Finset (Finset V)} (hP : Partition P) (v : V) :
    v ∈ (owner hP v).val := Classical.choose_spec (partition_contains hP v)

lemma owner_eq_of_mem {P : Finset (Finset V)} (hP : Partition P)
    {v : V} {C : Finset V} (hC : C ∈ P) (hv : v ∈ C) : (owner hP v).val = C := by
  by_contra hn
  have hd := hP.disjoint (owner hP v).property hC hn
  exact (disjoint_left.mp hd) (mem_owner hP v) hv

/-- A coloring saturating an edge has exactly one vertex of each color on it. -/
theorem saturated_edge_same_class {H : Hypergraph V} {P : Finset (Finset V)}
    (hP : Panchromatic H P) {e C : Finset V} (he : e ∈ H.edges)
    (hsat : P.card = e.card) (hC : C ∈ P) {u v : V}
    (hu : u ∈ e) (hv : v ∈ e) (huC : u ∈ C) (hvC : v ∈ C) : u = v := by
  classical
  let f : e → P := fun w => owner hP.1 w.val
  have hsurj : Function.Surjective f := by
    intro D
    obtain ⟨w, hw⟩ := hP.2 D.val D.property e he
    obtain ⟨hwD, hwe⟩ := mem_inter.mp hw
    refine ⟨⟨w, hwe⟩, ?_⟩
    apply Subtype.ext
    exact owner_eq_of_mem hP.1 D.property hwD
  have hcard : Fintype.card e = Fintype.card P := by simpa using hsat.symm
  have hinj := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard⟩).1
  have hfu : (f ⟨u, hu⟩).val = C := owner_eq_of_mem hP.1 hC huC
  have hfv : (f ⟨v, hv⟩).val = C := owner_eq_of_mem hP.1 hC hvC
  exact congrArg Subtype.val (hinj (Subtype.ext (hfu.trans hfv.symm)))

/-- A vertex co-occurring with every other vertex is forced to be a singleton
in a coloring that saturates every edge. -/
theorem forced_singleton {H : Hypergraph V} {P : Finset (Finset V)}
    (hP : Panchromatic H P) (hsat : ∀ e ∈ H.edges, P.card = e.card)
    (u : V) (hu : ∀ v, ∃ e ∈ H.edges, u ∈ e ∧ v ∈ e) : {u} ∈ P := by
  let C := (owner hP.1 u).val
  have hC : C ∈ P := (owner hP.1 u).property
  have huC : u ∈ C := mem_owner hP.1 u
  have heq : C = {u} := by
    apply Finset.ext
    intro v
    constructor
    · intro hvC
      obtain ⟨e, he, hue, hve⟩ := hu v
      have h := saturated_edge_same_class hP he (hsat e he) hC hue hve huC hvC
      exact mem_singleton.mpr h.symm
    · intro hv
      simpa using (mem_singleton.mp hv) ▸ huC
  simpa [heq] using hC

end Bipanchromatic

namespace Bipanchromatic
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hasPan_unique {H : Hypergraph V} {p q : ℕ} (hp : HasPan H p) (hq : HasPan H q) : p = q := by
  obtain ⟨P, hP, hPc⟩ := hp.1
  obtain ⟨Q, hQ, hQc⟩ := hq.1
  have := hp.2 Q hQ
  have := hq.2 P hP
  omega

theorem hasAlpha_unique {H : Hypergraph V} {p a a' : ℕ}
    (ha : HasAlpha H p a) (ha' : HasAlpha H p a') : a = a' := by
  obtain ⟨P, hP, hPc, hPa⟩ := ha.1
  obtain ⟨Q, hQ, hQc, hQa⟩ := ha'.1
  have := ha.2 Q hQ hQc
  have := ha'.2 P hP hPc
  omega

theorem hasBipan_unique {H : Hypergraph V} {b c : ℕ} (hb : HasBipan H b) (hc : HasBipan H c) : b = c := by
  obtain ⟨P, hP, hPc⟩ := hb.1
  obtain ⟨Q, hQ, hQc⟩ := hc.1
  have := hb.2 Q hQ
  have := hc.2 P hP
  omega

end Bipanchromatic
