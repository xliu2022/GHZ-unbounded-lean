module

public import RigidGHZ.Finite.FivePairObservation
public import Mathlib.Data.Fintype.EquivFin

/-! Claim B.1 on an arbitrary five-element ground type. The union of two
adjacent pairs is the complement of its color, so equality of unions expresses
equality of omitted-point colors without choosing numeric labels. -/

@[expose] public section

namespace RigidGHZ.Finite.FivePair

abbrev PairOn (V : Type*) := {p : Finset V // p.card = 2}

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def edgesOn (L R : Finset (PairOn V)) : Finset (PairOn V × PairOn V) :=
  (L.product R).filter (fun e => Disjoint e.1.val e.2.val)

theorem mem_edgesOn {L R : Finset (PairOn V)} {p q : PairOn V} :
    (p, q) ∈ edgesOn L R ↔ p ∈ L ∧ q ∈ R ∧ Disjoint p.val q.val := by
  constructor
  · intro h
    obtain ⟨hpq, ha⟩ := Finset.mem_filter.mp h
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    exact ⟨hp, hq, ha⟩
  · rintro ⟨hp, hq, ha⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, ha⟩

structure ConditionsOn (L R : Finset (PairOn V)) : Prop where
  left_unique : ∀ p ∈ L, ∀ q ∈ R, ∀ q' ∈ R,
    Disjoint p.val q.val → Disjoint p.val q'.val → q = q'
  right_unique : ∀ q ∈ R, ∀ p ∈ L, ∀ p' ∈ L,
    Disjoint p.val q.val → Disjoint p'.val q.val → p = p'
  color_unique : ∀ p ∈ L, ∀ q ∈ R, ∀ p' ∈ L, ∀ q' ∈ R,
    Disjoint p.val q.val → Disjoint p'.val q'.val →
    p.val ∪ q.val = p'.val ∪ q'.val → p = p' ∧ q = q'

def mapPair (e : V ≃ W) (p : PairOn V) : PairOn W :=
  ⟨p.val.map e.toEmbedding, by simpa using p.property⟩

theorem mapPair_injective (e : V ≃ W) : Function.Injective (mapPair e) := by
  intro p q hpq
  apply Subtype.ext
  apply Finset.map_injective e.toEmbedding
  exact congrArg Subtype.val hpq

theorem mapPair_disjoint (e : V ≃ W) (p q : PairOn V) :
    Disjoint (mapPair e p).val (mapPair e q).val ↔ Disjoint p.val q.val :=
  Finset.disjoint_map e.toEmbedding

theorem mapPair_union_injective (e : V ≃ W) {p q p' q' : PairOn V}
    (h : (mapPair e p).val ∪ (mapPair e q).val =
      (mapPair e p').val ∪ (mapPair e q').val) : p.val ∪ q.val = p'.val ∪ q'.val := by
  apply Finset.map_injective e.toEmbedding
  simpa only [mapPair, Finset.map_union] using h

theorem mapPair_prod_injective (e : V ≃ W) :
    Function.Injective (fun p : PairOn V × PairOn V => (mapPair e p.1, mapPair e p.2)) := by
  intro p q hpq
  exact Prod.ext (mapPair_injective e (congrArg Prod.fst hpq))
    (mapPair_injective e (congrArg Prod.snd hpq))

theorem edgesOn_map (e : V ≃ W) (L R : Finset (PairOn V)) :
    edgesOn (L.image (mapPair e)) (R.image (mapPair e)) =
      (edgesOn L R).image (fun p => (mapPair e p.1, mapPair e p.2)) := by
  ext pq
  rcases pq with ⟨p, q⟩
  constructor
  · intro h
    obtain ⟨hp, hq, ha⟩ := mem_edgesOn.mp h
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨(p₀, q₀),
      mem_edgesOn.mpr ⟨hp₀, hq₀, (mapPair_disjoint e p₀ q₀).mp ha⟩, rfl⟩
  · intro h
    obtain ⟨⟨p₀, q₀⟩, hpq, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hp₀, hq₀, ha⟩ := mem_edgesOn.mp hpq
    cases heq
    exact mem_edgesOn.mpr ⟨Finset.mem_image.mpr ⟨_, hp₀, rfl⟩,
      Finset.mem_image.mpr ⟨_, hq₀, rfl⟩, (mapPair_disjoint e p₀ q₀).mpr ha⟩

theorem conditionsOn_to_five (e : V ≃ Fin 5) {L R : Finset (PairOn V)}
    (h : ConditionsOn L R) : Conditions (L.image (mapPair e)) (R.image (mapPair e)) := by
  constructor
  · intro p hp q hq q' hq' ha hb
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hq'
    exact congrArg (mapPair e) (h.left_unique p₀ hp₀ q₀ hq₀ q₁ hq₁
      ((mapPair_disjoint e _ _).mp ha) ((mapPair_disjoint e _ _).mp hb))
  · intro q hq p hp p' hp' ha hb
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hp'
    exact congrArg (mapPair e) (h.right_unique q₀ hq₀ p₀ hp₀ p₁ hp₁
      ((mapPair_disjoint e _ _).mp ha) ((mapPair_disjoint e _ _).mp hb))
  · rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' hc
    obtain ⟨hp, hq, ha⟩ := mem_edges.mp hpq
    obtain ⟨hp', hq', hb⟩ := mem_edges.mp hpq'
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hp'
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hq'
    have hu : (mapPair e p₀).val ∪ (mapPair e q₀).val =
        (mapPair e p₁).val ∪ (mapPair e q₁).val := by
      rw [color_correct _ _ ha, color_correct _ _ hb, hc]
    obtain ⟨rfl, rfl⟩ := h.color_unique p₀ hp₀ q₀ hq₀ p₁ hp₁ q₁ hq₁
      ((mapPair_disjoint e _ _).mp ha) ((mapPair_disjoint e _ _).mp hb)
      (mapPair_union_injective e hu)
    rfl

/-- Claim B.1 for an arbitrary five-element ground set, with no fixed
numbering, no hypergraph rigidity assumption, and no assumed edge list. -/
theorem observation_on_five [Fintype V] (hV : Fintype.card V = 5)
    {L R : Finset (PairOn V)} (h : ConditionsOn L R) :
    ((edgesOn L R).card = 5 → L.card + R.card = 10) ∧
    ((edgesOn L R).card = 4 → L.card + R.card ≤ 9) := by
  classical
  let e : V ≃ Fin 5 := Fintype.equivFinOfCardEq hV
  have hobs := observation (conditionsOn_to_five e h)
  have he : (edges (L.image (mapPair e)) (R.image (mapPair e))).card =
      (edgesOn L R).card := by
    change (edgesOn (L.image (mapPair e)) (R.image (mapPair e))).card = _
    rw [edgesOn_map, Finset.card_image_of_injective _ (mapPair_prod_injective e)]
  rw [he, Finset.card_image_of_injective _ (mapPair_injective e),
    Finset.card_image_of_injective _ (mapPair_injective e)] at hobs
  exact hobs

end RigidGHZ.Finite.FivePair
