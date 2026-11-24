module

public import RigidGHZ.Supplement.Doubling

/-! The explicit edge replacement used by supplemental grafting. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ

 theorem PerfectMatching.edge_eq_of_vertex {V : Type*} [DecidableEq V]
    {H M : Hypergraph V} (hM : PerfectMatching H M) {e f : Finset V}
    (he : e ∈ M) (hf : f ∈ M) {v : V} (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  obtain ⟨g, hg, hu⟩ := hM.existsUnique_edge v
  exact (hu e ⟨he, hve⟩).trans (hu f ⟨hf, hvf⟩).symm

namespace Supplement.Graft

variable {V A W I : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq W]

/-- Replace the selected old vertex `inr a` by one chosen vertex of part `a`. -/
def inheritVertex (z : A → W) : (V ⊕ A) ↪ (V ⊕ (A × W)) where
  toFun
    | .inl v => .inl v
    | .inr a => .inr (a, z a)
  inj' := by
    intro v w h
    cases v <;> cases w <;> simp_all

 def inheritEdge (z : A → W) (e : Finset (V ⊕ A)) : Finset (V ⊕ (A × W)) :=
  e.map (inheritVertex z)

 def internalEdge (e : Finset (A × W)) : Finset (V ⊕ (A × W)) :=
  e.map Function.Embedding.inr

 def contractVertex : (V ⊕ (A × W)) → (V ⊕ A)
  | .inl v => .inl v
  | .inr aw => .inr aw.1

 def contractEdge (e : Finset (V ⊕ (A × W))) : Finset (V ⊕ A) := e.image contractVertex

@[simp] theorem mem_inherit_left (z : A → W) (e : Finset (V ⊕ A)) (v : V) :
    Sum.inl v ∈ inheritEdge z e ↔ Sum.inl v ∈ e := by
  simp only [inheritEdge, Finset.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    cases x <;> simp_all [inheritVertex]
  · intro hv
    exact ⟨Sum.inl v, hv, rfl⟩

@[simp] theorem mem_inherit_right (z : A → W) (e : Finset (V ⊕ A)) (a : A) (w : W) :
    Sum.inr (a, w) ∈ inheritEdge z e ↔ Sum.inr a ∈ e ∧ w = z a := by
  simp only [inheritEdge, Finset.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    cases x with
    | inl v => simp [inheritVertex] at he
    | inr b =>
      have hab : b = a ∧ z b = w := by simpa [inheritVertex] using he
      obtain ⟨rfl, hw⟩ := hab
      exact ⟨hx, hw.symm⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨Sum.inr a, ha, rfl⟩

@[simp] theorem mem_internal_left (e : Finset (A × W)) (v : V) :
    Sum.inl v ∉ internalEdge (V := V) e := by simp [internalEdge]

@[simp] theorem mem_internal_right (e : Finset (A × W)) (a : A) (w : W) :
    Sum.inr (a, w) ∈ internalEdge (V := V) e ↔ (a, w) ∈ e := by simp [internalEdge]

@[simp] theorem contract_inherit (z : A → W) (e : Finset (V ⊕ A)) :
    contractEdge (inheritEdge z e) = e := by
  ext v
  simp only [contractEdge, inheritEdge, Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, hv⟩
    have : contractVertex (inheritVertex z u) = u := by cases u <;> rfl
    rw [this] at hv
    simpa only [hv] using hu
  · intro hv
    exact ⟨inheritVertex z v, ⟨v, hv, rfl⟩, by cases v <;> rfl⟩

 theorem internalEdge_injective : Function.Injective (internalEdge (V := V) (A := A) (W := W)) :=
  Finset.map_injective Function.Embedding.inr

@[simp] theorem inheritEdge_card (z : A → W) (e : Finset (V ⊕ A)) :
    (inheritEdge z e).card = e.card := Finset.card_map _

@[simp] theorem internalEdge_card (e : Finset (A × W)) :
    (internalEdge (V := V) e).card = e.card := Finset.card_map _

variable [Fintype A] [Fintype W] [Fintype I]

/-- Input rigid families and the selected edge through the root of each right
matching. These witnesses are obtained from the actual perfect matchings. -/
structure Data (H : Hypergraph (V ⊕ A)) (S : Hypergraph (A × W)) where
  left : RigidFamily H I
  right : RigidFamily S I
  a0 : A
  w0 : W
  special : I → A → W
  special_mem : ∀ i, tupleEdge (special i) ∈ right.matching i
  special_root : ∀ i, special i a0 = w0
  transversal : ∀ e ∈ S, ∃ x : A → W, e = tupleEdge x

 theorem data_nonempty {H : Hypergraph (V ⊕ A)} {S : Hypergraph (A × W)}
    (L : RigidFamily H I) (R : RigidFamily S I) (a0 : A) (w0 : W)
    (htrans : ∀ e ∈ S, ∃ x : A → W, e = tupleEdge x) :
    Nonempty (Data (I := I) H S) := by
  classical
  obtain ⟨p, hp0, hpM, hpsep, hpcomplete⟩ := coordinates_of_rigidFamily a0 R htrans
  refine ⟨⟨L, R, a0, w0, fun i a => p i a w0, ?_, ?_, htrans⟩⟩
  · intro i
    rw [hpM i]
    exact Finset.mem_image.mpr ⟨w0, Finset.mem_univ _, rfl⟩
  · intro i
    rw [hp0 i]
    rfl

namespace Data

variable {H : Hypergraph (V ⊕ A)} {S : Hypergraph (A × W)} (D : Data (I := I) H S)

noncomputable def selector (e : Finset (V ⊕ A)) : A → W :=
  if he : e ∈ H then D.special (Classical.choose (D.left.mem_iff.mp he)) else fun _ => D.w0

 theorem selector_on_matching {e : Finset (V ⊕ A)} {i : I} (he : e ∈ D.left.matching i) :
    D.selector e = D.special i := by
  classical
  have hH := (D.left.perfect i).subset he
  rw [selector, dif_pos hH]
  have hc := Classical.choose_spec (D.left.mem_iff.mp hH)
  have hi := D.left.eq_of_shared_edge hc he
  rw [hi]

@[simp] theorem selector_root (e : Finset (V ⊕ A)) : D.selector e D.a0 = D.w0 := by
  classical
  unfold selector
  split_ifs with he
  · exact D.special_root _
  · rfl

noncomputable def lifted (e : Finset (V ⊕ A)) : Finset (V ⊕ (A × W)) := inheritEdge (D.selector e) e

def internal : Hypergraph (A × W) := S.filter (fun e => (D.a0, D.w0) ∉ e)

noncomputable def graph : Hypergraph (V ⊕ (A × W)) :=
  H.image D.lifted ∪ D.internal.image internalEdge

noncomputable def matching (i : I) : Hypergraph (V ⊕ (A × W)) :=
  (D.left.matching i).image D.lifted ∪
    ((D.right.matching i).erase (tupleEdge (D.special i))).image internalEdge

 theorem lifted_injective : Function.Injective D.lifted := by
  intro e f h
  have := congrArg contractEdge h
  simpa only [lifted, contract_inherit] using this

@[simp] theorem lifted_card (e : Finset (V ⊕ A)) : (D.lifted e).card = e.card := by
  exact inheritEdge_card _ _

@[simp] theorem mem_lifted_left (e : Finset (V ⊕ A)) (v : V) :
    Sum.inl v ∈ D.lifted e ↔ Sum.inl v ∈ e := mem_inherit_left _ _ _

@[simp] theorem mem_lifted_right (e : Finset (V ⊕ A)) (a : A) (w : W) :
    Sum.inr (a, w) ∈ D.lifted e ↔ Sum.inr a ∈ e ∧ w = D.selector e a :=
  mem_inherit_right _ _ _ _

 theorem special_contains_root (i : I) : (D.a0, D.w0) ∈ tupleEdge (D.special i) := by
  simp only [mem_tupleEdge, D.special_root]

 theorem root_iff_special {i : I} {e : Finset (A × W)} (he : e ∈ D.right.matching i) :
    (D.a0, D.w0) ∈ e ↔ e = tupleEdge (D.special i) := by
  constructor
  · intro hr
    exact (D.right.perfect i).edge_eq_of_vertex he (D.special_mem i) hr (D.special_contains_root i)
  · rintro rfl
    exact D.special_contains_root i

 theorem mem_internal_of_erased {i : I} {e : Finset (A × W)}
    (he : e ∈ (D.right.matching i).erase (tupleEdge (D.special i))) : e ∈ D.internal := by
  obtain ⟨hne, he⟩ := Finset.mem_erase.mp he
  exact Finset.mem_filter.mpr ⟨(D.right.perfect i).subset he,
    fun hr => hne ((D.root_iff_special he).mp hr)⟩

 theorem internal_root_witness {e : Finset (A × W)} (he : e ∈ D.internal) :
    ∃ w, w ≠ D.w0 ∧ (D.a0, w) ∈ e := by
  obtain ⟨heS, hn⟩ := Finset.mem_filter.mp he
  obtain ⟨x, rfl⟩ := D.transversal e heS
  refine ⟨x D.a0, ?_, ?_⟩
  · intro h
    apply hn
    simp [h]
  · simp

 theorem lifted_ne_internal (e : Finset (V ⊕ A)) {f : Finset (A × W)}
    (hf : f ∈ D.internal) : D.lifted e ≠ internalEdge f := by
  intro heq
  obtain ⟨w, hw, hmem⟩ := D.internal_root_witness hf
  have hnew : Sum.inr (D.a0, w) ∈ D.lifted e := by
    rw [heq]
    exact (mem_internal_right f D.a0 w).mpr hmem
  exact hw (((D.mem_lifted_right e D.a0 w).mp hnew).2.trans (D.selector_root e))

 theorem matching_subset (i : I) : D.matching i ⊆ D.graph := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, (D.left.perfect i).subset hf, rfl⟩)
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, D.mem_internal_of_erased hf, rfl⟩)

 theorem graph_uniform {r : ℕ} (hH : Uniform H r) (hS : Uniform S r) : Uniform D.graph r := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa using hH f hf
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa using hS f (Finset.mem_filter.mp hf).1

end Data
end Supplement.Graft
end RigidGHZ
