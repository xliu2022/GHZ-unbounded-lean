module

public import RigidGHZ.Basic

@[expose] public section

namespace RigidGHZ

/-- A balanced multipartition whose every edge meets every part exactly once. -/
def BalancedPartite {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (r m : ℕ) : Prop :=
  ∃ color : V → Fin r,
    (∀ i, (Finset.univ.filter (fun v => color v = i)).card = m) ∧
    ∀ e ∈ H, ∀ i, (e.filter (fun v => color v = i)).card = 1

section Tuple

variable {A W : Type*} [Fintype A] [DecidableEq A] [DecidableEq W]

/-- A transversal edge encoded by one coordinate in each part. -/
def tupleEdge (x : A → W) : Finset (A × W) :=
  Finset.univ.image (fun a => (a, x a))

@[simp] theorem mem_tupleEdge {x : A → W} {a : A} {w : W} :
    (a, w) ∈ tupleEdge x ↔ w = x a := by
  simp [tupleEdge, eq_comm]

 theorem tupleEdge_injective : Function.Injective (tupleEdge : (A → W) → Finset (A × W)) := by
  intro x y h
  funext a
  have hx : (a, x a) ∈ tupleEdge x := by simp
  rw [h] at hx
  simpa using hx

@[simp] theorem tupleEdge_card (x : A → W) : (tupleEdge x).card = Fintype.card A := by
  unfold tupleEdge
  rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
  simp

/-- Convert a finite set of coordinate tuples into an ordinary simple hypergraph. -/
def tupleHypergraph (E : Finset (A → W)) : Hypergraph (A × W) :=
  E.image tupleEdge

 theorem tupleHypergraph_uniform (E : Finset (A → W)) :
    Uniform (tupleHypergraph E) (Fintype.card A) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  simp

variable [Fintype W]

/-- The matching prescribed by coordinate maps, with rows indexed by `W`. -/
def coordinateMatching (p : A → W → W) : Hypergraph (A × W) :=
  Finset.univ.image (fun w => tupleEdge (fun a => p a w))

 theorem coordinateMatching_perfect [Nonempty A] (p : A → W → W)
    (hp : ∀ a, Function.Bijective (p a)) :
    PerfectMatching (coordinateMatching p) (coordinateMatching p) := by
  apply PerfectMatching.of_existsUnique (Finset.Subset.refl _)
  rintro ⟨a, v⟩
  obtain ⟨w, hw⟩ := (hp a).surjective v
  refine ⟨tupleEdge (fun b => p b w), ?_, ?_⟩
  · constructor
    · exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
    · simpa using hw.symm
  · intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he.1
    have huv : p a u = p a w := by
      have hv : v = p a u := (mem_tupleEdge (x := fun b => p b u)).mp he.2
      exact hv.symm.trans hw.symm
    have huw : u = w := (hp a).injective huv
    subst u
    rfl

 theorem coordinateMatching_uniform (p : A → W → W) :
    Uniform (coordinateMatching p) (Fintype.card A) := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
  simp

/-- The union of the coordinate matchings indexed by `I`. -/
def coordinateHypergraph {I : Type*} [Fintype I] (p : I → A → W → W) :
    Hypergraph (A × W) := Finset.univ.biUnion (fun i => coordinateMatching (p i))

 theorem coordinateHypergraph_uniform {I : Type*} [Fintype I] (p : I → A → W → W) :
    Uniform (coordinateHypergraph p) (Fintype.card A) := by
  intro e he
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  exact coordinateMatching_uniform (p i) e hei

/-- Every standard perfect matching of transversal edges admits bijective coordinate maps. -/
theorem perfectMatching_coordinates (a0 : A) {H M : Hypergraph (A × W)}
    (htrans : ∀ e ∈ H, ∃ x : A → W, e = tupleEdge x)
    (hM : PerfectMatching H M) :
    ∃ q : A → Equiv.Perm W, q a0 = Equiv.refl W ∧
      M = coordinateMatching (fun a w => q a w) := by
  classical
  have hrow : ∀ w : W, ∃ x : A → W, tupleEdge x ∈ M ∧ x a0 = w := by
    intro w
    obtain ⟨e, he, _⟩ := hM.existsUnique_edge (a0, w)
    obtain ⟨x, hx⟩ := htrans e (hM.subset he.1)
    subst e
    exact ⟨x, he.1, (mem_tupleEdge.mp he.2).symm⟩
  choose row hmem hfirst using hrow
  have heq : ∀ x y : A → W, tupleEdge x ∈ M → tupleEdge y ∈ M →
      ∀ a, x a = y a → x = y := by
    intro x y hx hy a ha
    obtain ⟨e, he, hu⟩ := hM.existsUnique_edge (a, x a)
    apply tupleEdge_injective
    exact (hu _ ⟨hx, by simp⟩).trans (hu _ ⟨hy, by simpa using ha⟩).symm
  have hbij : ∀ a : A, Function.Bijective (fun w => row w a) := by
    intro a
    constructor
    · intro w u hwu
      have hru : row w = row u := heq _ _ (hmem w) (hmem u) a hwu
      calc
        w = row w a0 := (hfirst w).symm
        _ = row u a0 := congrFun hru a0
        _ = u := hfirst u
    · intro v
      obtain ⟨e, he, _⟩ := hM.existsUnique_edge (a, v)
      obtain ⟨x, hx⟩ := htrans e (hM.subset he.1)
      subst e
      have hrx : row (x a0) = x := heq _ _ (hmem _) he.1 a0 (hfirst _)
      refine ⟨x a0, ?_⟩
      change row (x a0) a = v
      rw [hrx]
      exact (mem_tupleEdge.mp he.2).symm
  let q : A → Equiv.Perm W := fun a => Equiv.ofBijective (fun w => row w a) (hbij a)
  refine ⟨q, ?_, ?_⟩
  · ext w
    exact hfirst w
  · ext e
    constructor
    · intro he
      obtain ⟨x, hx⟩ := htrans e (hM.subset he)
      subst e
      have hrx : row (x a0) = x := heq _ _ (hmem _) he a0 (hfirst _)
      apply Finset.mem_image.mpr
      refine ⟨x a0, Finset.mem_univ _, ?_⟩
      change tupleEdge (row (x a0)) = tupleEdge x
      rw [hrx]
    · intro he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      exact hmem w

/-- Normalized coordinate presentations of the same matching coincide. -/
theorem coordinates_eq_of_matching_eq (a0 : A) (p q : A → Equiv.Perm W)
    (hp0 : p a0 = Equiv.refl W) (hq0 : q a0 = Equiv.refl W)
    (h : coordinateMatching (fun a w => p a w) =
      coordinateMatching (fun a w => q a w)) : p = q := by
  classical
  funext a
  apply Equiv.ext
  intro w
  have he : tupleEdge (fun b => p b w) ∈ coordinateMatching (fun b u => q b u) := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp he
  have htuples : (fun b => q b u) = (fun b => p b w) := tupleEdge_injective heu
  have huw : u = w := by
    have hh := congrFun htuples a0
    simpa only [hp0, hq0, Equiv.refl_apply] using hh
  subst u
  exact (congrFun htuples a).symm

/-- Coordinate rigidity implies rigidity in the standard finite-hypergraph sense. -/
def rigidFamily_of_coordinates {I : Type*} [Fintype I] (a0 : A)
    (p : I → A → Equiv.Perm W)
    (hp0 : ∀ i, p i a0 = Equiv.refl W)
    (hseparate : ∀ i j, i ≠ j → ∀ w, ∃ a, p i a w ≠ p j a w)
    (hcomplete : ∀ q : A → Equiv.Perm W, q a0 = Equiv.refl W →
      (∀ w, ∃ i, ∀ a, q a w = p i a w) → ∃ i, q = p i) :
    RigidFamily (coordinateHypergraph (fun i a w => p i a w)) I := by
  classical
  letI : Nonempty A := ⟨a0⟩
  refine {
    matching := fun i => coordinateMatching (fun a w => p i a w)
    perfect := ?_
    edge_disjoint := ?_
    covers := rfl
    complete := ?_ }
  · intro i
    apply (coordinateMatching_perfect (fun a w => p i a w) (fun a => (p i a).bijective)).mono
    intro e he
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hei
    obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hej
    have hcoords : (fun a => p i a w) = (fun a => p j a u) :=
      tupleEdge_injective (hew.trans heu.symm)
    have hwu : w = u := by
      have h := congrFun hcoords a0
      simpa only [hp0, Equiv.refl_apply] using h
    subst u
    obtain ⟨a, ha⟩ := hseparate i j hij w
    exact ha (congrFun hcoords a)
  · intro M hM
    have htrans : ∀ e ∈ coordinateHypergraph (fun i a w => p i a w),
        ∃ x : A → W, e = tupleEdge x := by
      intro e he
      obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
      obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hei
      exact ⟨fun a => p i a w, hew.symm⟩
    obtain ⟨q, hq0, hMq⟩ := perfectMatching_coordinates a0 htrans hM
    have hmixed : ∀ w, ∃ i, ∀ a, q a w = p i a w := by
      intro w
      have he : tupleEdge (fun a => q a w) ∈ M := by
        rw [hMq]
        exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
      obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp (hM.subset he)
      obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hei
      have hcoords : (fun a => p i a u) = (fun a => q a w) := tupleEdge_injective heu
      have huw : u = w := by
        have h := congrFun hcoords a0
        simpa only [hp0, hq0, Equiv.refl_apply] using h
      subst u
      exact ⟨i, fun a => (congrFun hcoords a).symm⟩
    obtain ⟨i, hi⟩ := hcomplete q hq0 hmixed
    exact ⟨i, by simpa only [hi] using hMq⟩

end Tuple

/-- Every hypergraph of transversal tuples has the canonical balanced multipartition. -/
theorem balancedPartite_of_transversal {r : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (H : Hypergraph (Fin r × W))
    (htrans : ∀ e ∈ H, ∃ x : Fin r → W, e = tupleEdge x) :
    BalancedPartite H r (Fintype.card W) := by
  classical
  refine ⟨Prod.fst, ?_, ?_⟩
  · intro i
    have hset : Finset.univ.filter (fun v : Fin r × W => v.1 = i) =
        Finset.univ.image (fun w : W => (i, w)) := by
      ext v
      rcases v with ⟨a, w⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        subst a
        exact ⟨w, rfl⟩
      · rintro ⟨u, h⟩
        exact (congrArg Prod.fst h).symm
    rw [hset, Finset.card_image_of_injective _ (fun u v h => congrArg Prod.snd h)]
    simp
  · intro e he i
    obtain ⟨x, rfl⟩ := htrans e he
    have hset : (tupleEdge x).filter (fun v => v.1 = i) = {(i, x i)} := by
      ext v
      rcases v with ⟨a, w⟩
      simp only [Finset.mem_filter, mem_tupleEdge, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨hw, rfl⟩
        exact ⟨rfl, hw⟩
      · rintro ⟨rfl, hw⟩
        exact ⟨hw, rfl⟩
    rw [hset]
    simp

 theorem coordinateHypergraph_balanced {r : ℕ} {W I : Type*}
    [Fintype W] [DecidableEq W] [Fintype I] (p : I → Fin r → W → W) :
    BalancedPartite (coordinateHypergraph p) r (Fintype.card W) := by
  apply balancedPartite_of_transversal
  intro e he
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hei
  exact ⟨fun a => p i a w, hew.symm⟩

/-- Canonical balanced multipartition for any finite index type of parts. -/
theorem balancedPartite_of_transversal_card {A W : Type*}
    [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
    (H : Hypergraph (A × W))
    (htrans : ∀ e ∈ H, ∃ x : A → W, e = tupleEdge x) :
    BalancedPartite H (Fintype.card A) (Fintype.card W) := by
  classical
  let c := Fintype.equivFin A
  refine ⟨fun v => c v.1, ?_, ?_⟩
  · intro i
    have hset : Finset.univ.filter (fun v : A × W => c v.1 = i) =
        Finset.univ.image (fun w : W => (c.symm i, w)) := by
      ext v
      rcases v with ⟨a, w⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        have ha : a = c.symm i := c.apply_eq_iff_eq_symm_apply.mp h
        subst a
        exact ⟨w, rfl⟩
      · rintro ⟨u, h⟩
        have ha : c.symm i = a := congrArg Prod.fst h
        rw [← ha]
        exact c.apply_symm_apply i
    rw [hset, Finset.card_image_of_injective _ (fun u v h => congrArg Prod.snd h)]
    simp
  · intro e he i
    obtain ⟨x, rfl⟩ := htrans e he
    have hset : (tupleEdge x).filter (fun v => c v.1 = i) =
        {(c.symm i, x (c.symm i))} := by
      ext v
      rcases v with ⟨a, w⟩
      simp only [Finset.mem_filter, mem_tupleEdge, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨hw, ha⟩
        have hai : a = c.symm i := c.apply_eq_iff_eq_symm_apply.mp ha
        subst a
        exact ⟨rfl, hw⟩
      · rintro ⟨rfl, hw⟩
        exact ⟨hw, c.apply_symm_apply i⟩
    rw [hset]
    simp

theorem coordinateHypergraph_balanced_card {A W I : Type*}
    [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W] [Fintype I]
    (p : I → A → W → W) :
    BalancedPartite (coordinateHypergraph p) (Fintype.card A) (Fintype.card W) := by
  apply balancedPartite_of_transversal_card
  intro e he
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hei
  exact ⟨fun a => p i a w, hew.symm⟩

end RigidGHZ
