module

public import RigidGHZ.Finite.TripartiteEquality
public import RigidGHZ.Relabel

@[expose] public section
namespace RigidGHZ.Finite

/-- A permutation of the three vertex parts, keeping their internal labels. -/
def permuteParts (e : Equiv.Perm (Fin 3)) :
    (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3) :=
  Equiv.prodCongr e (Equiv.refl _)

 theorem permuteParts_tupleEdge (e : Equiv.Perm (Fin 3)) (x : Fin 3 → Fin 3) :
    relabelEdge (permuteParts e) (tupleEdge x) = tupleEdge (fun t => x (e.symm t)) := by
  ext z
  rcases z with ⟨t,w⟩
  simp [permuteParts]

 theorem transversal_permuteParts {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (e : Equiv.Perm (Fin 3)) :
    ∀ f ∈ relabelHypergraph (permuteParts e) H,
      ∃ x : Fin 3 → Fin 3, f = tupleEdge x := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨x,rfl⟩ := htrans g hg
  exact ⟨_, permuteParts_tupleEdge e x⟩

 theorem extremal_second_codegree_two {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) (a c : Fin 3) :
    (Finset.univ.filter (fun b : Fin 3 => tupleEdge ![a,b,c] ∈ H)).card = 2 := by
  classical
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have ht := transversal_permuteParts htrans e
  have hr := hR.relabel (permuteParts e)
  have hc := extremal_first_codegree_two ht hr a c
  have he (b : Fin 3) : relabelEdge (permuteParts e) (tupleEdge ![a,b,c]) =
      tupleEdge ![b,a,c] := by
    rw [permuteParts_tupleEdge]
    congr 1
    funext t
    fin_cases t <;> simp [e, Equiv.swap_apply_def]
  have hf : (Finset.univ.filter (fun b : Fin 3 => tupleEdge ![b,a,c] ∈
      relabelHypergraph (permuteParts e) H)) =
      Finset.univ.filter (fun b : Fin 3 => tupleEdge ![a,b,c] ∈ H) := by
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, ← he]
    simp
  rw [hf] at hc
  exact hc

 theorem extremal_third_codegree_two {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) (a b : Fin 3) :
    (Finset.univ.filter (fun c : Fin 3 => tupleEdge ![a,b,c] ∈ H)).card = 2 := by
  classical
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have ht := transversal_permuteParts htrans e
  have hr := hR.relabel (permuteParts e)
  have hc := extremal_first_codegree_two ht hr b a
  have he (c : Fin 3) : relabelEdge (permuteParts e) (tupleEdge ![a,b,c]) =
      tupleEdge ![c,b,a] := by
    rw [permuteParts_tupleEdge]
    congr 1
    funext t
    fin_cases t <;> simp [e, Equiv.swap_apply_def]
  have hf : (Finset.univ.filter (fun c : Fin 3 => tupleEdge ![c,b,a] ∈
      relabelHypergraph (permuteParts e) H)) =
      Finset.univ.filter (fun c : Fin 3 => tupleEdge ![a,b,c] ∈ H) := by
    ext c
    rw [Finset.mem_filter, Finset.mem_filter, ← he]
    simp
  rw [hf] at hc
  exact hc

/-- A two-element subset of a three-element type omits a unique element. -/
theorem existsUnique_missing_of_two (P : Fin 3 → Prop) [DecidablePred P]
    (h : (Finset.univ.filter P).card = 2) : ∃! a, ¬ P a := by
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  have hn : (Finset.univ.filter (fun a => ¬ P a)).card = 1 := by
    rw [h] at hc
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hn
  refine ⟨a, ?_, ?_⟩
  · have hh : a ∈ Finset.univ.filter (fun a => ¬ P a) := by rw [ha]; simp
    exact (Finset.mem_filter.mp hh).2
  · intro b hb
    have hh : b ∈ Finset.univ.filter (fun a => ¬ P a) := by simp [hb]
    rw [ha] at hh
    exact Finset.mem_singleton.mp hh

/- There are only six permutations of three symbols. The certificate checks
three permutation rows (216 possibilities) and their column injectivity. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
 theorem latin_three_normalization :
    ∀ L : Fin 3 → Equiv.Perm (Fin 3),
      (∀ c, Function.Injective (fun b => L b c)) →
      ∃ row sym : Equiv.Perm (Fin 3), ∀ b c, sym (L (row b) c) = b + c := by
  decide

/-- The missing triples of an extremal graph form a Latin square. -/
theorem extremal_missing_latin {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) :
    ∃ L : Fin 3 → Equiv.Perm (Fin 3),
      (∀ c, Function.Injective (fun b => L b c)) ∧
      ∀ a b c, tupleEdge ![a,b,c] ∉ H ↔ a = L b c := by
  classical
  have hfirst : ∀ b c : Fin 3, ∃! a, tupleEdge ![a,b,c] ∉ H := by
    intro b c
    exact existsUnique_missing_of_two _ (extremal_first_codegree_two htrans hR b c)
  choose l hl using fun b c => (hfirst b c).exists
  have hiff : ∀ a b c, tupleEdge ![a,b,c] ∉ H ↔ a = l b c := by
    intro a b c
    constructor
    · intro ha
      exact (hfirst b c).unique ha (hl b c)
    · intro ha
      simpa only [ha] using hl b c
  have hrows : ∀ b, Function.Injective (l b) := by
    intro b c c' hcc
    have hu := existsUnique_missing_of_two _ (extremal_third_codegree_two htrans hR (l b c) b)
    apply hu.unique (hl b c)
    exact (hiff _ _ _).mpr hcc
  let L : Fin 3 → Equiv.Perm (Fin 3) := fun b =>
    Equiv.ofBijective (l b) ((Finite.injective_iff_bijective).mp (hrows b))
  refine ⟨L, ?_, ?_⟩
  · intro c b b' hbb
    have hu := existsUnique_missing_of_two _ (extremal_second_codegree_two htrans hR (l b c) c)
    apply hu.unique (hl b c)
    exact (hiff _ _ _).mpr hbb
  · exact hiff

/-- Every extremal graph has the same normal form after relabeling vertices
within its parts. The third part can even be kept pointwise fixed. -/
theorem tripartite_three_unique_normal_form {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) :
    ∃ row sym : Equiv.Perm (Fin 3), ∀ a b c,
      tupleEdge ![sym.symm a,row b,c] ∈ H ↔ a ≠ b + c := by
  obtain ⟨L,hcol,hL⟩ := extremal_missing_latin htrans hR
  obtain ⟨row,sym,hnorm⟩ := latin_three_normalization L hcol
  refine ⟨row,sym,?_⟩
  intro a b c
  have hn : tupleEdge ![sym.symm a,row b,c] ∉ H ↔ a = b + c := by
    rw [hL]
    constructor
    · intro h
      have hh := congrArg sym h
      simpa only [Equiv.apply_symm_apply, hnorm] using hh
    · intro h
      apply sym.injective
      simpa only [Equiv.apply_symm_apply, hnorm] using h
  simpa only [not_not] using not_congr hn

/-- Relabel vertices independently inside each of the three parts. -/
def withinParts (p : Fin 3 → Equiv.Perm (Fin 3)) :
    (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3) where
  toFun v := (v.1, p v.1 v.2)
  invFun v := (v.1, (p v.1).symm v.2)
  left_inv := by rintro ⟨t,w⟩; simp
  right_inv := by rintro ⟨t,w⟩; simp

 theorem withinParts_tupleEdge (p : Fin 3 → Equiv.Perm (Fin 3)) (x : Fin 3 → Fin 3) :
    relabelEdge (withinParts p) (tupleEdge x) = tupleEdge (fun t => p t (x t)) := by
  ext z
  rcases z with ⟨t,w⟩
  simp only [mem_relabelEdge, withinParts, Equiv.coe_fn_symm_mk, mem_tupleEdge]
  constructor
  · intro h
    have hh := congrArg (p t) h
    simpa only [Equiv.apply_symm_apply] using hh
  · intro h
    simpa only [h, Equiv.symm_apply_apply]

/-- The common normal form: all transversal triples except `a = b + c` in `Fin 3`. -/
def latinComplementGraph : Hypergraph (Fin 3 × Fin 3) :=
  ((Finset.univ : Finset (Fin 3 → Fin 3)).filter (fun x => x 0 ≠ x 1 + x 2)).image tupleEdge

 theorem mem_latinComplementGraph (x : Fin 3 → Fin 3) :
    tupleEdge x ∈ latinComplementGraph ↔ x 0 ≠ x 1 + x 2 := by
  simp only [latinComplementGraph, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y,hy,hxy⟩
    simpa only [tupleEdge_injective hxy] using hy
  · exact fun hx => ⟨x,hx,rfl⟩

 theorem latinComplementGraph_card : latinComplementGraph.card = 18 := by decide

/-- The extremal tripartite hypergraph is unique up to a genuine vertex
isomorphism preserving each of the three parts. -/
theorem tripartite_three_unique {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) :
    ∃ f : (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3),
      (∀ v, (f v).1 = v.1) ∧ relabelHypergraph f H = latinComplementGraph := by
  classical
  obtain ⟨row,sym,hnorm⟩ := tripartite_three_unique_normal_form htrans hR
  let p : Fin 3 → Equiv.Perm (Fin 3) := ![sym,row.symm,Equiv.refl _]
  refine ⟨withinParts p, fun _ => rfl, ?_⟩
  have hsub : relabelHypergraph (withinParts p) H ⊆ latinComplementGraph := by
    intro e he
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨x,rfl⟩ := htrans g hg
    rw [withinParts_tupleEdge, mem_latinComplementGraph]
    have hx : tupleEdge ![sym.symm (sym (x 0)),row (row.symm (x 1)),x 2] ∈ H := by
      have heq : ![sym.symm (sym (x 0)),row (row.symm (x 1)),x 2] = x := by
        funext t
        fin_cases t <;> simp
      simpa only [heq] using hg
    simpa [p] using (hnorm (sym (x 0)) (row.symm (x 1)) (x 2)).mp hx
  have hu : Uniform H 3 := by
    intro e he
    obtain ⟨x,rfl⟩ := htrans e he
    exact tupleEdge_card x
  obtain ⟨F⟩ := hR
  have hcard : H.card = 18 := F.card_edges (m := 3) hu (by decide) (by decide)
  have hrCard : (relabelHypergraph (withinParts p) H).card = 18 := by
    rw [relabelHypergraph, Finset.card_image_of_injective _ (relabelEdge_injective _)]
    exact hcard
  apply Finset.eq_of_subset_of_card_le hsub
  rw [latinComplementGraph_card, hrCard]

end RigidGHZ.Finite
