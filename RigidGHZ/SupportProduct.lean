module

public import RigidGHZ.ProductHypergraph
public import RigidGHZ.SupportPacking

/-!
# The support product from ordinary rigid tripartite factors

This file recovers permutation coordinates from the ordinary perfect matchings,
places the active supports disjointly, and invokes the supported product.
-/

@[expose] public section

namespace RigidGHZ

variable {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]

/-- Recover the full coordinate rigidity and separation conditions from an ordinary
rigid family of tripartite hypergraphs. -/
theorem factor_coordinates {H : Hypergraph (Fin 3 × W)} (R : RigidFamily H I)
    (U : Finset W)
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x)
    (hsupport : ∀ x : Fin 3 → W, tupleEdge x ∈ H → x 0 ∉ U → x 1 = x 0) :
    ∃ p c : I → Equiv.Perm W,
      (∀ i x, x ∉ U → p i x = x) ∧
      (∀ q t : Equiv.Perm W, (∀ x, ∃ i, q x = p i x ∧ t x = c i x) →
        ∃ i, q = p i ∧ t = c i) ∧
      (∀ i j x, p i x = p j x → c i x = c j x → i = j) := by
  classical
  have hcoords : ∀ i : I, ∃ a : Fin 3 → Equiv.Perm W,
      a 0 = Equiv.refl W ∧ R.matching i = coordinateMatching (fun b w => a b w) := by
    intro i
    exact perfectMatching_coordinates 0 htrans (R.perfect i)
  choose a ha0 haM using hcoords
  let p : I → Equiv.Perm W := fun i => a i 1
  let c : I → Equiv.Perm W := fun i => a i 2
  have hrow : ∀ i w, tupleEdge (fun b => a i b w) ∈ R.matching i := by
    intro i w
    rw [haM i]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  refine ⟨p, c, ?_, ?_, ?_⟩
  · intro i x hx
    have he := hsupport (fun b => a i b x) ((R.perfect i).subset (hrow i x))
    have hzero : a i 0 x = x := by rw [ha0 i]; rfl
    simpa only [hzero] using he (by simpa only [hzero] using hx)
  · intro q t hlocal
    let b : Fin 3 → Equiv.Perm W := ![Equiv.refl W, q, t]
    have hb0 : b 0 = Equiv.refl W := rfl
    have hM : PerfectMatching H (coordinateMatching (fun j w => b j w)) := by
      apply (coordinateMatching_perfect (fun j w => b j w) (fun j => (b j).bijective)).mono
      intro e he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨i, hq, ht⟩ := hlocal w
      have heq : (fun j => b j w) = (fun j => a i j w) := by
        funext j
        fin_cases j
        · change w = a i 0 w
          rw [ha0 i]
          rfl
        · exact hq
        · exact ht
      rw [heq]
      exact (R.perfect i).subset (hrow i w)
    obtain ⟨i, hi⟩ := R.complete _ hM
    have heq : b = a i := coordinates_eq_of_matching_eq 0 b (a i) hb0 (ha0 i)
      (hi.trans (haM i))
    exact ⟨i, congrFun heq 1, congrFun heq 2⟩
  · intro i j x hp hc
    apply R.eq_of_shared_edge (hrow i x)
    have heq : (fun b => a i b x) = (fun b => a j b x) := by
      funext b
      fin_cases b
      · change a i 0 x = a j 0 x
        rw [ha0 i, ha0 j]
      · exact hp
      · exact hc
    rw [heq]
    exact hrow j x

/-- Relabeling the first two parts conjugates the projection permutation; the tag
part retains its labels and its bijection is precomposed by the inverse relabeling. -/
def relabelProjection (e p : Equiv.Perm W) : Equiv.Perm W := e.symm.trans (p.trans e)

def relabelTag (e c : Equiv.Perm W) : Equiv.Perm W := e.symm.trans c

@[simp] theorem relabelProjection_apply (e p : Equiv.Perm W) (x : W) :
    relabelProjection e p x = e (p (e.symm x)) := rfl

@[simp] theorem relabelTag_apply (e c : Equiv.Perm W) (x : W) :
    relabelTag e c x = c (e.symm x) := rfl

 theorem relabelProjection_fixes (e p : Equiv.Perm W) (U : Finset W)
    (hfix : ∀ x, x ∉ U → p x = x) :
    ∀ x, x ∉ U.image e → relabelProjection e p x = x := by
  intro x hx
  have hn : e.symm x ∉ U := by
    intro h
    exact hx (Finset.mem_image.mpr ⟨e.symm x, h, e.apply_symm_apply x⟩)
  simp [hfix _ hn]

 theorem relabel_factor_purity (e : Equiv.Perm W) (p c : I → Equiv.Perm W)
    (hrigid : ∀ q t : Equiv.Perm W, (∀ x, ∃ i, q x = p i x ∧ t x = c i x) →
      ∃ i, q = p i ∧ t = c i) :
    ∀ q t : Equiv.Perm W,
      (∀ x, ∃ i, q x = relabelProjection e (p i) x ∧ t x = relabelTag e (c i) x) →
      ∃ i, q = relabelProjection e (p i) ∧ t = relabelTag e (c i) := by
  intro q t hlocal
  let q' : Equiv.Perm W := e.trans (q.trans e.symm)
  let t' : Equiv.Perm W := e.trans t
  have hold : ∀ x, ∃ i, q' x = p i x ∧ t' x = c i x := by
    intro x
    obtain ⟨i, hq, ht⟩ := hlocal (e x)
    refine ⟨i, ?_, ?_⟩
    · change e.symm (q (e x)) = p i x
      rw [hq]
      simp
    · change t (e x) = c i x
      simpa using ht
  obtain ⟨i, hq, ht⟩ := hrigid q' t' hold
  refine ⟨i, ?_, ?_⟩
  · apply Equiv.ext
    intro x
    have h := congrArg (fun z : Equiv.Perm W => e (z (e.symm x))) hq
    simpa [q'] using h
  · apply Equiv.ext
    intro x
    have h := congrArg (fun z : Equiv.Perm W => z (e.symm x)) ht
    simpa [t'] using h

 theorem relabel_factor_separation (e : Equiv.Perm W) (p c : I → Equiv.Perm W)
    (hsep : ∀ i j x, p i x = p j x → c i x = c j x → i = j) :
    ∀ i j x, relabelProjection e (p i) x = relabelProjection e (p j) x →
      relabelTag e (c i) x = relabelTag e (c j) x → i = j := by
  intro i j x hp hc
  exact hsep i j (e.symm x) (e.injective hp) hc

/-- Theorem 3.4 for ordinary simple tripartite factors, after identifying their equally
sized parts with the same finite set. The hypothesis is the paper's active-support
condition on actual edges, not an unproved coordinate-rigidity interface. -/
theorem support_product {F : Type*} [Fintype F] [DecidableEq F]
    {J : F → Type*} [∀ f, Fintype (J f)]
    (H : F → Hypergraph (Fin 3 × W)) (R : ∀ f, RigidFamily (H f) (J f))
    (U : F → Finset W)
    (hbound : (∑ f, (U f).card) ≤ Fintype.card W)
    (htrans : ∀ f e, e ∈ H f → ∃ x : Fin 3 → W, e = tupleEdge x)
    (hsupport : ∀ f (x : Fin 3 → W), tupleEdge x ∈ H f →
      (x 0 ∈ U f ∧ x 1 ∈ U f) ∨ (x 0 = x 1 ∧ x 0 ∉ U f)) :
    ∃ G : Hypergraph (Product.ProductParts F × W),
      Uniform G (Fintype.card F + 2) ∧
      BalancedPartite G (Fintype.card F + 2) (Fintype.card W) ∧
      IsRigid G (∏ f, Fintype.card (J f)) := by
  classical
  have hfactors : ∀ f, ∃ p c : J f → Equiv.Perm W,
      (∀ i x, x ∉ U f → p i x = x) ∧
      (∀ q t : Equiv.Perm W, (∀ x, ∃ i, q x = p i x ∧ t x = c i x) →
        ∃ i, q = p i ∧ t = c i) ∧
      (∀ i j x, p i x = p j x → c i x = c j x → i = j) := by
    intro f
    apply factor_coordinates (R f) (U f) (htrans f)
    intro x he hx
    rcases hsupport f x he with h | h
    · exact False.elim (hx h.1)
    · exact h.1.symm
  choose p c hfix hrigid hsep using hfactors
  obtain ⟨e, hdisj⟩ := pack_supports U hbound
  let U' : F → Finset W := fun f => (U f).image (e f)
  let p' : ∀ f, J f → Equiv.Perm W := fun f i => relabelProjection (e f) (p f i)
  let c' : ∀ f, J f → Equiv.Perm W := fun f i => relabelTag (e f) (c f i)
  have hfix' : ∀ f i x, x ∉ U' f → p' f i x = x := by
    intro f i
    exact relabelProjection_fixes (e f) (p f i) (U f) (hfix f i)
  have hrigid' : Product.FactorRigid p' c' := by
    intro f
    exact relabel_factor_purity (e f) (p f) (c f) (hrigid f)
  have hsep' : ∀ f (i j : J f) x,
      p' f i x = p' f j x → c' f i x = c' f j x → i = j := by
    intro f
    exact relabel_factor_separation (e f) (p f) (c f) (hsep f)
  let G := Product.productHypergraph U' p' c' hdisj hfix'
  refine ⟨G, Product.productHypergraph_uniform U' p' c' hdisj hfix', ?_,
    Product.productHypergraph_rigid U' p' c' hdisj hfix' hrigid' hsep'⟩
  have hb := coordinateHypergraph_balanced_card
    (fun i a w => Product.productCoordinates U' p' c' hdisj hfix' i a w)
  simpa only [G, Product.productHypergraph, Product.ProductParts,
    Fintype.card_option, Nat.add_assoc] using hb

end RigidGHZ
