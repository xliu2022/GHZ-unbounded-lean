module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Basic

/-!
# The common-two-parts product in permutation coordinates

The two main coordinate claims are complete proofs: disjoint supported
permutations can be assembled into one permutation, and every perfect matching
in their product has one fixed matching index in each factor. The translation
to finite-set hypergraphs is supplied separately.
-/

@[expose] public section

namespace RigidGHZ.Product

universe u v w z

variable {W : Type u} {F : Type v} [Fintype W] [DecidableEq W]

theorem perm_mem_iff_of_fixes_complement (p : Equiv.Perm W) (U : Finset W)
    (hfix : ∀ x, x ∉ U → p x = x) (x : W) : p x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    by_contra hn
    exact hn (by simpa only [hfix x hn] using hx)
  · intro hx
    by_contra hn
    have h : p (p x) = p x := hfix (p x) hn
    have he : p x = x := p.injective h
    apply hn
    simpa only [he] using hx

noncomputable def assembleMap (U : F → Finset W) (p : F → Equiv.Perm W)
    (x : W) : W := by
  classical
  exact if h : ∃ f, x ∈ U f then p h.choose x else x

theorem support_index_unique (U : F → Finset W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    {f g : F} {x : W} (hf : x ∈ U f) (hg : x ∈ U g) : f = g := by
  by_contra hfg
  exact Finset.disjoint_left.mp (hdisj hfg) hf hg

theorem assembleMap_of_mem (U : F → Finset W) (p : F → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    {f : F} {x : W} (hx : x ∈ U f) : assembleMap U p x = p f x := by
  classical
  have h : ∃ f, x ∈ U f := ⟨f, hx⟩
  simp only [assembleMap, dif_pos h]
  have he : h.choose = f := support_index_unique U hdisj h.choose_spec hx
  rw [he]

theorem assembleMap_of_not_mem (U : F → Finset W) (p : F → Equiv.Perm W)
    {x : W} (hx : ∀ f, x ∉ U f) : assembleMap U p x = x := by
  classical
  simp only [assembleMap]
  split
  · rename_i h
    obtain ⟨f, hf⟩ := h
    exact False.elim (hx f hf)
  · rfl

theorem assembleMap_mem_iff (U : F → Finset W) (p : F → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f x, x ∉ U f → p f x = x) (f : F) (x : W) :
    assembleMap U p x ∈ U f ↔ x ∈ U f := by
  classical
  by_cases hx : x ∈ U f
  · rw [assembleMap_of_mem U p hdisj hx]
    exact perm_mem_iff_of_fixes_complement (p f) (U f) (hfix f) x
  · by_cases ha : ∃ g, x ∈ U g
    · obtain ⟨g, hg⟩ := ha
      rw [assembleMap_of_mem U p hdisj hg]
      have hpg : p g x ∈ U g :=
        (perm_mem_iff_of_fixes_complement (p g) (U g) (hfix g) x).2 hg
      have hgf : g ≠ f := by intro he; exact hx (he ▸ hg)
      have hpf : p g x ∉ U f := by
        intro hh
        exact Finset.disjoint_left.mp (hdisj hgf) hpg hh
      simp [hx, hpf]
    · have hn : ∀ g, x ∉ U g := by simpa only [not_exists] using ha
      rw [assembleMap_of_not_mem U p hn]

theorem assembleMap_injective (U : F → Finset W) (p : F → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f x, x ∉ U f → p f x = x) : Function.Injective (assembleMap U p) := by
  classical
  intro x y hxy
  by_cases ha : ∃ f, x ∈ U f
  · obtain ⟨f, hf⟩ := ha
    have hy : y ∈ U f := by
      apply (assembleMap_mem_iff U p hdisj hfix f y).1
      rw [← hxy]
      exact (assembleMap_mem_iff U p hdisj hfix f x).2 hf
    rw [assembleMap_of_mem U p hdisj hf, assembleMap_of_mem U p hdisj hy] at hxy
    exact (p f).injective hxy
  · have hx : ∀ f, x ∉ U f := by simpa only [not_exists] using ha
    have hy : ∀ f, y ∉ U f := by
      intro f hf
      have hh := (assembleMap_mem_iff U p hdisj hfix f y).2 hf
      rw [← hxy] at hh
      exact hx f ((assembleMap_mem_iff U p hdisj hfix f x).1 hh)
    simpa only [assembleMap_of_not_mem U p hx, assembleMap_of_not_mem U p hy] using hxy

noncomputable def assemble (U : F → Finset W) (p : F → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f x, x ∉ U f → p f x = x) : Equiv.Perm W :=
  Equiv.ofBijective (assembleMap U p)
    (assembleMap_injective U p hdisj hfix).bijective_of_finite

@[simp] theorem assemble_apply (U : F → Finset W) (p : F → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f x, x ∉ U f → p f x = x) (x : W) :
    assemble U p hdisj hfix x = assembleMap U p x := rfl

noncomputable def restrictPermutation (q : Equiv.Perm W) (U : Finset W)
    (hq : ∀ x, q x ∈ U ↔ x ∈ U) : Equiv.Perm W where
  toFun x := if x ∈ U then q x else x
  invFun x := if x ∈ U then q.symm x else x
  left_inv x := by
    by_cases hx : x ∈ U
    · simp [hx, (hq x).2 hx]
    · simp [hx]
  right_inv x := by
    by_cases hx : x ∈ U
    · have hs : q.symm x ∈ U := (hq (q.symm x)).1 (by simpa using hx)
      simp [hx, hs]
    · simp [hx]

@[simp] theorem restrictPermutation_apply (q : Equiv.Perm W) (U : Finset W)
    (hq : ∀ x, q x ∈ U ↔ x ∈ U) (x : W) :
    restrictPermutation q U hq x = if x ∈ U then q x else x := rfl

variable {I : F → Type w} {C : F → Type z}

/-- Coordinate form of the rigidity hypothesis for one tripartite factor. -/
def FactorRigid (p : ∀ f, I f → Equiv.Perm W)
    (c : ∀ f, I f → W ≃ C f) : Prop :=
  ∀ f (q : Equiv.Perm W) (t : W ≃ C f),
    (∀ x, ∃ i, q x = p f i x ∧ t x = c f i x) →
    ∃ i, q = p f i ∧ t = c f i

/-- A matching in the product must select a single index in every factor.
The candidate matching is represented by its second-coordinate permutation
and its bijection into each tag part. -/
theorem support_product_purity
    (U : F → Finset W) (p : ∀ f, I f → Equiv.Perm W)
    (c : ∀ f, I f → W ≃ C f)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x)
    (hrigid : FactorRigid p c)
    (q : Equiv.Perm W) (t : ∀ f, W ≃ C f)
    (hlocal : ∀ x, ∃ i : ∀ f, I f,
      q x = assembleMap U (fun f => p f (i f)) x ∧
      ∀ f, t f x = c f (i f) x) :
    ∃ i : ∀ f, I f,
      (∀ x, q x = assembleMap U (fun f => p f (i f)) x) ∧
      ∀ f, t f = c f (i f) := by
  classical
  have hq : ∀ f x, q x ∈ U f ↔ x ∈ U f := by
    intro f x
    obtain ⟨i, hi, _⟩ := hlocal x
    rw [hi]
    exact assembleMap_mem_iff U (fun f => p f (i f)) hdisj
      (fun f => hfix f (i f)) f x
  have hfactor : ∀ f, ∃ i, restrictPermutation q (U f) (hq f) = p f i ∧
      t f = c f i := by
    intro f
    apply hrigid f
    intro x
    obtain ⟨i, hi, htag⟩ := hlocal x
    refine ⟨i f, ?_, htag f⟩
    by_cases hx : x ∈ U f
    · simp only [restrictPermutation_apply, if_pos hx]
      rw [hi, assembleMap_of_mem U (fun f => p f (i f)) hdisj hx]
    · simp only [restrictPermutation_apply, if_neg hx, hfix f (i f) x hx]
  choose i hi using hfactor
  refine ⟨i, ?_, fun f => (hi f).2⟩
  intro x
  by_cases ha : ∃ f, x ∈ U f
  · obtain ⟨f, hf⟩ := ha
    rw [assembleMap_of_mem U (fun f => p f (i f)) hdisj hf]
    have he := congrArg (fun e : Equiv.Perm W => e x) (hi f).1
    simpa only [restrictPermutation_apply, if_pos hf] using he
  · have hn : ∀ f, x ∉ U f := by simpa only [not_exists] using ha
    obtain ⟨j, hj, _⟩ := hlocal x
    rw [hj, assembleMap_of_not_mem U (fun f => p f (j f)) hn,
      assembleMap_of_not_mem U (fun f => p f (i f)) hn]

/-- Pointwise edge disjointness is preserved by the supported product. -/
theorem support_product_edge_disjoint
    (U : F → Finset W) (p : ∀ f, I f → Equiv.Perm W)
    (c : ∀ f, I f → W ≃ C f)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x)
    (hsep : ∀ f (i j : I f) x, p f i x = p f j x → c f i x = c f j x → i = j)
    (i j : ∀ f, I f) (x : W)
    (hp : assembleMap U (fun f => p f (i f)) x =
      assembleMap U (fun f => p f (j f)) x)
    (hc : ∀ f, c f (i f) x = c f (j f) x) : i = j := by
  classical
  funext f
  apply hsep f (i f) (j f) x _ (hc f)
  by_cases hx : x ∈ U f
  · simpa only [assembleMap_of_mem U (fun f => p f (i f)) hdisj hx,
      assembleMap_of_mem U (fun f => p f (j f)) hdisj hx] using hp
  · rw [hfix f (i f) x hx, hfix f (j f) x hx]

end RigidGHZ.Product
