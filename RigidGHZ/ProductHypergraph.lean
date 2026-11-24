module

public import RigidGHZ.Product
public import RigidGHZ.Partite

/-!
# Supported products as ordinary finite hypergraphs

The row and permutation parts use the first two coordinates; each factor has
one additional tag coordinate. All assertions use the standard finite-set
perfect-matching definition, by the coordinate equivalence theorem.
-/

@[expose] public section

namespace RigidGHZ.Product

universe u v w

variable {W : Type u} {F : Type v} {I : F → Type w}
  [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
  [∀ f, Fintype (I f)]

/-- The first coordinate is `none`, the second `some none`, and each factor
has a tag coordinate `some (some f)`. -/
abbrev ProductParts (F : Type v) := Option (Option F)

noncomputable def productCoordinates
    (U : F → Finset W) (p c : ∀ f, I f → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x)
    (i : ∀ f, I f) : ProductParts F → Equiv.Perm W
  | none => Equiv.refl W
  | some none => assemble U (fun f => p f (i f)) hdisj (fun f => hfix f (i f))
  | some (some f) => c f (i f)

noncomputable def productHypergraph
    (U : F → Finset W) (p c : ∀ f, I f → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x) :
    Hypergraph (ProductParts F × W) := by
  classical
  exact coordinateHypergraph
    (fun i a x => productCoordinates U p c hdisj hfix i a x)

/-- Theorem 3.4 after the factor supports have been placed disjointly, expressed
using coordinate presentations of the tripartite factors. -/
noncomputable def supportedProductRigidFamily
    (U : F → Finset W) (p c : ∀ f, I f → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x)
    (hrigid : FactorRigid p c)
    (hsep : ∀ f (i j : I f) x, p f i x = p f j x → c f i x = c f j x → i = j) :
    RigidFamily (productHypergraph U p c hdisj hfix) (∀ f, I f) := by
  classical
  apply rigidFamily_of_coordinates (none : ProductParts F)
    (productCoordinates U p c hdisj hfix)
  · intro i
    rfl
  · intro i j hij x
    by_contra hn
    push_neg at hn
    apply hij
    apply support_product_edge_disjoint U p c hdisj hfix hsep i j x
    · exact hn (some none)
    · intro f
      exact hn (some (some f))
  · intro q hq0 hsupported
    have hlocal : ∀ x, ∃ i : ∀ f, I f,
        q (some none) x = assembleMap U (fun f => p f (i f)) x ∧
        ∀ f, q (some (some f)) x = c f (i f) x := by
      intro x
      obtain ⟨i, hi⟩ := hsupported x
      exact ⟨i, hi (some none), fun f => hi (some (some f))⟩
    obtain ⟨i, hi, hc⟩ := support_product_purity U p c hdisj hfix hrigid
      (q (some none)) (fun f => q (some (some f))) hlocal
    refine ⟨i, ?_⟩
    funext a
    cases a with
    | none => exact hq0
    | some a =>
      cases a with
      | none =>
        apply Equiv.ext
        exact hi
      | some f => exact hc f

theorem productHypergraph_uniform
    (U : F → Finset W) (p c : ∀ f, I f → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x) :
    Uniform (productHypergraph U p c hdisj hfix) (Fintype.card F + 2) := by
  classical
  have h := coordinateHypergraph_uniform
    (fun i a x => productCoordinates U p c hdisj hfix i a x)
  simpa only [productHypergraph, ProductParts, Fintype.card_option, Nat.add_assoc] using h

theorem productHypergraph_rigid
    (U : F → Finset W) (p c : ∀ f, I f → Equiv.Perm W)
    (hdisj : Pairwise (fun f g => Disjoint (U f) (U g)))
    (hfix : ∀ f i x, x ∉ U f → p f i x = x)
    (hrigid : FactorRigid p c)
    (hsep : ∀ f (i j : I f) x, p f i x = p f j x → c f i x = c f j x → i = j) :
    IsRigid (productHypergraph U p c hdisj hfix) (∏ f, Fintype.card (I f)) := by
  classical
  have hcard : Fintype.card (∀ f, I f) = ∏ f, Fintype.card (I f) := Fintype.card_pi
  have e : (∀ f, I f) ≃ Fin (∏ f, Fintype.card (I f)) :=
    (Fintype.equivFin (∀ f, I f)).trans (finCongr hcard)
  exact ⟨(supportedProductRigidFamily U p c hdisj hfix hrigid hsep).reindex e.symm⟩

end RigidGHZ.Product
