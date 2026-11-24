module

public import RigidGHZ.Partite
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace RigidGHZ

/-- Finite supports with total size at most the ambient size can be placed disjointly
by independently relabeling their common ambient finite set. -/
theorem pack_supports {F W : Type*} [Fintype F] [Fintype W] [DecidableEq W]
    (U : F → Finset W) (hbound : (∑ f, (U f).card) ≤ Fintype.card W) :
    ∃ e : F → Equiv.Perm W,
      Pairwise (fun f g => Disjoint ((U f).image (e f)) ((U g).image (e g))) := by
  classical
  let Tagged := Σ f : F, ↥(U f)
  have hcard : Fintype.card Tagged ≤ Fintype.card W := by
    simpa [Tagged] using hbound
  obtain ⟨g⟩ : Nonempty (Tagged ↪ W) := Function.Embedding.nonempty_of_card_le hcard
  have hext : ∀ f : F, ∃ e : Equiv.Perm W,
      ∀ x : U f, e (x : W) = g ⟨f, x⟩ := by
    intro f
    apply Equiv.Perm.exists_extending_pair
      (fun x : U f => (x : W)) (fun x : U f => g ⟨f, x⟩) Subtype.val_injective
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun t : Tagged => (t.2 : W)) (g.injective hxy)
  choose e he using hext
  refine ⟨e, ?_⟩
  intro f h hfh
  apply Finset.disjoint_left.mpr
  intro z hzF hzH
  obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hzF
  obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hzH
  have hxy : g ⟨f, ⟨x, hx⟩⟩ = g ⟨h, ⟨y, hy⟩⟩ := by
    rw [← he f ⟨x, hx⟩, ← he h ⟨y, hy⟩]
    exact hxz.trans hyz.symm
  exact hfh (congrArg Sigma.fst (g.injective hxy))

end RigidGHZ
