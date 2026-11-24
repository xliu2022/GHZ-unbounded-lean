module

public import RigidGHZ.Basic

/-! Proper edge colorings of rigid hypergraphs. A proper coloring with exactly
the regular degree many colors has perfect-matching color classes; rigidity
then identifies the coloring uniquely up to a permutation of colors. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.EdgeColoring

variable {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
  {H : Hypergraph V}

/-- Edges with the same color are vertex-disjoint unless they are identical. -/
def Proper (color : H → I) : Prop :=
  ∀ e f : H, color e = color f → e ≠ f → Disjoint e.val f.val

def colorClass (color : H → I) (i : I) : Hypergraph V :=
  (Finset.univ.filter (fun e : H => color e = i)).image Subtype.val

theorem colorClass_subset (color : H → I) (i : I) : colorClass color i ⊆ H := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  exact f.property

theorem mem_colorClass (color : H → I) (i : I) (e : H) :
    e.val ∈ colorClass color i ↔ color e = i := by
  constructor
  · intro he
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp he
    have hfe : f = e := Subtype.ext heq
    subst f
    exact (Finset.mem_filter.mp hf).2
  · intro he
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

theorem Proper.eq_of_common {color : H → I} (hP : Proper color)
    {e f : H} (hc : color e = color f) {v : V} (hve : v ∈ e.val) (hvf : v ∈ f.val) :
    e = f := by
  by_contra hef
  exact Finset.disjoint_left.mp (hP e f hc hef) hve hvf

/-- Saturation of the available colors at each vertex makes every color class
a genuine ordinary perfect matching. No completeness assumption is used here. -/
theorem regular_colorClass_perfect (color : H → I) (hP : Proper color)
    (hreg : ∀ v : V, degree H v = Fintype.card I) (i : I) :
    PerfectMatching H (colorClass color i) := by
  classical
  apply PerfectMatching.of_existsUnique (colorClass_subset color i)
  intro v
  let S := H.filter (fun e => v ∈ e)
  let g : S → I := fun e => color ⟨e.val, (Finset.mem_filter.mp e.property).1⟩
  have hinj : Function.Injective g := by
    intro e f hef
    apply Subtype.ext
    exact congrArg (fun x : H => x.val) (hP.eq_of_common hef
      (Finset.mem_filter.mp e.property).2 (Finset.mem_filter.mp f.property).2)
  have hcard : Fintype.card S = Fintype.card I := by
    simpa only [Fintype.card_coe, S, degree] using hreg v
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj, hcard⟩
  obtain ⟨e, hei⟩ := hbij.2 i
  let eH : H := ⟨e.val, (Finset.mem_filter.mp e.property).1⟩
  have hcolor : color eH = i := hei
  refine ⟨e.val, ⟨(mem_colorClass color i eH).mpr hcolor,
    (Finset.mem_filter.mp e.property).2⟩, ?_⟩
  intro f hf
  let fH : H := ⟨f, colorClass_subset color i hf.1⟩
  have hfcolor : color fH = i := (mem_colorClass color i fH).mp hf.1
  exact congrArg Subtype.val (hP.eq_of_common (hfcolor.trans hcolor.symm)
    hf.2 (Finset.mem_filter.mp e.property).2)

/-- Every proper coloring with precisely `d` colors of a `d`-rigid hypergraph
has the prescribed perfect-matching classes, up to one unique color permutation. -/
theorem rigid_proper_coloring_unique [Nonempty V] (R : RigidFamily H I)
    (color : H → I) (hP : Proper color) :
    ∃! σ : Equiv.Perm I, ∀ i, colorClass color i = R.matching (σ i) := by
  classical
  have hperf : ∀ i, PerfectMatching H (colorClass color i) :=
    regular_colorClass_perfect color hP (fun v => R.regular v)
  have hex : ∀ i, ∃ j, colorClass color i = R.matching j := fun i => R.complete _ (hperf i)
  choose s hs using hex
  have hinj : Function.Injective s := by
    intro i j hij
    let v : V := Classical.arbitrary V
    obtain ⟨e, he, hu⟩ := (hperf i).existsUnique_edge v
    let eH : H := ⟨e, colorClass_subset color i he.1⟩
    have hclasses : colorClass color i = colorClass color j :=
      (hs i).trans ((congrArg R.matching hij).trans (hs j).symm)
    have hej : e ∈ colorClass color j := by rw [← hclasses]; exact he.1
    exact ((mem_colorClass color i eH).mp he.1).symm.trans
      ((mem_colorClass color j eH).mp hej)
  let σ : Equiv.Perm I := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, hs, ?_⟩
  intro τ hτ
  apply Equiv.ext
  intro i
  exact R.matching_injective ((hτ i).symm.trans (hs i))

end RigidGHZ.EdgeColoring
