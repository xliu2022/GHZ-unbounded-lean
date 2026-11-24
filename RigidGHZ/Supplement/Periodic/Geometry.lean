module

public import RigidGHZ.Supplement.Periodic.Transfer
public import RigidGHZ.Supplement.Linearity

/-! Uniformity, balanced partitions, and linearity of actual periodic lifts. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L]
  [DecidableEq V] [DecidableEq E] [DecidableEq L] (D : Scheme V E)

 theorem graph_balanced {r m : ℕ} (σ : Equiv.Perm L) (c : V → Fin r)
    (hpart : ∀ i, (Finset.univ.filter (fun v => c v = i)).card = m)
    (hedge : ∀ e i, ((D.edge e).filter (fun v => c v = i)).card = 1) :
    BalancedPartite (D.graph σ) r (m * Fintype.card L) := by
  refine ⟨fun p => c p.1, ?_, ?_⟩
  · intro i
    have heq : (Finset.univ : Finset (V × L)).filter (fun p => c p.1 = i) =
        (Finset.univ.filter (fun v => c v = i)).product Finset.univ := by
      ext p
      simp
    rw [heq]
    calc
      _ = (Finset.univ.filter (fun v => c v = i)).card * (Finset.univ : Finset L).card :=
        Finset.card_product _ _
      _ = m * Fintype.card L := by rw [hpart, Finset.card_univ]
  · intro g hg i
    obtain ⟨⟨e, j⟩, he, rfl⟩ := Finset.mem_image.mp hg
    have heq : (D.liftEdge σ e j).filter (fun p => c p.1 = i) =
        ((D.edge e).filter (fun v => c v = i)).map (D.liftVertex σ e j) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_map, liftEdge]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hcv⟩
        exact ⟨v, ⟨hv, hcv⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hcv⟩, rfl⟩
        exact ⟨⟨v, hv, rfl⟩, hcv⟩
    rw [heq, Finset.card_map, hedge]

 theorem same_edge_disjoint (σ : Equiv.Perm L) (e : E) {j k : L} (hjk : j ≠ k) :
    Disjoint (D.liftEdge σ e j) (D.liftEdge σ e k) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨v, l⟩ hvj hvk
  have hj := ((D.mem_liftEdge σ e j l v).mp hvj).2
  have hk := ((D.mem_liftEdge σ e k l v).mp hvk).2
  by_cases ho : v ∈ D.outgoing e
  · simp only [if_pos ho] at hj hk
    exact hjk (σ.injective (hj.symm.trans hk))
  · simp only [if_neg ho] at hj hk
    exact hjk (hj.symm.trans hk)

 theorem graph_linear (σ : Equiv.Perm L)
    (hbase : ∀ e f, e ≠ f → ((D.edge e) ∩ (D.edge f)).card ≤ 1) :
    IsLinear (D.graph σ) := by
  intro g hg h hh hgh
  obtain ⟨⟨e, j⟩, he, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨⟨f, k⟩, hf, rfl⟩ := Finset.mem_image.mp hh
  by_cases hef : e = f
  · subst f
    have hjk : j ≠ k := by intro hjk; exact hgh (by rw [hjk])
    have hd := D.same_edge_disjoint σ e hjk
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
    simp
  · have hcard : ((D.liftEdge σ e j) ∩ (D.liftEdge σ f k)).card ≤
        ((D.edge e) ∩ (D.edge f)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · rintro ⟨v, l⟩ hv
        exact Finset.mem_inter.mpr
          ⟨((D.mem_liftEdge σ e j l v).mp (Finset.mem_inter.mp hv).1).1,
           ((D.mem_liftEdge σ f k l v).mp (Finset.mem_inter.mp hv).2).1⟩
      · rintro ⟨v, l⟩ hv ⟨w, n⟩ hw hvw
        change v = w at hvw
        subst w
        have hl := ((D.mem_liftEdge σ e j l v).mp (Finset.mem_inter.mp hv).1).2
        have hn := ((D.mem_liftEdge σ e j n v).mp (Finset.mem_inter.mp hw).1).2
        exact Prod.ext rfl (hl.trans hn.symm)
    exact hcard.trans (hbase e f hef)

end RigidGHZ.Supplement.Periodic.Scheme
