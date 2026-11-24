module

public import RigidGHZ.Partite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace RigidGHZ.Finite
open scoped BigOperators

/- The finite exchange inequality on three representatives, multiplied by six.
Diagonal arcs are allowed; opposite non-diagonal arcs are forbidden. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
 theorem three_exchange_weight :
    ∀ R : Fin 3 → Fin 3 → Bool,
      (∀ a, R a a = true) →
      (∀ a b, a ≠ b → ¬(R a b = true ∧ R b a = true)) →
      9 ≤ ∑ a : Fin 3, 6 / (Finset.univ.filter (fun b => R a b = true)).card := by
  decide

/-- A fiber of size `c` contributes `c * floor(6/c) ≤ 6`; there are nine pairs. -/
theorem pair_fiber_weight_bound {D : Type*} [Fintype D] [DecidableEq D]
    (f : D → Fin 3 × Fin 3) :
    ∑ a : D, 6 / (Finset.univ.filter (fun b => f b = f a)).card ≤ 54 := by
  classical
  let w : Fin 3 × Fin 3 → ℕ := fun p => 6 / (Finset.univ.filter (fun b => f b = p)).card
  have heq := Finset.sum_fiberwise' (Finset.univ : Finset D) f w
  have hb : (∑ p : Fin 3 × Fin 3,
      (Finset.univ.filter (fun b => f b = p)).card * w p) ≤ 54 := by
    calc
      _ ≤ ∑ _p : Fin 3 × Fin 3, 6 := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.mul_div_le 6 _
      _ = 54 := by decide
  have hs : (∑ p : Fin 3 × Fin 3,
      (Finset.univ.filter (fun b => f b = p)).card * w p) = ∑ a : D, w (f a) := by
    simpa only [Finset.sum_const, smul_eq_mul] using heq
  rw [hs] at hb
  exact hb

section CoordinateFamily

variable {I : Type*} [Fintype I]
variable {H : Hypergraph (Fin 3 × Fin 3)}

/-- The last two coordinates of a prescribed matching edge. -/
def coordinatePair (p : I → Fin 3 → Equiv.Perm (Fin 3)) (x : I × Fin 3) : Fin 3 × Fin 3 :=
  (p x.1 1 x.2, p x.1 2 x.2)

/-- All three coordinates of a prescribed matching edge. -/
def coordinateSource (p : I → Fin 3 → Equiv.Perm (Fin 3)) (x : I × Fin 3) : Fin 3 → Fin 3 :=
  fun t => p x.1 t x.2

theorem source_eq_of_pair_row (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3)) {x y : I × Fin 3}
    (hr : x.2 = y.2) (hp : coordinatePair p x = coordinatePair p y) :
    coordinateSource p x = coordinateSource p y := by
  funext t
  fin_cases t
  · change (p x.1 0) x.2 = (p y.1 0) y.2
    simpa only [hp0, Equiv.refl_apply] using hr
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

theorem source_mem_matching (F : RigidFamily H I)
    (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (x : I × Fin 3) : tupleEdge (coordinateSource p x) ∈ F.matching x.1 := by
  rw [hm]
  exact Finset.mem_image.mpr ⟨x.2, Finset.mem_univ _, rfl⟩

theorem coordinateSource_injective (F : RigidFamily H I)
    (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w)) :
    Function.Injective (coordinateSource p) := by
  intro x y hxy
  have hr : x.2 = y.2 := by
    have hh := congrFun hxy 0
    simpa only [coordinateSource, hp0, Equiv.refl_apply] using hh
  have hx := source_mem_matching F p hm x
  have hy := source_mem_matching F p hm y
  rw [← hxy] at hy
  exact Prod.ext (F.eq_of_shared_edge hx hy) hr

/-- A pair fiber and its set of possible first coordinates have the same size. -/
theorem pair_fiber_card (F : RigidFamily H I)
    (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (i : I) (a : Fin 3) :
    (Finset.univ.filter (fun x : I × Fin 3 => coordinatePair p x = coordinatePair p (i,a))).card =
    (Finset.univ.filter (fun b : Fin 3 => ∃ j, coordinatePair p (j,b) = coordinatePair p (i,a))).card := by
  classical
  let S := Finset.univ.filter (fun x : I × Fin 3 => coordinatePair p x = coordinatePair p (i,a))
  have hi : Set.InjOn Prod.snd (↑S : Set (I × Fin 3)) := by
    intro x hx y hy hxy
    apply coordinateSource_injective F p hp0 hm
    apply source_eq_of_pair_row p hp0 hxy
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  have himage : S.image Prod.snd =
      Finset.univ.filter (fun b : Fin 3 => ∃ j, coordinatePair p (j,b) = coordinatePair p (i,a)) := by
    ext b
    simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j,c⟩, hjc, rfl⟩
      exact ⟨j, hjc⟩
    · rintro ⟨j,hj⟩
      exact ⟨(j,b), hj, rfl⟩
  calc
    S.card = (S.image Prod.snd).card := (Finset.card_image_of_injOn hi).symm
    _ = _ := congrArg Finset.card himage

/-- Coordinate membership follows from the source with the same first coordinate
and the same last-coordinate pair. -/
theorem coordinate_matching_subset (F : RigidFamily H I)
    (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (q : Fin 3 → Equiv.Perm (Fin 3)) (hq0 : q 0 = Equiv.refl (Fin 3))
    (h : ∀ w, ∃ j, coordinatePair p (j,w) = (q 1 w, q 2 w)) :
    coordinateMatching (fun t w => q t w) ⊆ H := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j, hj⟩ := h w
  have heq : (fun t => q t w) = coordinateSource p (j,w) := by
    funext t
    fin_cases t
    · change (q 0) w = (p j 0) w
      simp only [hp0, hq0, Equiv.refl_apply]
    · exact (congrArg Prod.fst hj).symm
    · exact (congrArg Prod.snd hj).symm
  rw [heq]
  exact (F.perfect j).subset (source_mem_matching F p hm (j,w))

/-- Opposite exchanges would produce a new matching sharing the untouched third
edge with the original matching. Rigidity therefore excludes them. -/
theorem coordinate_exchange_antisymm (F : RigidFamily H I)
    (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (i : I) (a b : Fin 3) (hab : a ≠ b) :
    ¬((∃ j, coordinatePair p (j,b) = coordinatePair p (i,a)) ∧
      (∃ j, coordinatePair p (j,a) = coordinatePair p (i,b))) := by
  classical
  rintro ⟨hab', hba'⟩
  let q : Fin 3 → Equiv.Perm (Fin 3) :=
    ![Equiv.refl _, (Equiv.swap a b).trans (p i 1), (Equiv.swap a b).trans (p i 2)]
  have hq0 : q 0 = Equiv.refl (Fin 3) := rfl
  have hs : coordinateMatching (fun t w => q t w) ⊆ H := by
    apply coordinate_matching_subset F p hp0 hm q hq0
    intro w
    by_cases hwa : w = a
    · subst w
      simpa [q, coordinatePair] using hba'
    by_cases hwb : w = b
    · subst w
      simpa [q, coordinatePair] using hab'
    · refine ⟨i, ?_⟩
      simp [q, coordinatePair, Equiv.swap_apply_of_ne_of_ne hwa hwb]
  have hnew : PerfectMatching H (coordinateMatching (fun t w => q t w)) :=
    (coordinateMatching_perfect (fun t w => q t w) (fun t => (q t).bijective)).mono hs
  obtain ⟨j, hj⟩ := F.complete _ hnew
  have hc : ∃ c : Fin 3, c ≠ a ∧ c ≠ b :=
    (by decide : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b) a b
  obtain ⟨c, hca, hcb⟩ := hc
  have heqc : (fun t => q t c) = coordinateSource p (i,c) := by
    funext t
    fin_cases t
    · simp [q, coordinateSource, hp0]
    · simp [q, coordinateSource, Equiv.swap_apply_of_ne_of_ne hca hcb]
    · simp [q, coordinateSource, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have hcn : tupleEdge (coordinateSource p (i,c)) ∈ coordinateMatching (fun t w => q t w) := by
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, congrArg tupleEdge heqc⟩
  rw [hj] at hcn
  have hji : j = i := F.eq_of_shared_edge hcn (source_mem_matching F p hm (i,c))
  subst j
  have han : tupleEdge (fun t => q t a) ∈ coordinateMatching (fun t w => q t w) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  rw [hj, hm] at han
  obtain ⟨u, hu, hequ⟩ := Finset.mem_image.mp han
  have hcoords := tupleEdge_injective hequ
  have hua : u = a := by
    have hh := congrFun hcoords 0
    simpa only [hp0, hq0, Equiv.refl_apply] using hh
  subst u
  have hh := congrFun hcoords 1
  have hpab : p i 1 a = p i 1 b := by
    simpa [q] using hh
  exact hab ((p i 1).injective hpab)

/-- Each matching contributes at least nine after the reciprocal codegrees are
multiplied by six. -/
theorem coordinate_local_weight (F : RigidFamily H I)
    (p : I → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (i : I) :
    9 ≤ ∑ a : Fin 3, 6 / (Finset.univ.filter
      (fun x : I × Fin 3 => coordinatePair p x = coordinatePair p (i,a))).card := by
  classical
  let R : Fin 3 → Fin 3 → Bool := fun a b =>
    decide (∃ j, coordinatePair p (j,b) = coordinatePair p (i,a))
  have hd : ∀ a, R a a = true := by
    intro a
    simp only [R, decide_eq_true_eq]
    exact ⟨i, rfl⟩
  have ha : ∀ a b, a ≠ b → ¬(R a b = true ∧ R b a = true) := by
    intro a b hab
    simpa only [R, decide_eq_true_eq] using coordinate_exchange_antisymm F p hp0 hm i a b hab
  have hw := three_exchange_weight R hd ha
  have hc : ∀ a : Fin 3,
      (Finset.univ.filter (fun x : I × Fin 3 => coordinatePair p x = coordinatePair p (i,a))).card =
      (Finset.univ.filter (fun b => R a b = true)).card := by
    intro a
    simpa only [R, decide_eq_true_eq] using pair_fiber_card F p hp0 hm i a
  simpa only [← hc] using hw

end CoordinateFamily

/-- The sharp upper bound for a rigid tripartite hypergraph with three vertices
in each canonically labeled part. -/
theorem tripartite_three_upper {H : Hypergraph (Fin 3 × Fin 3)} {d : ℕ}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H d) : d ≤ 6 := by
  classical
  obtain ⟨F⟩ := hR
  have hex : ∀ i : Fin d, ∃ q : Fin 3 → Equiv.Perm (Fin 3),
      q 0 = Equiv.refl (Fin 3) ∧ F.matching i = coordinateMatching (fun t w => q t w) := by
    intro i
    exact perfectMatching_coordinates 0 htrans (F.perfect i)
  choose p hp0 hm using hex
  have hlocal := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => coordinate_local_weight F p hp0 hm i)
  have hglobal := pair_fiber_weight_bound (coordinatePair p)
  rw [Fintype.sum_prod_type] at hglobal
  have hlow : d * 9 ≤ ∑ i : Fin d, ∑ a : Fin 3,
      6 / (Finset.univ.filter (fun x : Fin d × Fin 3 =>
        coordinatePair p x = coordinatePair p (i,a))).card := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hlocal
  omega


end RigidGHZ.Finite
