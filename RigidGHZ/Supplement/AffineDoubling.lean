module

public import RigidGHZ.Supplement.AffineSeed

/-! Doubling a constant-sum affine seed.  All perfect matchings of the
ordinary hypergraph are classified; the constant bit is forced by summation. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

/-- Interpret a bit as the integer zero or one, before reducing modulo a size. -/
def bit (h : Bool) : ℕ := if h then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl
 theorem bit_le_one (h : Bool) : bit h ≤ 1 := by cases h <;> decide

 theorem sum_bit {X : Type*} [Fintype X] (h : X → Bool) :
    ∑ x, bit (h x) = (Finset.univ.filter (fun x => h x = true)).card := by
  simp [bit, Finset.sum_ite]

 theorem constant_bit_of_card_dvd {X : Type*} [Fintype X] (h : X → Bool)
    (hdvd : Fintype.card X ∣ (Finset.univ.filter (fun x => h x = true)).card) :
    ∃ b, ∀ x, h x = b := by
  classical
  let U := Finset.univ.filter (fun x => h x = true)
  by_cases hu : U.card = 0
  · refine ⟨false, ?_⟩
    intro x
    have hu0 : U = ∅ := Finset.card_eq_zero.mp hu
    have hne : h x ≠ true := by
      intro hx
      have : x ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      rw [hu0] at this
      exact Finset.notMem_empty _ this
    cases hx : h x <;> simp_all
  · have hle : Fintype.card X ≤ U.card := Nat.le_of_dvd (by omega) hdvd
    have heq : U = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa using hle)
    refine ⟨true, ?_⟩
    intro x
    have hx : x ∈ U := by rw [heq]; exact Finset.mem_univ x
    exact (Finset.mem_filter.mp hx).2

variable {m : ℕ} [NeZero m]

 theorem bit_cast_injective (hm : 2 ≤ m) :
    Function.Injective (fun h => (bit h : ZMod m)) := by
  letI : Fact (1 < m) := ⟨hm⟩
  intro h k hhk
  cases h <;> cases k <;> simp_all

/-- Doubled affine rows, indexed by the bit and the seed shift. -/
def doubleMap (lam δ : ZMod m) (h : Bool) (s : ZMod m) : Fin 3 → ZMod m → ZMod m :=
  ![id, (fun a => lam * a + s), (fun a => δ * (bit h : ZMod m) - (lam + 1) * a - s)]

 theorem doubleMap_bijective {lam : ZMod m} (hl : IsUnit lam) (hr : IsUnit (lam + 1))
    (δ : ZMod m) (h : Bool) (s : ZMod m) (j : Fin 3) :
    Function.Bijective (doubleMap lam δ h s j) := by
  fin_cases j
  · exact Function.bijective_id
  · exact baseMap_bijective hl hr s 1
  · have hfun : doubleMap lam δ h s 2 =
        (Equiv.addRight (δ * (bit h : ZMod m))) ∘ baseMap lam s 2 := by
      funext a
      simp [doubleMap, baseMap]
      ring
    change Function.Bijective (doubleMap lam δ h s 2)
    rw [hfun]
    exact (Equiv.addRight _).bijective.comp (baseMap_bijective hl hr s 2)

 def doublePerm {lam : ZMod m} (hl : IsUnit lam) (hr : IsUnit (lam + 1))
    (δ : ZMod m) (h : Bool) (s : ZMod m) (j : Fin 3) : Equiv.Perm (ZMod m) :=
  Equiv.ofBijective _ (doubleMap_bijective hl hr δ h s j)

@[simp] theorem doublePerm_apply {lam : ZMod m} (hl : IsUnit lam) (hr : IsUnit (lam + 1))
    (δ : ZMod m) (h : Bool) (s : ZMod m) (j : Fin 3) (a : ZMod m) :
    doublePerm hl hr δ h s j a = doubleMap lam δ h s j a := rfl

 theorem double_sum (lam δ a s : ZMod m) (h : Bool) :
    a + doubleMap lam δ h s 1 a + doubleMap lam δ h s 2 a = δ * (bit h : ZMod m) := by
  simp [doubleMap]
  ring

 theorem double_complete {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (hodd : Odd m) (δ : ZMod m) (hδ : IsUnit δ)
    (q r : Equiv.Perm (ZMod m))
    (hlocal : ∀ a, ∃ hs : Bool × S,
      q a = doubleMap lam δ hs.1 hs.2.val 1 a ∧
      r a = doubleMap lam δ hs.1 hs.2.val 2 a) :
    ∃ hs : Bool × S, (∀ a, q a = doubleMap lam δ hs.1 hs.2.val 1 a) ∧
      (∀ a, r a = doubleMap lam δ hs.1 hs.2.val 2 a) := by
  choose hs hq hr using hlocal
  have hsum : δ * ((∑ a, bit (hs a).1 : ℕ) : ZMod m) = 0 := by
    calc
      _ = ∑ a, (a + q a + r a) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hq, hr]
        exact (double_sum lam δ a (hs a).2.val (hs a).1).symm
      _ = 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Equiv.sum_comp q (fun a => a), Equiv.sum_comp r (fun a => a), sum_zmod_eq_zero hodd]
        simp
  have hdvd : m ∣ (Finset.univ.filter (fun a => (hs a).1 = true)).card := by
    rw [← sum_bit]
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    exact hδ.mul_left_cancel (by simpa using hsum)
  obtain ⟨h, hh⟩ := constant_bit_of_card_dvd (fun a => (hs a).1) (by simpa using hdvd)
  let r' : Equiv.Perm (ZMod m) := r.trans (Equiv.addRight (-δ * (bit h : ZMod m)))
  have hbase : ∀ a, ∃ s : S, q a = lam * a + s.val ∧ r' a = -(lam + 1) * a - s.val := by
    intro a
    refine ⟨(hs a).2, ?_, ?_⟩
    · simpa [doubleMap] using hq a
    · change r a + -δ * (bit h : ZMod m) = _
      rw [hr a, hh a]
      simp [doubleMap]
      ring
  obtain ⟨s, hqs, hrs⟩ := B.coordinate_complete q r' hbase
  refine ⟨(h, s), ?_, ?_⟩
  · exact hqs
  · intro a
    have ha := hrs a
    change r a + -δ * (bit h : ZMod m) = _ at ha
    dsimp [doubleMap]
    linear_combination ha

/-- The supplement's constant-sum doubling lemma, as a family on an ordinary
simple hypergraph. No coordinate-completeness premise is added. -/
def Seed.doubledFamily {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (δ : ZMod m) (hδ : IsUnit δ) :
    RigidFamily (coordinateHypergraph (fun hs : Bool × S => doubleMap lam δ hs.1 hs.2.val))
      (Bool × S) := by
  let p : (Bool × S) → Fin 3 → Equiv.Perm (ZMod m) :=
    fun hs => doublePerm B.unit_left B.unit_right δ hs.1 hs.2.val
  apply rigidFamily_of_coordinates 0 p
  · intro hs
    ext a
    rfl
  · intro i j hij a
    by_contra h
    push_neg at h
    have hs : i.2 = j.2 := by
      apply Subtype.ext
      simpa [p, doubleMap] using h 1
    have hh : i.1 = j.1 := by
      apply bit_cast_injective (m := m) (by omega)
      apply hδ.mul_left_cancel
      have h2 := h 2
      simpa [p, doubleMap, hs] using h2
    exact hij (Prod.ext hh hs)
  · intro q hq0 hq
    obtain ⟨hs, hs1, hs2⟩ := double_complete B hodd δ hδ (q 1) (q 2) (by
      intro a
      obtain ⟨hs, hhs⟩ := hq a
      exact ⟨hs, hhs 1, hhs 2⟩)
    refine ⟨hs, ?_⟩
    funext j
    ext a
    fin_cases j
    · change q 0 a = a
      rw [hq0]
      rfl
    · exact hs1 a
    · exact hs2 a

end RigidGHZ.Supplement.Affine
