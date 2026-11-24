module

public import RigidGHZ.Construction.ExactPackedFactor
public import RigidGHZ.Construction.RoundedOwnerCounts
public import RigidGHZ.Construction.NumericalPrivate

/-! Actual rigid factors with the exact support and private-hole counts retained. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

open RectangleEstimates Rectangle

def ExactFactorWitness (k T m : ℕ) (G : Hypergraph (Fin 3 × Fin m))
    (U : Finset (Fin m)) (R : ℕ) : Prop :=
  Uniform G 3 ∧ BalancedPartite G 3 m ∧
  Nonempty (RigidFamily G (Fin (T + 1) × Fin (T + 1))) ∧
  (∀ e ∈ G, ∃ x : Fin 3 → Fin m, e = tupleEdge x) ∧
  (∀ x : Fin 3 → Fin m, tupleEdge x ∈ G →
    (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) ∧
  (R : ℝ) = privateAmount k T (boxHeight k T m) (remainder k T m) ∧
  U.card = supportCount k T (boxHeight k T m) R

 theorem exact_rectangular_factor {k T m : ℕ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hlo : 128 * k ^ 3 * T ^ 7 ≤ m) (hhi : m < 128 * k ^ 3 * (T + 1) ^ 7) :
    ∃ G : Hypergraph (Fin 3 × Fin m), ∃ U : Finset (Fin m), ∃ R : ℕ,
      ExactFactorWitness k T m G U R := by
  classical
  let H := boxHeight k T m
  let ρ := remainder k T m
  have hT6 : 6 ≤ T := by omega
  have hm : 1 ≤ m := by
    have hp : 0 < 128 * k ^ 3 * T ^ 7 := by positivity
    omega
  have hdiv := box_division (T := T) hk (show 1 ≤ T by omega) hm
  have hρ : ρ < widthA k T * widthB k T := hdiv.1
  have hsize : widthA k T * widthB k T * H + ρ + 1 = m := hdiv.2
  have hheight := box_height_bounds hk (show 100 ≤ T by omega) hlo hhi
  have hh : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H := hheight.1
  have hh' : (H : ℝ) ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2 := hheight.2
  let s := numericalLayout k T H hk hT6 hh
  obtain ⟨R, hRpos, hRcap, hbalance, hRupper⟩ := private_count_exists hk hT hh hh' hρ
  have hmarg := natural_margins hk hT6 hh
  have hgrid := grid_fits hk hT hh
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT6
  have hnh : 0 < s.nh := by
    have hn := (nHorizontal_bounds hkr hTr hh).1
    change 0 < nHorizontal k T H
    omega
  have hnf : 0 < s.nf := by
    have hn := (nFull_bounds hkr hTr hh).1
    change 0 < nFull k T H
    omega
  obtain ⟨G, U, hUG, hPG, hRG, htrans, hsupport, hUcard⟩ :=
    s.factor_of_counts_exact (A := widthA k T) (Px := gridX k T) (Py := gridY k T)
      (R := R) (ρ := ρ) (show 1 ≤ T by omega) hmarg.1 hmarg.2
      (shortIndicator_valid k T H) hnh hnf (numericalLayout_plane_fit hk hT hh)
      hgrid.2.1 hgrid.2.2 hRpos hRcap hρ.le
      (numericalLayout_full_supply k T H hk hT6 hh)
      (fun l => numericalLayout_proper_supply k T H l.val hk hT6 hh) hbalance
  have hRcast : (R : ℝ) = privateAmount k T H ρ :=
    private_count_cast_of_balance hk hT6 hh hbalance
  have hUexact : U.card = supportCount k T H R := hUcard
  let f : Fin (widthA k T * widthB k T * H + ρ + 1) ≃ Fin m := finCongr hsize
  let e := Equiv.prodCongr (Equiv.refl (Fin 3)) f
  let G' := relabelHypergraph e G
  let U' := relabelEdge f U
  have ht' : ∀ e ∈ G', ∃ x : Fin 3 → Fin m, e = tupleEdge x :=
    ground_relabel_transversal f G htrans
  refine ⟨G', U', R, hUG.relabel e, ?_, ?_, ht', ?_, hRcast, ?_⟩
  · simpa only [Fintype.card_fin] using balancedPartite_of_transversal G' ht'
  · obtain ⟨RG⟩ := hRG
    exact ⟨RG.relabel e⟩
  · exact ground_relabel_support f G U hsupport
  · simpa only [U', relabelEdge_card] using hUexact

end RigidGHZ.Rectangular
