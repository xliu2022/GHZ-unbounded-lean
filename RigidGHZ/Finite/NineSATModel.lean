module

public import RigidGHZ.Finite.NineSATData
public import RigidGHZ.Finite.NineCover
public import RigidGHZ.Finite.SatKernel
public import RigidGHZ.Finite.PairNormalization

@[expose] public section
namespace RigidGHZ.Finite

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- SAT variable for a prefix count, using a rectangular `9 × 29 × 16` array. -/
def nineCountVariable (v : Fin 9) (i : Fin 29) (k : Fin 16) : ℕ :=
  364 + v.val * 464 + i.val * 16 + k.val

/-- Semantic valuation of every propositional variable in the certificate.
The first 84 variables are actual hyperedges, the next 280 are actual partitions,
and the remaining variables assert lower bounds on actual incidence counts. -/
def nineSATValuation (H : Hypergraph (Fin 9)) (n : ℕ) : Prop :=
  if h : n < 84 then nineEdge ⟨n,h⟩ ∈ H
  else if h' : n < 364 then ninePartition ⟨n - 84, by omega⟩ ⊆ H
  else
    let z := n - 364
    let v : Fin 9 := ⟨z / 464 % 9, Nat.mod_lt _ (by decide)⟩
    z % 16 ≤ prefixCount (fun j => nineEdge (nineIncident v j) ∈ H) (z % 464 / 16)

@[simp] theorem nineSAT_edge (H : Hypergraph (Fin 9)) (e : Fin 84) :
    nineSATValuation H e.val ↔ nineEdge e ∈ H := by
  simp only [nineSATValuation, dif_pos e.isLt]

@[simp] theorem nineSAT_partition (H : Hypergraph (Fin 9)) (i : Fin 280) :
    nineSATValuation H (84 + i.val) ↔ ninePartition i ⊆ H := by
  have h0 : ¬84 + i.val < 84 := by omega
  have h1 : 84 + i.val < 364 := by omega
  simp only [nineSATValuation, dif_neg h0, dif_pos h1, Nat.add_sub_cancel_left]

@[simp] theorem nineSAT_count (H : Hypergraph (Fin 9)) (v : Fin 9) (i : Fin 29) (k : Fin 16) :
    nineSATValuation H (nineCountVariable v i k) ↔
      k.val ≤ prefixCount (fun j => nineEdge (nineIncident v j) ∈ H) i.val := by
  have h0 : ¬nineCountVariable v i k < 84 := by dsimp [nineCountVariable]; omega
  have h1 : ¬nineCountVariable v i k < 364 := by dsimp [nineCountVariable]; omega
  have hz : nineCountVariable v i k - 364 = v.val * 464 + i.val * 16 + k.val := by
    dsimp [nineCountVariable]; omega
  have hv : (v.val * 464 + i.val * 16 + k.val) / 464 % 9 = v.val := by omega
  have hi : (v.val * 464 + i.val * 16 + k.val) % 464 / 16 = i.val := by omega
  have hk : (v.val * 464 + i.val * 16 + k.val) % 16 = k.val := by omega
  simp only [nineSATValuation, dif_neg h0, dif_neg h1, hz, hv, hi, hk]

 theorem nine_incident_count (H : Hypergraph (Fin 9)) (hU : Uniform H 3) (v : Fin 9) :
    prefixCount (fun j => nineEdge (nineIncident v j) ∈ H) 28 = degree H v := by
  rw [prefixCount_full]
  let S := Finset.univ.filter (fun j : Fin 28 => nineEdge (nineIncident v j) ∈ H)
  have hinj : Function.Injective (fun j => nineEdge (nineIncident v j)) :=
    nineEdge_injective.comp (nineIncident_injective v)
  have himage : S.image (fun j => nineEdge (nineIncident v j)) = H.filter (fun e => v ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2,
        (nineIncident_complete v _).mpr ⟨j,rfl⟩⟩
    · intro he
      obtain ⟨heH,hve⟩ := Finset.mem_filter.mp he
      obtain ⟨i,rfl⟩ := nineEdge_complete e (hU e heH)
      obtain ⟨j,rfl⟩ := (nineIncident_complete v i).mp hve
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heH⟩,rfl⟩
  calc
    S.card = (S.image (fun j => nineEdge (nineIncident v j))).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = degree H v := congrArg Finset.card himage

 def ninePartitionEdge (i : Fin 280) (s : Fin 3) : Fin 84 :=
  let c := ninePartitionCode i
  ![c.1,c.2.1,c.2.2] s

 theorem ninePartitionEdge_mem (i : Fin 280) (s : Fin 3) :
    nineEdge (ninePartitionEdge i s) ∈ ninePartition i := by
  fin_cases s <;> simp [ninePartitionEdge,ninePartition]

 theorem ninePartition_subset_iff (H : Hypergraph (Fin 9)) (i : Fin 280) :
    ninePartition i ⊆ H ↔
      nineEdge (ninePartitionEdge i 0) ∈ H ∧
      nineEdge (ninePartitionEdge i 1) ∈ H ∧ nineEdge (ninePartitionEdge i 2) ∈ H := by
  simp [ninePartition,ninePartitionEdge,Finset.insert_subset_iff,Finset.singleton_subset_iff]

 theorem nineSAT_forward (H : Hypergraph (Fin 9)) (i : Fin 280) (s : Fin 3) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (84+i.val),.pos (ninePartitionEdge i s).val] := by
  change nineSATValuation H (84+i.val) → ¬nineSATValuation H (ninePartitionEdge i s).val → False
  rw [nineSAT_partition,nineSAT_edge]
  exact fun hm hn => hn (hm (ninePartitionEdge_mem i s))

 theorem nineSAT_backward (H : Hypergraph (Fin 9)) (i : Fin 280) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.pos (84+i.val),.neg (ninePartitionEdge i 0).val,
       .neg (ninePartitionEdge i 1).val,.neg (ninePartitionEdge i 2).val] := by
  change ¬nineSATValuation H (84+i.val) → nineSATValuation H (ninePartitionEdge i 0).val →
    nineSATValuation H (ninePartitionEdge i 1).val → nineSATValuation H (ninePartitionEdge i 2).val → False
  simp only [nineSAT_partition,nineSAT_edge]
  exact fun hn h0 h1 h2 => hn ((ninePartition_subset_iff H i).mpr ⟨h0,h1,h2⟩)

 def ninePartitionsThrough (e : Fin 84) : List ℕ :=
  (nineCoverIndices e).map (fun i => 84+i.val)

 theorem nineSAT_cover {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (e : Fin 84) :
    Sat.Valuation.satisfies (nineSATValuation H)
      (.neg e.val :: (ninePartitionsThrough e).map Sat.Literal.pos) := by
  change nineSATValuation H e.val → _
  rw [nineSAT_edge]
  intro he
  obtain ⟨j,hj⟩ := F.mem_iff.mp he
  obtain ⟨i,hi⟩ := ninePartition_complete hU (F.perfect j)
  apply sat_positive_list
  refine ⟨84+i.val,?_,?_⟩
  · apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    apply (nineCover_correct e i).mp
    simpa only [←hi] using hj
  · rw [nineSAT_partition]
    simpa only [←hi] using (F.perfect j).subset

 theorem nineSAT_conflict {H : Hypergraph (Fin 9)} (F : RigidFamily H (Fin 14))
    (e : Fin 84) (k : Fin 45) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (84+(nineConflict e k).1.val),.neg (84+(nineConflict e k).2.val)] := by
  change nineSATValuation H (84+(nineConflict e k).1.val) →
    nineSATValuation H (84+(nineConflict e k).2.val) → False
  simp only [nineSAT_partition]
  intro hi hj
  obtain ⟨hei,hej,hne⟩ := nineConflict_valid e k
  obtain ⟨a,ha⟩ := F.complete _ ((ninePartition_perfect _).mono hi)
  obtain ⟨b,hb⟩ := F.complete _ ((ninePartition_perfect _).mono hj)
  have hab : a = b := F.eq_of_shared_edge (by simpa only [←ha] using hei)
    (by simpa only [←hb] using hej)
  exact hne (ha.trans ((congrArg F.matching hab).trans hb.symm))

 theorem nineSAT_zero (H : Hypergraph (Fin 9)) (v : Fin 9) (i : Fin 29) :
    Sat.Valuation.satisfies (nineSATValuation H) [.pos (nineCountVariable v i 0)] := by
  change ¬nineSATValuation H (nineCountVariable v i 0) → False
  rw [nineSAT_count]
  simp

 theorem nineSAT_empty (H : Hypergraph (Fin 9)) (v : Fin 9) (k : Fin 15) :
    Sat.Valuation.satisfies (nineSATValuation H) [.neg (nineCountVariable v 0 k.succ)] := by
  change nineSATValuation H (nineCountVariable v 0 k.succ) → False
  rw [nineSAT_count]
  change k.val + 1 ≤ prefixCount _ 0 → False
  rw [prefixCount_zero]
  omega

 theorem nineSAT_step1 (H : Hypergraph (Fin 9)) (v : Fin 9) (i : Fin 28) (k : Fin 15) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (nineCountVariable v i.castSucc k.succ),.pos (nineCountVariable v i.succ k.succ)] := by
  change nineSATValuation H (nineCountVariable v i.castSucc k.succ) →
    ¬nineSATValuation H (nineCountVariable v i.succ k.succ) → False
  simp only [nineSAT_count,Fin.val_succ,Fin.val_castSucc]
  intro ha hn
  exact hn ((prefixThreshold_step _ i k.val).mpr (Or.inl ha))

 theorem nineSAT_step2 (H : Hypergraph (Fin 9)) (v : Fin 9) (i : Fin 28) (k : Fin 15) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (nineIncident v i).val,.neg (nineCountVariable v i.castSucc k.castSucc),
       .pos (nineCountVariable v i.succ k.succ)] := by
  change nineSATValuation H (nineIncident v i).val →
    nineSATValuation H (nineCountVariable v i.castSucc k.castSucc) →
    ¬nineSATValuation H (nineCountVariable v i.succ k.succ) → False
  simp only [nineSAT_count,nineSAT_edge,Fin.val_succ,Fin.val_castSucc]
  exact fun he hb hn => hn ((prefixThreshold_step _ i k.val).mpr (Or.inr ⟨he,hb⟩))

 theorem nineSAT_step3 (H : Hypergraph (Fin 9)) (v : Fin 9) (i : Fin 28) (k : Fin 15) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (nineCountVariable v i.succ k.succ),.pos (nineCountVariable v i.castSucc k.succ),
       .pos (nineIncident v i).val] := by
  change nineSATValuation H (nineCountVariable v i.succ k.succ) →
    ¬nineSATValuation H (nineCountVariable v i.castSucc k.succ) →
    ¬nineSATValuation H (nineIncident v i).val → False
  simp only [nineSAT_count,nineSAT_edge,Fin.val_succ,Fin.val_castSucc]
  intro hy hna hne
  rcases (prefixThreshold_step _ i k.val).mp hy with ha | ⟨he,hb⟩
  · exact hna ha
  · exact hne he

 theorem nineSAT_step4 (H : Hypergraph (Fin 9)) (v : Fin 9) (i : Fin 28) (k : Fin 15) :
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (nineCountVariable v i.succ k.succ),.pos (nineCountVariable v i.castSucc k.succ),
       .pos (nineCountVariable v i.castSucc k.castSucc)] := by
  change nineSATValuation H (nineCountVariable v i.succ k.succ) →
    ¬nineSATValuation H (nineCountVariable v i.castSucc k.succ) →
    ¬nineSATValuation H (nineCountVariable v i.castSucc k.castSucc) → False
  simp only [nineSAT_count,Fin.val_succ,Fin.val_castSucc]
  intro hy hna hnb
  rcases (prefixThreshold_step _ i k.val).mp hy with ha | ⟨he,hb⟩
  · exact hna ha
  · exact hnb hb

 theorem nineSAT_lower {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (v : Fin 9) :
    Sat.Valuation.satisfies (nineSATValuation H) [.pos (nineCountVariable v 28 14)] := by
  change ¬nineSATValuation H (nineCountVariable v 28 14) → False
  rw [nineSAT_count]
  change (¬14 ≤ prefixCount _ 28) → False
  rw [nine_incident_count H hU v,F.regular v]
  simp

 theorem nineSAT_upper {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (v : Fin 9) :
    Sat.Valuation.satisfies (nineSATValuation H) [.neg (nineCountVariable v 28 15)] := by
  change nineSATValuation H (nineCountVariable v 28 15) → False
  rw [nineSAT_count]
  change 15 ≤ prefixCount _ 28 → False
  rw [nine_incident_count H hU v,F.regular v]
  simp

/-- Every fan clause follows from the ordinary bound on a pair's completions. -/
theorem nineSAT_fan {H : Hypergraph (Fin 9)}
    (hmax : ∀ a b : Fin 9, a ≠ b → (pairCompletions H a b).card ≤ 4) (n : Fin 756) :
    let F := nineFan n
    Sat.Valuation.satisfies (nineSATValuation H)
      [.neg (F.edges 0).val,.neg (F.edges 1).val,.neg (F.edges 2).val,
       .neg (F.edges 3).val,.neg (F.edges 4).val] := by
  dsimp only
  change nineSATValuation H ((nineFan n).edges 0).val →
    nineSATValuation H ((nineFan n).edges 1).val →
    nineSATValuation H ((nineFan n).edges 2).val →
    nineSATValuation H ((nineFan n).edges 3).val →
    nineSATValuation H ((nineFan n).edges 4).val → False
  simp only [nineSAT_edge]
  intro h0 h1 h2 h3 h4
  obtain ⟨hab,hinj,hv⟩ := nineFan_valid n
  have hm : ∀ i : Fin 5, nineEdge ((nineFan n).edges i) ∈ H := by
    intro i; fin_cases i <;> assumption
  have hsub : Finset.univ.image (nineFan n).vertices ⊆
      pairCompletions H (nineFan n).a (nineFan n).b := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(hv i).1,(hv i).2.1,by simpa only [←(hv i).2.2] using hm i⟩
  have hc : (Finset.univ.image (nineFan n).vertices).card = 5 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hle := Finset.card_le_card hsub
  have hbound := hmax _ _ hab
  omega

 theorem nineSAT_given {H : Hypergraph (Fin 9)} (e : Fin 84) (he : nineEdge e ∈ H) :
    Sat.Valuation.satisfies (nineSATValuation H) [.pos e.val] := by
  change ¬nineSATValuation H e.val → False
  rw [nineSAT_edge]
  exact fun hn => hn he

 def NormalizedNinePair (H : Hypergraph (Fin 9)) (k : ℕ) : Prop :=
  ∀ x : Fin 9, x ≠ 0 → x ≠ 1 →
    (({0,1,x} : Finset (Fin 9)) ∈ H ↔ 2 ≤ x.val ∧ x.val < 2+k)

 theorem nineSAT_normpos {H : Hypergraph (Fin 9)} {k : ℕ}
    (hnorm : NormalizedNinePair H k) (j : Fin 7) (hj : j.val < k) :
    Sat.Valuation.satisfies (nineSATValuation H) [.pos j.val] := by
  change ¬nineSATValuation H (⟨j.val,by omega⟩ : Fin 84).val → False
  rw [nineSAT_edge,nine_initial_pair_edge]
  intro hn
  exact hn ((hnorm _ (by intro h; have hh := congrArg Fin.val h; change j.val + 2 = 0 at hh; omega)
    (by intro h; have hh := congrArg Fin.val h; change j.val + 2 = 1 at hh; omega)).mpr ⟨by change 2 ≤ j.val+2; omega,by change j.val+2 < 2+k; omega⟩)

 theorem nineSAT_normneg {H : Hypergraph (Fin 9)} {k : ℕ}
    (hnorm : NormalizedNinePair H k) (j : Fin 7) (hj : k ≤ j.val) :
    Sat.Valuation.satisfies (nineSATValuation H) [.neg j.val] := by
  change nineSATValuation H (⟨j.val,by omega⟩ : Fin 84).val → False
  rw [nineSAT_edge,nine_initial_pair_edge]
  intro he
  have h := (hnorm _ (by intro h; have hh := congrArg Fin.val h; change j.val + 2 = 0 at hh; omega)
    (by intro h; have hh := congrArg Fin.val h; change j.val + 2 = 1 at hh; omega )).mp he
  change 2 ≤ j.val+2 ∧ j.val+2 < 2+k at h
  omega

end RigidGHZ.Finite
