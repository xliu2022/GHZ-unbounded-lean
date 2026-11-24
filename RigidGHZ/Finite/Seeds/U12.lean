module

public import RigidGHZ.Finite.Seeds.U12Data
public import RigidGHZ.Finite.Seeds.U12Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/U12.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin 12) :=
  valid.family complete

theorem rigid : IsRigid data.host 12 := ⟨family⟩

theorem witness : ∃ H : Hypergraph (Fin 12),
    Uniform H 3 ∧ IsRigid H 12 := ⟨data.host,uniform,rigid⟩

end RigidGHZ.Finite.Seeds.U12
