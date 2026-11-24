module

public import RigidGHZ.Finite.Seeds.U24Data
public import RigidGHZ.Finite.Seeds.U24Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.U24
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/U24.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin 10) :=
  valid.family complete

theorem rigid : IsRigid data.host 10 := ⟨family⟩

theorem witness : ∃ H : Hypergraph (Fin 24),
    Uniform H 3 ∧ IsRigid H 10 := ⟨data.host,uniform,rigid⟩

end RigidGHZ.Finite.Seeds.U24
