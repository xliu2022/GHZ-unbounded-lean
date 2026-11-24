module

public import RigidGHZ.Finite.Seeds.A7Data
public import RigidGHZ.Finite.Seeds.A7Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A7
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/A7.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin 4) :=
  valid.family complete

theorem rigid : IsRigid data.host 4 := ⟨family⟩

end RigidGHZ.Finite.Seeds.A7
