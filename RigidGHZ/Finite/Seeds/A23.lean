module

public import RigidGHZ.Finite.Seeds.A23Data
public import RigidGHZ.Finite.Seeds.A23Proof.Chunk007
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A23
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/A23.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin 6) :=
  valid.family complete

theorem rigid : IsRigid data.host 6 := ⟨family⟩

end RigidGHZ.Finite.Seeds.A23
