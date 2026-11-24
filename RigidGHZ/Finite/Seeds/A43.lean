module

public import RigidGHZ.Finite.Seeds.A43Data
public import RigidGHZ.Finite.Seeds.A43Proof.Chunk008
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A43
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/A43.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin 5) :=
  valid.family complete

theorem rigid : IsRigid data.host 5 := ⟨family⟩

end RigidGHZ.Finite.Seeds.A43
