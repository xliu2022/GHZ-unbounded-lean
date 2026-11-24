module

public import RigidGHZ.Finite.Seeds.A3Data
public import RigidGHZ.Finite.Seeds.A3Proof.Chunk000
public import RigidGHZ.Finite.ExactCoverAssemble

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  exact_cover_sat unsat (include_str "../ExactCoverCertificates/A3.core.json") data valid M hM hn

noncomputable def family : RigidFamily data.host (Fin 3) :=
  valid.family complete

theorem rigid : IsRigid data.host 3 := ⟨family⟩

end RigidGHZ.Finite.Seeds.A3
