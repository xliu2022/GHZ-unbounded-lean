module

public import RigidGHZ.Supplement.Periodic.ElevenCodeCheck05

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem catalogue_pair_codes :
    catalogueList.map (fun A => finitePairCode (scheme.input A, scheme.output A)) =
      cataloguePairCodes := by
  rw [catalogue_chunk_decomposition]
  simp only [List.map_append, cataloguePairCodes, pair_code_chunk00, pair_code_chunk01, pair_code_chunk02, pair_code_chunk03, pair_code_chunk04, pair_code_chunk05]

theorem catalogue_input_codes :
    catalogueList.map (fun A => finiteSetCode (scheme.input A)) = cataloguePairCodes.map Prod.fst := by
  simpa only [List.map_map, Function.comp_def, finitePairCode] using
    congrArg (List.map Prod.fst) catalogue_pair_codes

theorem catalogue_output_codes :
    catalogueList.map (fun A => finiteSetCode (scheme.output A)) = cataloguePairCodes.map Prod.snd := by
  simpa only [List.map_map, Function.comp_def, finitePairCode] using
    congrArg (List.map Prod.snd) catalogue_pair_codes

end RigidGHZ.Supplement.Periodic.Eleven
