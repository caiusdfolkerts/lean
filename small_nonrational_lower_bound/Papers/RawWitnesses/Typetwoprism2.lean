module
prelude
public import Papers.RawWitnesses.Typetwoprism2Spanning
public import Papers.RawWitnesses.Typetwoprism2Facets
public import Papers.RawWitnesses.Typetwoprism2LowRanks
public import Papers.RawWitnesses.Typetwoprism2Relations
public import Papers.RawWitnesses.Typetwoprism2Coverage
public import Papers.RawWitnesses.Typetwoprism2Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typetwoprism2
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Typetwoprism2
