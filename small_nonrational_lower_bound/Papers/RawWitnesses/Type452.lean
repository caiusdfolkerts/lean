module
prelude
public import Papers.RawWitnesses.Type452Spanning
public import Papers.RawWitnesses.Type452Facets
public import Papers.RawWitnesses.Type452LowRanks
public import Papers.RawWitnesses.Type452Relations
public import Papers.RawWitnesses.Type452Coverage
public import Papers.RawWitnesses.Type452Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type452
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Type452
