module
prelude
public import Papers.RawWitnesses.Type53Spanning
public import Papers.RawWitnesses.Type53Facets
public import Papers.RawWitnesses.Type53LowRanks
public import Papers.RawWitnesses.Type53Relations
public import Papers.RawWitnesses.Type53Coverage
public import Papers.RawWitnesses.Type53Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type53
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Type53
