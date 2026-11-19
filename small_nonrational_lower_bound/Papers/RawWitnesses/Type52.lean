module
prelude
public import Papers.RawWitnesses.Type52Spanning
public import Papers.RawWitnesses.Type52Facets
public import Papers.RawWitnesses.Type52LowRanks
public import Papers.RawWitnesses.Type52Relations
public import Papers.RawWitnesses.Type52Coverage
public import Papers.RawWitnesses.Type52Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type52
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Type52
