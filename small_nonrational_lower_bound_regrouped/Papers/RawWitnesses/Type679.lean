module
prelude
public import Papers.RawWitnesses.Type679Spanning
public import Papers.RawWitnesses.Type679Facets
public import Papers.RawWitnesses.Type679LowRanks
public import Papers.RawWitnesses.Type679Relations
public import Papers.RawWitnesses.Type679Coverage
public import Papers.RawWitnesses.Type679Positivity

/-! Assembly of the independently checked finite certificate stages. -/
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type679
open Papers.RationalWitnesses.Raw

theorem certificate_valid : certificate.Valid coordinates :=
  ⟨spanning_check, facets_check, low_ranks_check, relations_check, coverage_check⟩

#print axioms certificate_valid
end Papers.RationalWitnesses.RawWitnesses.Type679
