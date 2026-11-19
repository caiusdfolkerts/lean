module
public import MatroidChecked.PackedClauses
meta import MatroidChecked.InlineFormula
import all MatroidCases.N8R4C62

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C62

/-- The original ordered CNF data, with project aliases expanded. -/
@[expose] noncomputable def formula : Sat.Fmla :=
  inline_cnf% Papers.RationalityTen.MatroidCases.N8R4C62.extension.formula

/-- The original kernel-checked derivation of the empty clause. -/
theorem refutation : Sat.Fmla.proof formula [] := by
  change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N8R4C62.extension.formula []
  exact Papers.RationalityTen.MatroidCases.N8R4C62.extension.refutation

end Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C62
