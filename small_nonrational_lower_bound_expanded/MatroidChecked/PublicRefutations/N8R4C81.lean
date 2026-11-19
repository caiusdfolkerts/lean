module
public import MatroidChecked.PackedClauses
public import MatroidChecked.PureClauseMathlibAdapter
meta import MatroidChecked.InlineFormulaWithCore
import all MatroidCases.N8R4C81

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C81

/-- The original ordered CNF data, with project aliases expanded. -/
@[expose] noncomputable def formula : Sat.Fmla :=
  inline_cnf_with_core% Papers.RationalityTen.MatroidCases.N8R4C81.extension.formula

/-- The original kernel-checked derivation of the empty clause. -/
theorem refutation : Sat.Fmla.proof formula [] := by
  change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N8R4C81.extension.formula []
  exact Papers.RationalityTen.MatroidCases.N8R4C81.extension.refutation

end Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C81
