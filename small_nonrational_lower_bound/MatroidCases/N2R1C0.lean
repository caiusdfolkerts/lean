module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N2R1C0

kernel_lrat_refutation extension
  "p cnf 2 2\n2 0\n-2 0\n"
  "3 0 1 2 0\n"

end Papers.RationalityTen.MatroidCases.N2R1C0
