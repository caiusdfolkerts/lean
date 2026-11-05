module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N3R1C0

kernel_lrat_refutation extension
  "p cnf 3 2\n3 0\n-3 0\n"
  "3 0 1 2 0\n"

end Papers.RationalityTen.MatroidCases.N3R1C0
