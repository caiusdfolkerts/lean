module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N3R2C0

kernel_lrat_refutation extension
  "p cnf 3 4\n2 3 0\n-3 2 0\n-2 3 0\n-3 -2 0\n"
  "5 2 0 1 2 0\n6 3 0 5 3 0\n7 0 6 5 4 0\n"

end Papers.RationalityTen.MatroidCases.N3R2C0
