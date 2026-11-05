module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N4R2C0

kernel_lrat_refutation extension
  "p cnf 6 9\n-1 0\n2 0\n3 0\n-5 -2 1 4 0\n-4 -3 1 5 0\n4 5 6 0\n-6 4 5 0\n-5 -4 6 0\n-6 -5 -4 0\n"
  "10 4 0 2 1 4 7 6 0\n11 5 0 10 3 1 5 0\n12 6 0 11 10 8 0\n13 0 12 11 10 9 0\n"

end Papers.RationalityTen.MatroidCases.N4R2C0
