module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N4R3C0

kernel_lrat_refutation extension
  "p cnf 4 8\n2 3 4 0\n-4 2 3 0\n-3 2 4 0\n-4 -3 2 0\n-2 3 4 0\n-4 -2 3 0\n-3 -2 4 0\n-4 -3 -2 0\n"
  "9 4 2 0 1 3 0\n10 2 0 9 2 4 0\n11 -4 0 10 8 6 0\n12 -3 0 10 11 7 0\n13 0 10 12 11 5 0\n"

end Papers.RationalityTen.MatroidCases.N4R3C0
