module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R4C0

kernel_lrat_refutation extension
  "p cnf 5 16\n2 3 4 5 0\n-5 2 3 4 0\n-4 2 3 5 0\n-5 -4 2 3 0\n-3 2 4 5 0\n-5 -3 2 4 0\n-4 -3 2 5 0\n-5 -4 -3 2 0\n-2 3 4 5 0\n-5 -2 3 4 0\n-4 -2 3 5 0\n-5 -4 -2 3 0\n-3 -2 4 5 0\n-5 -3 -2 4 0\n-4 -3 -2 5 0\n-5 -4 -3 -2 0\n"
  "17 4 5 2 0 1 5 0\n18 5 2 0 17 3 7 0\n19 -4 -5 2 0 4 8 0\n20 2 0 18 19 6 2 0\n21 4 -5 0 20 14 10 0\n22 -5 0 20 21 12 16 0\n23 -4 0 20 22 15 11 0\n24 -3 0 20 23 22 13 0\n25 0 20 24 23 22 9 0\n"

end Papers.RationalityTen.MatroidCases.N5R4C0
