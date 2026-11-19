module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R3C0

kernel_lrat_refutation extension
  "p cnf 10 17\n-1 0\n-2 0\n3 0\n4 0\n-7 -3 1 6 0\n-9 -3 2 8 0\n-6 -4 1 7 0\n-8 -4 2 9 0\n-5 -3 1 2 0\n5 6 7 8 9 10 0\n-10 5 6 7 8 9 0\n-9 -8 5 6 7 10 0\n-10 -9 -8 5 6 7 0\n-7 -6 5 8 9 10 0\n-10 -7 -6 5 8 9 0\n-9 -8 -7 -6 5 10 0\n-10 -9 -8 -7 -6 5 0\n"
  "18 -5 0 3 1 2 9 0\n19 7 10 9 8 0 18 4 1 7 10 0\n20 10 8 9 0 18 3 1 19 5 14 0\n21 -7 -10 8 9 0 18 3 1 5 15 0\n22 8 0 18 4 1 3 2 6 20 21 7 11 0\n23 9 0 22 4 2 8 0\n24 7 -10 0 23 22 18 4 1 7 13 0\n25 -10 0 23 22 18 3 1 24 5 17 0\n26 -7 0 23 22 18 25 3 1 5 16 0\n27 -6 0 4 1 26 7 0\n28 0 23 22 18 27 26 25 12 0\n"

end Papers.RationalityTen.MatroidCases.N5R3C0
