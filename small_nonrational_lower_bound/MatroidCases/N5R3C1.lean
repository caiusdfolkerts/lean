module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R3C1

kernel_lrat_refutation extension
  "p cnf 10 22\n-1 0\n2 0\n3 0\n4 0\n-6 -2 1 5 0\n-7 -2 1 5 0\n-5 -3 1 6 0\n-5 -4 1 7 0\n-8 -4 9 10 0\n-9 -3 8 10 0\n-10 -2 8 9 0\n-10 -5 8 9 0\n5 6 7 8 9 10 0\n-10 -9 5 6 7 8 0\n-10 -8 5 6 7 9 0\n-9 -8 5 6 7 10 0\n-10 -9 -8 5 6 7 0\n-7 -6 -5 8 9 10 0\n-10 -9 -7 -6 -5 8 0\n-10 -8 -7 -6 -5 9 0\n-9 -8 -7 -6 -5 10 0\n-10 -9 -8 -7 -6 -5 0\n"
  "23 9 8 5 6 7 0 2 13 11 0\n24 8 5 6 7 0 3 23 10 14 0\n25 -10 -8 5 6 7 0 17 15 0\n26 5 0 4 2 1 5 6 24 25 16 9 0\n27 6 0 26 3 1 7 0\n28 7 0 26 4 1 8 0\n29 9 -8 0 28 27 26 4 9 20 0\n30 -8 0 28 27 26 29 22 21 0\n31 -9 0 28 27 26 30 3 10 19 0\n32 -10 0 26 30 31 12 0\n33 0 28 27 26 30 31 32 18 0\n"

end Papers.RationalityTen.MatroidCases.N5R3C1
