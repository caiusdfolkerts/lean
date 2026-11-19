module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R2C2

kernel_lrat_refutation extension
  "p cnf 10 15\n-1 0\n2 0\n3 0\n4 0\n6 0\n-8 -2 1 7 0\n-7 -3 1 8 0\n-8 -6 9 10 0\n-9 -4 7 10 0\n-10 -2 7 9 0\n7 8 9 10 0\n-10 -9 7 8 0\n-10 -8 -7 9 0\n-9 -8 -7 10 0\n-10 -9 -8 -7 0\n"
  "16 9 7 8 0 2 11 10 0\n17 7 0 4 2 1 6 16 9 12 0\n18 8 0 17 3 1 7 0\n19 -10 0 18 17 15 13 0\n20 -9 0 18 17 19 14 0\n21 0 18 5 20 19 8 0\n"

end Papers.RationalityTen.MatroidCases.N5R2C2
