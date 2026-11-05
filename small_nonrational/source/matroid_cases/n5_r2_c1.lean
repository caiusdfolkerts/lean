module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R2C1

kernel_lrat_refutation extension
  "p cnf 10 13\n-1 0\n2 0\n3 0\n4 0\n-6 0\n-8 -2 1 7 0\n-10 -2 6 9 0\n-7 -3 1 8 0\n-9 -4 6 10 0\n7 8 9 10 0\n-10 -9 7 8 0\n-8 -7 9 10 0\n-10 -9 -8 -7 0\n"
  "14 8 9 10 0 3 1 8 10 0\n15 10 0 2 1 4 5 9 14 6 12 0\n16 9 0 15 2 5 7 0\n17 -8 0 15 16 2 1 6 13 0\n18 -7 0 3 1 17 8 0\n19 0 15 16 18 17 11 0\n"

end Papers.RationalityTen.MatroidCases.N5R2C1
