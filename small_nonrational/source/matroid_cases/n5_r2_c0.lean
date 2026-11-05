module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R2C0

kernel_lrat_refutation extension
  "p cnf 10 13\n-2 0\n-3 0\n4 0\n5 0\n6 0\n-9 -4 2 7 0\n-9 -5 3 8 0\n-7 -6 2 9 0\n-8 -6 3 9 0\n7 8 9 10 0\n-10 7 8 9 0\n-9 -8 -7 10 0\n-10 -9 -8 -7 0\n"
  "14 9 10 0 5 2 1 8 9 10 0\n15 10 0 4 2 3 1 14 6 7 12 0\n16 -9 0 15 4 2 3 1 6 7 13 0\n17 -7 0 5 1 16 8 0\n18 -8 0 5 2 16 9 0\n19 0 15 17 18 16 11 0\n"

end Papers.RationalityTen.MatroidCases.N5R2C0
