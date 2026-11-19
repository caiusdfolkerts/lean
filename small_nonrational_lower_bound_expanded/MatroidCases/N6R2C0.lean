module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N6R2C0

kernel_lrat_refutation extension
  "p cnf 15 17\n-4 0\n-5 0\n-6 0\n7 0\n8 0\n9 0\n10 0\n-14 -7 4 11 0\n-14 -8 5 12 0\n-14 -9 6 13 0\n-11 -10 4 14 0\n-12 -10 5 14 0\n-13 -10 6 14 0\n11 12 13 14 15 0\n-15 11 12 13 14 0\n-14 -13 -12 -11 15 0\n-15 -14 -13 -12 -11 0\n"
  "18 14 0 7 3 2 1 11 12 13 15 14 0\n19 11 0 18 4 1 8 0\n20 12 0 18 5 2 9 0\n21 13 0 18 6 3 10 0\n22 -15 0 18 21 20 19 17 0\n23 0 18 21 20 19 22 16 0\n"

end Papers.RationalityTen.MatroidCases.N6R2C0
