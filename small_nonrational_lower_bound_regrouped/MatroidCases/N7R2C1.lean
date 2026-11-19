module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C1

kernel_lrat_refutation extension
  "p cnf 21 27\n-2 0\n-3 0\n-4 0\n-5 0\n-6 0\n7 0\n8 0\n9 0\n10 0\n11 0\n-15 0\n-18 -7 2 16 0\n-19 -7 4 16 0\n-21 -7 15 20 0\n-18 -8 3 17 0\n-19 -8 5 17 0\n-16 -9 2 18 0\n-17 -9 3 18 0\n-19 -9 6 18 0\n-16 -10 4 19 0\n-17 -10 5 19 0\n-18 -10 6 19 0\n-20 -11 15 21 0\n16 17 18 19 20 21 0\n-21 -20 16 17 18 19 0\n-19 -18 -17 -16 20 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "28 18 20 21 0 8 5 2 1 17 18 19 24 0\n29 20 0 9 5 7 2 6 1 11 14 28 12 15 22 26 0\n30 21 0 29 10 11 23 0\n31 -19 0 30 29 8 5 7 4 6 3 13 16 19 27 0\n32 -16 0 9 3 31 20 0\n33 -17 0 9 4 31 21 0\n34 -18 0 9 5 31 22 0\n35 0 30 29 32 33 34 31 25 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C1
