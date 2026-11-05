module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C5

kernel_lrat_refutation extension
  "p cnf 21 26\n-1 0\n-2 0\n4 0\n5 0\n6 0\n7 0\n10 0\n11 0\n14 0\n15 0\n-17 -4 1 16 0\n-18 -4 2 16 0\n-16 -5 1 17 0\n-16 -6 2 18 0\n-18 -14 19 21 0\n-18 -15 20 21 0\n-19 -7 16 20 0\n-19 -11 16 21 0\n-20 -6 18 19 0\n-21 -10 19 20 0\n16 17 18 19 20 21 0\n-21 -20 -19 16 17 18 0\n-21 -20 -18 -17 -16 19 0\n-21 -19 -18 -17 -16 20 0\n-20 -19 -18 -17 -16 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "27 19 16 17 18 0 7 5 19 20 21 0\n28 16 0 8 6 3 2 1 11 12 27 17 18 22 0\n29 17 0 28 4 1 13 0\n30 18 0 28 5 2 14 0\n31 -20 -21 0 30 29 28 26 23 0\n32 -21 0 30 29 28 7 31 20 24 0\n33 20 0 30 10 32 16 0\n34 19 0 30 9 32 15 0\n35 0 33 34 30 29 28 32 25 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C5
