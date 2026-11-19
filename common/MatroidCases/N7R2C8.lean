module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C8

kernel_lrat_refutation extension
  "p cnf 21 33\n-1 0\n2 0\n3 0\n4 0\n6 0\n7 0\n9 0\n10 0\n11 0\n13 0\n14 0\n15 0\n-17 -2 1 16 0\n-16 -3 1 17 0\n-16 -6 18 19 0\n-17 -13 18 21 0\n-17 -14 19 21 0\n-17 -15 20 21 0\n-18 -4 16 19 0\n-18 -7 16 20 0\n-18 -11 16 21 0\n-19 -3 17 18 0\n-20 -6 18 19 0\n-21 -6 18 19 0\n-21 -9 18 20 0\n-21 -10 19 20 0\n16 17 18 19 20 21 0\n-21 -20 -19 -18 16 17 0\n-21 -20 -19 -17 -16 18 0\n-21 -20 -18 -17 -16 19 0\n-21 -19 -18 -17 -16 20 0\n-20 -19 -18 -17 -16 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "34 18 16 17 0 5 3 22 23 24 27 0\n35 16 0 9 6 4 2 1 13 34 19 20 21 28 0\n36 17 0 35 3 1 14 0\n37 -18 -20 -21 0 36 35 33 30 0\n38 -20 -21 0 36 35 5 37 15 29 0\n39 -21 0 36 35 8 7 38 25 26 31 0\n40 18 0 36 10 39 16 0\n41 19 0 36 11 39 17 0\n42 20 0 36 12 39 18 0\n43 0 42 41 40 36 35 39 32 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C8
