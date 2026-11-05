module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C7

kernel_lrat_refutation extension
  "p cnf 21 31\n-1 0\n2 0\n3 0\n4 0\n-6 0\n7 0\n9 0\n10 0\n11 0\n13 0\n14 0\n15 0\n-17 -2 1 16 0\n-19 -2 6 18 0\n-16 -3 1 17 0\n-18 -4 6 19 0\n-17 -9 18 20 0\n-17 -13 18 21 0\n-17 -14 19 21 0\n-17 -15 20 21 0\n-18 -7 16 20 0\n-18 -11 16 21 0\n-20 -3 17 18 0\n-21 -3 17 18 0\n-21 -10 19 20 0\n16 17 18 19 20 21 0\n-21 -20 -19 -18 16 17 0\n-21 -19 -18 -17 -16 20 0\n-20 -19 -18 -17 -16 21 0\n-21 -20 -17 -16 18 19 0\n-21 -20 -19 -18 -17 -16 0\n"
  "32 18 16 17 0 3 2 5 14 23 24 26 0\n33 16 0 9 6 4 5 2 1 13 32 16 21 22 27 0\n34 17 0 33 3 1 15 0\n35 -18 -20 -21 0 34 33 4 5 16 31 0\n36 -20 -21 0 34 33 2 5 35 14 30 0\n37 -21 0 34 33 7 8 36 25 17 28 0\n38 19 0 34 11 37 19 0\n39 18 0 34 10 37 18 0\n40 20 0 34 12 37 20 0\n41 0 40 38 39 34 33 37 29 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C7
