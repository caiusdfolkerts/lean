module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C4

kernel_lrat_refutation extension
  "p cnf 21 30\n-1 0\n-2 0\n-3 0\n4 0\n5 0\n6 0\n7 0\n-10 0\n11 0\n12 0\n13 0\n14 0\n-17 -4 1 16 0\n-18 -4 2 16 0\n-20 -4 10 19 0\n-16 -5 1 17 0\n-18 -5 3 17 0\n-16 -6 2 18 0\n-17 -6 3 18 0\n-19 -7 10 20 0\n-18 -14 19 21 0\n-19 -11 16 21 0\n-19 -12 17 21 0\n-19 -13 18 21 0\n-21 -6 18 19 0\n16 17 18 19 20 21 0\n-21 -20 -19 16 17 18 0\n-20 -19 -18 -17 -16 21 0\n-21 -18 -17 -16 19 20 0\n-21 -20 -19 -18 -17 -16 0\n"
  "31 18 19 20 0 6 3 2 18 19 25 26 0\n32 20 0 12 5 3 4 2 7 8 20 31 14 17 21 29 0\n33 19 0 32 4 8 15 0\n34 -17 -21 0 32 33 6 3 4 1 13 19 30 0\n35 -21 0 32 33 5 3 1 34 16 17 27 0\n36 17 0 33 10 35 23 0\n37 18 0 33 11 35 24 0\n38 16 0 33 9 35 22 0\n39 0 32 33 37 36 38 35 28 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C4
