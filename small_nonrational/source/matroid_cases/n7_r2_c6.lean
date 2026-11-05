module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C6

kernel_lrat_refutation extension
  "p cnf 21 28\n-1 0\n2 0\n3 0\n4 0\n5 0\n-6 0\n7 0\n8 0\n9 0\n11 0\n-15 0\n-17 -2 1 16 0\n-19 -2 6 18 0\n-16 -3 1 17 0\n-18 -4 6 19 0\n-21 -7 15 20 0\n-20 -11 15 21 0\n-16 -9 18 20 0\n-17 -9 18 20 0\n-18 -7 16 20 0\n-18 -8 17 20 0\n-21 -4 16 19 0\n-21 -5 17 19 0\n16 17 18 19 20 21 0\n-21 -20 -19 -18 16 17 0\n-21 -20 -17 -16 18 19 0\n-19 -18 -17 -16 20 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "29 18 20 21 0 9 2 6 13 18 19 24 0\n30 20 0 8 7 4 6 11 16 29 15 20 21 27 0\n31 21 0 30 10 11 17 0\n32 -16 -19 -18 0 31 30 3 1 14 28 0\n33 -19 0 31 30 2 1 6 13 32 12 25 0\n34 -18 0 4 6 33 15 0\n35 17 0 31 5 33 23 0\n36 16 0 31 4 33 22 0\n37 0 31 30 35 36 34 33 26 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C6
