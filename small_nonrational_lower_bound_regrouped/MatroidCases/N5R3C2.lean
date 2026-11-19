module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N5R3C2

kernel_lrat_refutation extension
  "p cnf 10 34\n1 0\n2 0\n3 0\n4 0\n-5 -3 6 8 0\n-5 -4 7 9 0\n-6 -2 5 8 0\n-6 -4 7 10 0\n-7 -2 5 9 0\n-7 -3 6 10 0\n-8 -7 6 10 0\n-8 -1 5 6 0\n-8 -4 9 10 0\n-8 -7 9 10 0\n-9 -1 5 7 0\n-9 -3 8 10 0\n-10 -1 6 7 0\n-10 -2 8 9 0\n-10 -5 8 9 0\n5 6 7 8 9 10 0\n-10 -9 -7 5 6 8 0\n-10 -8 -6 5 7 9 0\n-9 -8 -7 -6 5 10 0\n-10 -9 -8 -7 -6 5 0\n-9 -8 -5 6 7 10 0\n-7 -6 -5 8 9 10 0\n-9 -8 -7 -6 -5 10 0\n-10 -8 -7 -5 6 9 0\n-10 -9 -8 -7 -5 6 0\n-10 -8 -7 -6 -5 9 0\n-10 -9 -6 -5 7 8 0\n-10 -9 -8 -6 -5 7 0\n-10 -9 -7 -6 -5 8 0\n-10 -9 -8 -7 -6 -5 0\n"
  "35 9 6 5 8 0 2 9 18 20 0\n36 8 5 0 3 1 2 7 35 15 16 21 0\n37 -9 -10 -8 -6 5 0 1 15 24 0\n38 -10 -8 -6 5 0 2 37 9 22 0\n39 5 0 4 1 36 12 38 8 13 23 0\n40 -6 10 -8 -9 0 39 4 8 27 0\n41 10 -8 -9 0 39 40 11 25 0\n42 6 -10 -9 -8 0 1 39 29 17 0\n43 -8 -9 0 39 41 42 34 32 0\n44 -9 0 39 3 43 5 16 31 33 0\n45 7 0 39 4 44 6 0\n46 -10 0 45 39 44 19 28 30 0\n47 -8 0 45 44 46 14 0\n48 6 0 45 3 46 10 0\n49 0 45 48 39 47 44 46 26 0\n"

end Papers.RationalityTen.MatroidCases.N5R3C2
