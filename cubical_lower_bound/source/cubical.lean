import cubical.polytope.main
import cubical.polytope.face_bounds
import cubical.polytope.generic_theorems
import cubical.polytope.stacking_sharpness_real
import cubical.pl.lower_bound

/-!
# Complete formalization of “The cubical lower bound theorem”

This entry point imports every principal mathematical claim of the paper:
Theorem 1, Lemma 2, Proposition 3, Corollaries 4 and 5, the strengthened
face-number formulas, and cube/stacked-cubical sharpness.

See `README.md` for the correspondence and `cubical.audit` for the
transitive axiom guards and machine-readable dependency graphs.
-/
