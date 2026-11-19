module

public import cubical.polytope.main
public import cubical.polytope.face_bounds
public import cubical.polytope.generic_theorems
public import cubical.polytope.stacking_sharpness_real
public import cubical.pl.lower_bound

@[expose] public section

/-!
# Complete formalization of “The cubical lower bound theorem”

This entry point imports every principal mathematical claim of the paper:
Theorem 1, Lemma 2, Proposition 3, Corollaries 4 and 5, the strengthened
face-number formulas, and cube/stacked-cubical sharpness.

See `README.md` for the correspondence and `cubical.audit` for the
transitive axiom guards and machine-readable dependency graphs.
-/
