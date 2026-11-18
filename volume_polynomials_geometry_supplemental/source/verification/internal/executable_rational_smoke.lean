module

import volume_polynomials
meta import volume_polynomials

/-!
Runtime checks for the computational parts of Section 8.

These checks exercise ordinary generated code for rational elimination,
rational hulls, box-volume counts, Lagrange coefficients, finite certificates,
and the concrete coefficient-net enumerator. They are an additional code
generation check, not a substitute for any universally quantified theorem.
The file must be run only after the ordinary complete default project build.
-/

set_option autoImplicit false

namespace VolumePolynomials.ExecutableRationalSmoke

private def check (label : String) (accepted : Bool) : IO Unit := do
  unless accepted do
    throw (IO.userError ("Rational runtime check failed: " ++ label))
  IO.println ("PASS: " ++ label)

private def inequality (a b : ℚ) : RationalElimination.Inequality 1 :=
  ⟨fun _ => a, b⟩

private def holdsRational (S : List (RationalElimination.Inequality 1)) (x : ℚ) : Bool :=
  S.all fun p => decide (p.rationalValue (fun _ => x) ≤ p.bound)

private def degreeOne : MultiIndex 1 1 := ⟨fun _ => 1, by simp⟩

private def run : IO Unit := do
  let feasible := RationalElimination.eliminateAll [inequality 1 1, inequality (-1) 0]
  check "Fourier--Motzkin feasible interval" (decide (feasible.map (·.bound) = [1]))
  let impossible := RationalElimination.eliminateAll [inequality 1 0, inequality (-1) (-1)]
  check "Fourier--Motzkin inconsistent interval" (decide (impossible.map (·.bound) = [-1]))
  let vertices : Fin 2 → Fin 1 → ℚ := fun j _ => if j = 0 then 0 else 2
  let hull := RationalElimination.hullHalfspaces vertices
  check "Rational hull includes both endpoints and its midpoint"
    (holdsRational hull 0 && holdsRational hull 1 && holdsRational hull 2)
  check "Rational hull excludes an exterior point" (!(holdsRational hull 3))
  check "Inner rational box-volume count" (decide (RationalElimination.lowerVolume hull 2 1 = 2))
  check "Outer rational box-volume count" (decide (RationalElimination.upperVolume hull 2 1 = 3))
  check "Executable normalized Lagrange factor product"
    (decide (lagrangeCoefficient 1 [2, 3] 1 = -(5 / 2 : ℚ)))
  let matrices : ℕ → Fin 1 → Fin 1 → ℚ := fun _ _ _ => 0
  let name : ℕ → Fin 1 → ℚ := fun _ _ => -2
  let certificate : RationalCertificates.Certificate (Fin 1) := .inl (0, 0)
  check "Finite rational certificate enumeration"
    ((RationalCertificates.enumerate matrices name (Encodable.encode certificate)).isSome)
  check "Finite lexicographic path output"
    (decide (ComputableFinitePaths.output (fun _ => [(0 : ℕ), 1])
      (fun _ x y => x = y) 3 = some 0))
  let descriptor : QuadraticSeparation.CertificateIndex (MultiIndex 1 1) :=
    (fun _ => 10000, 1, 0)
  let M := QuadraticSeparation.enumeratedRationalMatrix
    (RationalCoefficientNets.model 1 1 0) (Encodable.encode descriptor)
  check "Concrete coefficient net, terminating volume search, and quadratic enumeration"
    (decide (M degreeOne degreeOne = 99980000))
  let reconstructed := RationalReconstruction.output 1 1 0 (fun _ _ => 0) 0
  check "Actual bounded rational reconstruction outputs the zero polytope"
    (match reconstructed with
     | none => false
     | some s => decide (s.vertices 0 = [(0 : Fin 1 → ℚ)]))
  IO.println "RATIONAL RUNTIME SMOKE CHECKS PASSED"

#eval run

end VolumePolynomials.ExecutableRationalSmoke
