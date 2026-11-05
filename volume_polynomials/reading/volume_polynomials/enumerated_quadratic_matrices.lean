module
public import VolumePolynomials.QuadraticSeparation

@[expose] public section

set_option autoImplicit false

/-!
# Executable coefficients of the enumerated quadratic forms

The enumerator returns a rational matrix, using only rational arithmetic and
the finite rational admission test. Its specification is proved equal to the
semantic polynomial enumerator. Thus no polynomial implementation is needed
to compute the actual coefficients of the certificates.
-/

open scoped BigOperators

namespace VolumePolynomials.QuadraticSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Encodable ι]

def enumeratedRationalMatrix (M : Model ι) (k : ℕ) : ι → ι → ℚ :=
  match enumeratedCertificate M k with
  | none => fun _ _ => 0
  | some (a, r, _) => rationalMatrix a r

/-- Exact agreement of the executable rational coefficients and the
homogeneous polynomial used in the mathematical characterization. -/
theorem enumeratedRationalMatrix_eval (M : Model ι) (k : ℕ) (c : Space ι) :
    (∑ i, ∑ j, (enumeratedRationalMatrix M k i j : ℝ) * c i * c j) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) := by
  first
  | cases hd : Encodable.decode (α := CertificateIndex ι) k with
    | none => simp [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm, hd]
    | some z =>
        obtain ⟨a, r, m⟩ := z
        by_cases ha : M.Admitted a r m
        · simp only [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm,
            hd, if_pos ha, eval_rationalForm]
          exact (quadratic_eq_matrix a r c).symm
        · simp [enumeratedRationalMatrix, enumeratedCertificate, enumeratedForm, hd, ha]

theorem enumeratedRationalMatrix_encode (M : Model ι)
    (a : ι → ℚ) (r : ℚ) (m : ℕ) (h : M.Admitted a r m) :
    enumeratedRationalMatrix M (Encodable.encode (a, r, m)) = rationalMatrix a r := by
  first
  | rw [enumeratedRationalMatrix, enumeratedCertificate_encode M a r m h]

/-- The complete abstract criterion with a literally executable rational
matrix at every natural-number index. Geometry must supply the model and the
four stated identifications before this is applied to a volume locus. -/
theorem countable_matrix_characterization
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧ ∀ k : ℕ,
      0 ≤ ∑ i, ∑ j, (enumeratedRationalMatrix M k i j : ℝ) * c i * c j := by
  first
  | simp only [enumeratedRationalMatrix_eval]
    exact countable_coefficient_characterization M V hzero hnonneg hnormalize hrealize c

end VolumePolynomials.QuadraticSeparation
