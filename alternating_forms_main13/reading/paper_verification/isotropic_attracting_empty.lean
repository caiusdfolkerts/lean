module

public import PaperVerification.IsotropicAttractingElimination

/-!
# The empty attracting charts

If a pivot coordinate plane is not common isotropic, its row-echelon
chart contains an original isotropy equation equal to a unit.  Thus the
entire scheme-theoretic chart is empty, including over nonreduced rings.
Combined with the elimination theorem, this gives the exact nonempty-cell
indexing condition, without a field-point or reducedness argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial

variable {R : Type*} [CommRing R] {n s : ℕ}

@[simp] theorem equation_constantCoeff (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    (equation (R := R) p c i j).constantCoeff = formMatrix c (p i) (p j) := by
  classical
  simp [equation, row_constantCoeff, mul_ite]

/-- Weight zero leaves exactly the original pivot-pair coefficient. -/
theorem equation_eq_constant_of_zero_weight (p : Fin s ↪ Fin n) (c : ℕ)
    (i j : Fin s) (hc : (p i).val + (p j).val = c) :
    equation (R := R) p c i j = C (formMatrix c (p i) (p j)) := by
  have hh := equation_homogeneous (R := R) p c i j
  have hd : c - (p i).val - (p j).val = 0 := by omega
  rw [hd] at hh
  calc
    _ = weightedHomogeneousComponent (coordinateWeight p) 0 (equation p c i j) :=
      (weightedHomogeneousComponent_eq_self hh).symm
    _ = C ((equation p c i j).coeff 0) :=
      weightedHomogeneousComponent_zero _ (fun v => ne_of_gt (coordinateWeight_pos p v))
    _ = _ := congrArg C (equation_constantCoeff p c i j)

variable {k : ℕ} {p : Fin s ↪ Fin (2*k+1)}

/-- A forbidden pivot edge gives the unit ideal, rather than an extra
nonempty component with a nonisotropic torus limit. -/
theorem isotropyIdeal_eq_top_of_not_independent (hp : ¬ IndependentPivots p) :
    isotropyIdeal (R := R) p (2*k+1) (2*k) = ⊤ := by
  classical
  unfold IndependentPivots at hp
  push Not at hp
  obtain ⟨i, j, hij, he⟩ := hp
  have hpi : p i ≠ p j := fun h => hij (p.injective h)
  have obtain_unit (c : ℕ) (hc : c = 2*k+1 ∨ c = 2*k)
      (hsum : (p i).val + (p j).val = c) :
      (1 : MvPolynomial (Coordinate p) R) ∈ isotropyIdeal p (2*k+1) (2*k) := by
    have hmem : equation (R := R) p c i j ∈ isotropyIdeal p (2*k+1) (2*k) := by
      apply Ideal.subset_span
      rcases hc with rfl | rfl
      · exact ⟨(true, i, j), rfl⟩
      · exact ⟨(false, i, j), rfl⟩
    rw [equation_eq_constant_of_zero_weight p c i j hsum] at hmem
    rcases lt_or_gt_of_ne hpi with hlt | hgt
    · have hcoeff : formMatrix (R := R) c (p i) (p j) = -1 := by
        simp [formMatrix, hsum, hlt, not_lt_of_gt hlt]
      have hn := neg_mem hmem
      simpa only [hcoeff, map_neg, map_one, neg_neg] using hn
    · have hcoeff : formMatrix (R := R) c (p i) (p j) = 1 := by
        simp [formMatrix, hsum, hgt]
      simpa only [hcoeff, map_one] using hmem
  apply (Ideal.eq_top_iff_one _).mpr
  by_cases h : (p i).val + (p j).val = 2*k
  · exact obtain_unit (2*k) (Or.inr rfl) h
  · exact obtain_unit (2*k+1) (Or.inl rfl) (he h)

end PaperVerification.IsotropicAttractingCoordinates
