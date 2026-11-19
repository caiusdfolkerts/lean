module

public import Continuation.Divisor.WallSupport

/-!
# The literal normalized wall relations in Proposition 6.3

The vectors are the outside ray followed by the original full-cone basis.
The outside coefficient is one, the other outside coefficient is proved
one, the vector relation is proved, and normalization determines every
coefficient uniquely. Thus negative mass is computed on the actual relation,
not on a newly stipulated inequality with the same name.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} (F : SmoothCompleteFan n)

/-- The outside ray and the ordered primitive generators of the full cone. -/
def normalizedWallVectors (s : F.fullCones) (w : Lattice n) : Fin (n+1) → Lattice n :=
  Fin.cons w (F.fullConeBasis s)

/-- The unique relation whose outside coefficient is one. -/
def normalizedWallCoefficients (s : F.fullCones) (w : Lattice n) : Fin (n+1) → ℤ :=
  Fin.cons 1 (fun i => -(F.fullConeBasis s).repr w i)

@[simp] theorem normalizedWallCoefficients_zero (s : F.fullCones) (w : Lattice n) :
    F.normalizedWallCoefficients s w 0 = 1 := rfl

lemma normalizedWallCoefficients_otherOutside (s : F.fullCones) (j : Fin n) (w : Lattice n)
    (hw : (F.fullConeBasis s).repr w j = -1) :
    F.normalizedWallCoefficients s w j.succ = 1 := by
  simp [normalizedWallCoefficients, hw]

lemma normalizedWallRelation (s : F.fullCones) (w : Lattice n) :
    ∑ i, F.normalizedWallCoefficients s w i • F.normalizedWallVectors s w i = 0 := by
  simp only [normalizedWallCoefficients, normalizedWallVectors, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, one_smul, neg_smul, Finset.sum_neg_distrib]
  rw [(F.fullConeBasis s).sum_repr]
  exact add_neg_cancel _

/-- No additional normalized relation is omitted: its coefficients are forced
by the actual basis coordinates of the outside ray. -/
theorem normalizedWallRelation_unique (s : F.fullCones) (w : Lattice n)
    (c : Fin (n+1) → ℤ) (hc0 : c 0 = 1)
    (hc : ∑ i, c i • F.normalizedWallVectors s w i = 0) :
    c = F.normalizedWallCoefficients s w := by
  have hs : w + ∑ i : Fin n, c i.succ • F.fullConeBasis s i = 0 := by
    simpa only [normalizedWallVectors, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, hc0, one_smul] using hc
  funext i
  refine Fin.cases hc0 (fun j => ?_) i
  have h := congrArg (fun x => (F.fullConeBasis s).repr x j) hs
  simp only [map_add, map_sum, map_smul, Finsupp.add_apply,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self_apply,
    map_zero, Finsupp.zero_apply, smul_eq_mul] at h
  have hsum : (∑ i : Fin n, c i.succ * (if i=j then (1:ℤ) else 0)) = c j.succ := by
    simp
  rw [hsum] at h
  change c j.succ = -(F.fullConeBasis s).repr w j
  omega

/-- The total absolute value of the negative coefficients is the positive
coordinate mass of the outside ray; this is an equality of actual sums. -/
theorem normalizedWall_negativeMass (s : F.fullCones) (w : Lattice n) :
    (∑ i, max (-(F.normalizedWallCoefficients s w i)) 0) =
      ∑ i, max ((F.fullConeBasis s).repr w i) 0 := by
  simp [normalizedWallCoefficients, Fin.sum_univ_succ]

lemma integerPairing_basis_expansion (b : Module.Basis (Fin n) ℤ (Lattice n))
    (w m : Lattice n) :
    integerPairing w m = ∑ i, b.repr w i * integerPairing (b i) m := by
  conv_lhs => rw [← b.sum_repr w]
  simp only [integerPairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum, mul_assoc]

lemma integerWallSlack_eq_normalizedRelation (a : Lattice n → ℤ)
    (s : F.fullCones) (w : Lattice n) :
    F.integerWallSlack a s w =
      ∑ i, F.normalizedWallCoefficients s w i * a (F.normalizedWallVectors s w i) := by
  change a w + integerPairing w (F.cartierLatticePoint a s) = _
  rw [integerPairing_basis_expansion (F.fullConeBasis s)]
  have hpair (i : Fin n) :
      integerPairing (F.fullConeBasis s i) (F.cartierLatticePoint a s) =
        -a (F.fullConeBasis s i) := by
    apply F.cartierLatticePoint_pairing a s
    rw [F.fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simp only [normalizedWallCoefficients, normalizedWallVectors, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, one_mul, hpair, mul_neg, neg_mul]


end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.integerWallSlack_eq_normalizedRelation
