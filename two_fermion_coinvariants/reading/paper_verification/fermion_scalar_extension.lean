module

public import PaperVerification.FermionPairedPrefix
public import PaperVerification.FermionGaussRankOne

/-!
# Scalar extension of the literal exterior equations

The map below sends each exterior basis word to the identical word over a new
coefficient ring. Its semilinearity, coordinate formula, and compatibility with
creation and contraction are proved explicitly. This allows polynomial scalar
extension without inferring polynomial identities from their values on a field.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

section Coordinates

variable {R S V W J : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    [Fintype J] [LinearOrder J]

variable (b : Module.Basis J R V) (b' : Module.Basis J S W) (f : R →+* S)

/-- Extension of coefficients in the genuine exterior bases. -/
def exteriorScalarExtension : ExteriorAlgebra R V →ₛₗ[f] ExteriorAlgebra S W where
  toFun w := ∑ T : Finset J, f (b.ExteriorAlgebra.repr w T) • b'.ExteriorAlgebra T
  map_add' x y := by
    simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      mul_smul, Finset.smul_sum]

@[simp] theorem exteriorScalarExtension_basis (T : Finset J) :
    exteriorScalarExtension b b' f (b.ExteriorAlgebra T) = b'.ExteriorAlgebra T := by
  simp [exteriorScalarExtension, Module.Basis.repr_self, Finsupp.single_apply]

@[simp] theorem exteriorScalarExtension_coord (w : ExteriorAlgebra R V) (T : Finset J) :
    b'.ExteriorAlgebra.repr (exteriorScalarExtension b b' f w) T =
      f (b.ExteriorAlgebra.repr w T) := by
  simp [exteriorScalarExtension, Module.Basis.repr_self, Finsupp.single_apply]

theorem exteriorScalarExtension_injective (hf : Function.Injective f) :
    Function.Injective (exteriorScalarExtension b b' f) := by
  intro x y h
  apply b.ExteriorAlgebra.repr.injective
  ext T
  apply hf
  simpa only [exteriorScalarExtension_coord] using
    congrArg (fun w ↦ b'.ExteriorAlgebra.repr w T) h

/-- Creation by a basis vector commutes with coefficient extension. The signs
are the actual exterior shuffle signs, including in characteristic two. -/
theorem exteriorScalarExtension_creation (i : J) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (creation (b i) w) =
      creation (b' i) (exteriorScalarExtension b b' f w) := by
  have h : (exteriorScalarExtension b b' f).comp (creation (b i)) =
      (creation (b' i)).comp (exteriorScalarExtension b b' f) := by
    apply b.ExteriorAlgebra.ext
    intro T
    simp only [LinearMap.comp_apply, exteriorScalarExtension_basis, creation_apply,
      TauCeti.ExteriorAlgebra.ι_mul_basis]
    split_ifs <;> simp only [map_zero, map_zsmul_unit, exteriorScalarExtension_basis]
  exact LinearMap.congr_fun h w

/-- Coordinate contraction commutes with coefficient extension. -/
theorem exteriorScalarExtension_annihilation (i : J) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (annihilation (b.coord i) w) =
      annihilation (b'.coord i) (exteriorScalarExtension b b' f w) := by
  have h : (exteriorScalarExtension b b' f).comp (annihilation (b.coord i)) =
      (annihilation (b'.coord i)).comp (exteriorScalarExtension b b' f) := by
    apply b.ExteriorAlgebra.ext
    intro T
    simp only [LinearMap.comp_apply, exteriorScalarExtension_basis, annihilation,
      TauCeti.ExteriorAlgebra.contractLeft_coord_basis]
    split_ifs <;> simp only [map_zero, map_zsmul_unit, exteriorScalarExtension_basis]
  exact LinearMap.congr_fun h w

/-- Genuine homogeneous exterior degree is preserved by scalar extension. -/
theorem exteriorScalarExtension_mem {k : ℕ} {w : ExteriorAlgebra R V}
    (hw : w ∈ ⋀[R]^k V) : exteriorScalarExtension b b' f w ∈ ⋀[S]^k W := by
  apply Submodule.sum_mem
  intro T hT
  by_cases hc : T.card = k
  · exact Submodule.smul_mem _ _ (hc ▸ exterior_basis_mem b' T)
  · rw [exterior_coefficient_eq_zero_of_card_ne b T hw hc, map_zero, zero_smul]
    exact zero_mem _

theorem exteriorScalarExtension_projection (k : ℕ) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (exteriorDegreeProjection k w) =
      exteriorDegreeProjection k (exteriorScalarExtension b b' f w) := by
  have h : (exteriorScalarExtension b b' f).comp (exteriorDegreeProjection k) =
      (exteriorDegreeProjection k).comp (exteriorScalarExtension b b' f) := by
    apply b.ExteriorAlgebra.ext
    intro T
    simp only [LinearMap.comp_apply, exteriorScalarExtension_basis]
    by_cases hT : T.card = k
    · simp only [exteriorDegreeProjection_self (hT ▸ exterior_basis_mem b T),
        exteriorDegreeProjection_self (hT ▸ exterior_basis_mem b' T),
        exteriorScalarExtension_basis]
    · simp only [exteriorDegreeProjection_zero (exterior_basis_mem b T) hT,
        exteriorDegreeProjection_zero (exterior_basis_mem b' T) hT, map_zero]
  exact LinearMap.congr_fun h w

end Coordinates

section Paired

variable {R S V W I : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]

variable (b : Module.Basis (I ⊕ I) R V) (b' : Module.Basis (I ⊕ I) S W)
    (f : R →+* S)

theorem exteriorScalarExtension_pairLower (i : I) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (pairLower b i w) =
      pairLower b' i (exteriorScalarExtension b b' f w) := by
  simp only [pairLower, Module.End.mul_apply, exteriorScalarExtension_annihilation]

theorem exteriorScalarExtension_pairRaise (i : I) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (pairRaise b i w) =
      pairRaise b' i (exteriorScalarExtension b b' f w) := by
  simp only [pairRaise, Module.End.mul_apply, exteriorScalarExtension_creation]

theorem exteriorScalarExtension_elementary (l : List I) (j : ℕ)
    (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (elementaryOperator (l.map (pairRaise b)) j w) =
      elementaryOperator (l.map (pairRaise b')) j (exteriorScalarExtension b b' f w) := by
  induction l generalizing j with
  | nil => cases j <;> simp [elementaryOperator]
  | cons i l ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.map_cons, elementaryOperator, LinearMap.add_apply,
        Module.End.mul_apply, map_add, ih, exteriorScalarExtension_pairRaise]

theorem exteriorScalarExtension_lowerProduct (l : List I) (y : I → R)
    (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f
        ((l.map fun i ↦ 1 + y i • pairLower b i).prod w) =
      (l.map fun i ↦ 1 + f (y i) • pairLower b' i).prod
        (exteriorScalarExtension b b' f w) := by
  induction l generalizing w with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, LinearMap.map_smulₛₗ, exteriorScalarExtension_pairLower, ih]

theorem exteriorScalarExtension_diagonalGaussCoefficient (y : I → R)
    (k : ℕ) (w : ExteriorAlgebra R V) (j : ℕ) :
    diagonalGaussCoefficient b' (f ∘ y) k (exteriorScalarExtension b b' f w) j =
      exteriorScalarExtension b b' f (diagonalGaussCoefficient b y k w j) := by
  simp only [diagonalGaussCoefficient, exteriorScalarExtension_projection,
    exteriorScalarExtension_lowerProduct, exteriorScalarExtension_elementary,
    Function.comp_apply]

theorem exteriorScalarExtension_thetaDual (a : I → R) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (annihilation (rankOneThetaDual b a) w) =
      annihilation (rankOneThetaDual b' (f ∘ a)) (exteriorScalarExtension b b' f w) := by
  simp only [rankOneThetaDual, annihilation, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact exteriorScalarExtension_annihilation b b' f (.inl i) w

theorem exteriorScalarExtension_xiDual (a : I → R) (w : ExteriorAlgebra R V) :
    exteriorScalarExtension b b' f (annihilation (rankOneXiDual b a) w) =
      annihilation (rankOneXiDual b' (f ∘ a)) (exteriorScalarExtension b b' f w) := by
  simp only [rankOneXiDual, annihilation, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact exteriorScalarExtension_annihilation b b' f (.inr i) w

theorem exteriorScalarExtension_diagonalRankOneCoefficient (y U a : I → R)
    (u : R) (k : ℕ) (w : ExteriorAlgebra R V) (j : ℕ) :
    diagonalRankOneCoefficient b' (f ∘ y) (f ∘ U) (f ∘ a) (f u) k
        (exteriorScalarExtension b b' f w) j =
      exteriorScalarExtension b b' f (diagonalRankOneCoefficient b y U a u k w j) := by
  simp only [diagonalRankOneCoefficient, exteriorScalarExtension_projection,
    exteriorScalarExtension_xiDual, exteriorScalarExtension_thetaDual,
    exteriorScalarExtension_lowerProduct, exteriorScalarExtension_elementary,
    map_mul, Function.comp_apply]

/-- All polynomial mixed equations survive arbitrary scalar extension. The
target polynomial may have new coefficients; it need not be the image of a
polynomial over the source ring. -/
theorem exteriorScalarExtension_mixed (y : I → R) (w : ExteriorAlgebra R V)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (p : Polynomial S) :
    (∑ i, p.eval (f (y i)) • pairLower b' i) (exteriorScalarExtension b b' f w) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, add_smul, Finset.sum_add_distrib,
      LinearMap.add_apply, hp, hq, add_zero]
  | monomial k a =>
    have h := congrArg (exteriorScalarExtension b b' f) (hw (Polynomial.X ^ k))
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      LinearMap.map_smulₛₗ, Polynomial.eval_pow, Polynomial.eval_X, map_pow,
      exteriorScalarExtension_pairLower, map_zero] at h
    simp only [Polynomial.eval_monomial, LinearMap.sum_apply,
      LinearMap.smul_apply, mul_smul, ← Finset.smul_sum, h, smul_zero]

/-- The same coefficient-extension argument for an arbitrary family of odd
coordinate contractions. It is used for both colours of the odd moments. -/
theorem exteriorScalarExtension_odd (indices : I → I ⊕ I) (y a : I → R)
    (w : ExteriorAlgebra R V)
    (hw : ∀ p : Polynomial R,
      (∑ i, (a i * p.eval (y i)) • annihilation (b.coord (indices i))) w = 0)
    (p : Polynomial S) :
    (∑ i, (f (a i) * p.eval (f (y i))) • annihilation (b'.coord (indices i)))
      (exteriorScalarExtension b b' f w) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, mul_add, add_smul, Finset.sum_add_distrib,
      LinearMap.add_apply, hp, hq, add_zero]
  | monomial k c =>
    have h := congrArg (exteriorScalarExtension b b' f) (hw (Polynomial.X ^ k))
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      LinearMap.map_smulₛₗ, Polynomial.eval_pow, Polynomial.eval_X, map_pow, map_mul,
      exteriorScalarExtension_annihilation, map_zero] at h
    simp only [Polynomial.eval_monomial, LinearMap.sum_apply, LinearMap.smul_apply]
    calc
      _ = c • (∑ i, (f (a i) * f (y i) ^ k) •
          annihilation (b'.coord (indices i)) (exteriorScalarExtension b b' f w)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        ring
      _ = 0 := by rw [h, smul_zero]

end Paired

end PaperVerification.Fermion.Exterior
