module

public import PaperVerification.FermionColorAssociatedGraded
public import PaperVerification.FermionColorGeneralFibers
public import PaperVerification.FermionCoefficientHilbert
public import Mathlib.LinearAlgebra.Pi

/-!
# The complete algebraic and equivariant statement of Theorem 8.1

The source is the original strict type-A moment quotient. The filtration,
its successive quotient spaces, the Rees subalgebra, both algebra fibers,
and the independent exterior tensor representations are defined before
this theorem. Multiplication is specified on a proved spanning family of
all polynomial/exterior pure tensors, using the original polynomial and
exterior products. No ring structure or action is transported to make the
conclusion true. The actual invariant-generated wreath quotient is a separate
specialization in Section 8.1; it is not an extra hypothesis here.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct DirectSum
  PaperVerification.Fermion.WeightRees

namespace PaperVerification.Fermion.TypeA

open MvPolynomial Exterior

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

local instance theoremEightOneOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- All multiplicity blocks, including the proved-zero inadmissible blocks,
are retained before taking the finite admissible direct sum. -/
def naturalAssociatedFunctionEquiv (hn : 0<n) :
    StrictMultiplicityAssociatedGraded (data (F := F) hn) ≃ₗ[F]
      ((m : MultiplicityVector n) → ExteriorCoefficientBlock (F := F) m) :=
  (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).toLinearEquiv.trans
    (naturalInitialFunctionEquiv hn)

/-- The class of an actual polynomial/exterior pure tensor in the actual
associated graded. Its original representative is proved below. -/
def gradedPureTensor (hn : 0<n) (m : MultiplicityVector n)
    (p : PolynomialRing F n) (x : ColorPaths.ExteriorColorTensor F m) :
    StrictMultiplicityAssociatedGraded (data (F := F) hn) :=
  (naturalAssociatedFunctionEquiv hn).symm
    (Pi.single m (Ideal.Quotient.mk (coefficientIdeal m) p ⊗ₜ[F] x))

private theorem algEquiv_apply_linear_symm {A B : Type*}
    [Ring A] [Ring B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (y : B) : e (e.toLinearEquiv.symm y)=y := by
  exact e.apply_symm_apply y

set_option maxRecDepth 2048 in
theorem gradedPureTensor_original (hn : 0<n) (m : MultiplicityVector n)
    (p : PolynomialRing F n) (x : ColorPaths.ExteriorColorTensor F m) :
    strictMultiplicityAssociatedGradedEquiv (data (F := F) hn) (gradedPureTensor hn m p x)=
      strictInitialProjection (data (F := F) hn)
        (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x) := by
  simp only [gradedPureTensor,naturalAssociatedFunctionEquiv,
    LinearEquiv.trans_symm,LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_symm,
    AlgEquiv.toLinearEquiv_apply,AlgEquiv.apply_symm_apply]
  have hcancel := algEquiv_apply_linear_symm
    (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn))
      ((naturalInitialFunctionEquiv hn).symm
        (Pi.single m (Ideal.Quotient.mk (coefficientIdeal m) p ⊗ₜ[F] x)))
  exact hcancel.trans (naturalInitialFunctionEquiv_symm_tmul hn m p x)

set_option maxRecDepth 2048 in
/-- These representatives span the entire associated graded, so the next
product formula determines every product, not merely selected examples. -/
theorem gradedPureTensor_span (hn : 0<n) :
    Submodule.span F (Set.range (fun z :
      Σ m : MultiplicityVector n,PolynomialRing F n × ColorPaths.ExteriorColorTensor F m ↦
        gradedPureTensor hn z.1 z.2.1 z.2.2))=⊤ := by
  let S := Submodule.span F (Set.range (fun z :
    Σ m : MultiplicityVector n,PolynomialRing F n × ColorPaths.ExteriorColorTensor F m ↦
      gradedPureTensor hn z.1 z.2.1 z.2.2))
  let e := naturalAssociatedFunctionEquiv (F := F) hn
  have hsingle (m : MultiplicityVector n) (z : ExteriorCoefficientBlock (F := F) m) :
      e.symm (Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m z)∈S := by
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [Pi.single_zero,e.symm.map_zero]
        exact S.zero_mem
    | add z w hz hw =>
        have hs : Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m (z+w)=Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m z+Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m w := by
          rw [Pi.single_add]
        have ha := e.symm.toLinearMap.map_add (Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m z) (Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m w)
        have hm := S.add_mem hz hw
        exact ((congrArg e.symm hs).trans ha).symm ▸ hm
    | tmul c x =>
        obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
        have hm : gradedPureTensor hn m p x∈S :=
          Submodule.subset_span (R := F) ⟨⟨m,p,x⟩,rfl⟩
        exact hm
  apply top_unique
  intro x hx
  change x∈S
  have hsum := map_sum e.symm.toLinearMap
    (fun m : MultiplicityVector n ↦ Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m (e x m)) Finset.univ
  have he : x=∑ m : MultiplicityVector n,e.symm (Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m (e x m)) := by
    calc
      x=e.symm (∑ m : MultiplicityVector n,Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m (e x m)) := by
        rw [Finset.univ_sum_single,e.symm_apply_apply]
      _=∑ m : MultiplicityVector n,e.symm (Pi.single (M := fun m : MultiplicityVector n ↦ ExteriorCoefficientBlock (F := F) m) m (e x m)) := hsum
  rw [he]
  exact S.sum_mem (fun m _ ↦ hsingle m (e x m))

/-- Bilinearity and the proved spanning family make the pure-product formula
an exact specification of the whole multiplication. In particular, changing
coordinates to the displayed tensor blocks cannot conceal a different product. -/
theorem gradedPureTensor_mul_unique (hn : 0<n)
    (μ ν : StrictMultiplicityAssociatedGraded (data (F := F) hn) →ₗ[F]
      StrictMultiplicityAssociatedGraded (data (F := F) hn) →ₗ[F]
        StrictMultiplicityAssociatedGraded (data (F := F) hn))
    (h : ∀ (m l : MultiplicityVector n) (p q : PolynomialRing F n)
      (x : ColorPaths.ExteriorColorTensor F m) (y : ColorPaths.ExteriorColorTensor F l),
      μ (gradedPureTensor hn m p x) (gradedPureTensor hn l q y)=
        ν (gradedPureTensor hn m p x) (gradedPureTensor hn l q y)) : μ=ν := by
  apply LinearMap.ext_on_range (gradedPureTensor_span hn)
  intro z
  apply LinearMap.ext_on_range (gradedPureTensor_span hn)
  intro w
  exact h z.1 w.1 z.2.1 w.2.1 z.2.2 w.2.2

/-- The full multiplication is induced by the original polynomial and
exterior products, including every shuffle sign and every vanishing product. -/
theorem gradedPureTensor_mul (hn : 0<n) (m l : MultiplicityVector n)
    (p q : PolynomialRing F n)
    (x : ColorPaths.ExteriorColorTensor F m) (y : ColorPaths.ExteriorColorTensor F l) :
    gradedPureTensor hn m p x*gradedPureTensor hn l q y=
      (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
        (strictInitialProjection (data (F := F) hn)
          ((p*q) ⊗ₜ[F] (NaturalColor.assemble (fun i ↦ (m i).val) x*
            NaturalColor.assemble (fun i ↦ (l i).val) y))) := by
  apply (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).injective
  rw [map_mul,AlgEquiv.apply_symm_apply,gradedPureTensor_original,
    gradedPureTensor_original,←map_mul,Algebra.TensorProduct.tmul_mul_tmul]

section ZeroFiber

local instance theoremEightOneZeroEvaluation : Algebra (Polynomial F) F :=
  (Polynomial.evalRingHom (0 : F)).toAlgebra

/-- The zero fiber is the independently constructed actual associated graded
as an algebra, not only as an equal-dimensional module. -/
def zeroFiberAssociatedEquiv (hn : 0<n) :
    F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictMultiplicityAssociatedGraded (data (F := F) hn) :=
  (strictMultiplicityFiberZero (data (F := F) hn)).trans
    (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm

set_option maxHeartbeats 1000000 in
theorem zeroFiberAssociatedEquiv_intertwines (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)) :
    zeroFiberAssociatedEquiv hn
      (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
      gradedColorAction hn g (zeroFiberAssociatedEquiv hn z) := by
  apply (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).injective
  simp only [zeroFiberAssociatedEquiv,AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply]
  rw [multiplicityAssociatedGraded_color_equivariant,
    AlgEquiv.apply_symm_apply,fiberZero_color_equivariant]

end ZeroFiber

set_option maxHeartbeats 1000000 in
/-- The complete printed claim, with the exact independently defined maps.
The coefficient formula quantifies over every original polynomial/exterior
word; the degree formula retains every polynomial degree. -/
structure TheoremEightOneClaim (hn : 0<n) : Prop where
  initial_coefficients : ∀ z : SuperRing F n,z∈initialIdeal hn ↔
    ∀ T,(superPolynomialBasis (K := F)).repr z T∈coefficientIdeal (wordMultiplicityVector T)
  inadmissible_blocks : ∀ m : MultiplicityVector n,¬Admissible m →
    coefficientIdeal (F := F) m=⊤
  coefficient_hilbert : ∀ (m : MultiplicityVector n),Admissible m → ∀ k : ℕ,
    (Module.finrank F (coefficientPolynomialPiece (F := F) m k) : F)=
      (ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k
  actual_filtration : ∀ r : ℕ,
    (strictMultiplicityDescendingFiltration (data (F := F) hn)).piece r=
      strictMultiplicityFiltration (data (F := F) hn) r
  actual_rees : ∀ z : LaurentPolynomial
      (StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)),
    z∈StrictMultiplicityRees (data (F := F) hn) ↔
      ∀ e,z.coeff e∈strictMultiplicityFiltration (data (F := F) hn) (-e).toNat
  finite_free_flat :
    Module.Finite (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧
    Module.Free (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧
    Module.Flat (Polynomial F) (StrictMultiplicityRees (data (F := F) hn))
  family_color_coefficients : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : StrictMultiplicityRees (data (F := F) hn)) (r : ℤ),
    (reesColorAction hn g z).val.coeff r=
      ColorAction.quotientEquiv g (fun i ↦ X i)
        (z.val.coeff r)
  zero_fiber :
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (0 : F)).toAlgebra
    Nonempty (F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictMultiplicityAssociatedGraded (data (F := F) hn)) ∧
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)),
      zeroFiberAssociatedEquiv hn
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        gradedColorAction hn g (zeroFiberAssociatedEquiv hn z)
  unit_fiber :
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (1 : F)).toAlgebra
    Nonempty (F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)) ∧
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)),
      strictMultiplicityFiberOne (data (F := F) hn)
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        ColorAction.quotientEquiv g (fun i ↦ X i) (strictMultiplicityFiberOne (data (F := F) hn) z)
  nonzero_fibers : ∀ (c : F) (hc : c≠0),
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom c).toAlgebra
    Nonempty (F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn) ≃ₐ[F]
      StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i)) ∧
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (z : F ⊗[Polynomial F] StrictMultiplicityRees (data (F := F) hn)),
      nonzeroFiberEquiv hn c hc
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (reesColorAction hn g) z)=
        ColorAction.quotientEquiv g (fun i ↦ X i) (nonzeroFiberEquiv hn c hc z)
  graded_initial_algebra : Nonempty
    (StrictMultiplicityAssociatedGraded (data (F := F) hn) ≃ₐ[F]
      StrictMultiplicityInitialQuotient (data (F := F) hn))
  graded_exterior_blocks : Nonempty
    (StrictMultiplicityAssociatedGraded (data (F := F) hn) ≃ₗ[F]
      ⨁ m : {m : MultiplicityVector n // Admissible m},
        ExteriorCoefficientBlock (F := F) m.val)
  graded_color_equivariance : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) F)
      (x : StrictMultiplicityAssociatedGraded (data (F := F) hn)),
    naturalAssociatedGradedEquiv hn (gradedColorAction hn g x)=
      naturalAdmissibleRepresentation (fun _ ↦ g) (naturalAssociatedGradedEquiv hn x)
  independent_color_representatives :
    ∀ (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F) (z : SuperRing F n),
      ColorAction.initialQuotientAction (data (F := F) hn) g (strictInitialProjection (data (F := F) hn) z)=
        strictInitialProjection (data (F := F) hn) (ColorAction.indexAmbient (fun i ↦ (g i).val) z)
  independent_color_equivariance :
    ∀ (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
      (x : StrictMultiplicityInitialQuotient (data (F := F) hn)),
      naturalInitialAdmissibleEquiv hn (ColorAction.initialQuotientAction (data (F := F) hn) g x)=
        naturalAdmissibleRepresentation g (naturalInitialAdmissibleEquiv hn x)
  products_span : Submodule.span F (Set.range (fun z :
    Σ m : MultiplicityVector n,PolynomialRing F n × ColorPaths.ExteriorColorTensor F m ↦
      gradedPureTensor hn z.1 z.2.1 z.2.2))=⊤
  original_products : ∀ (m l : MultiplicityVector n) (p q : PolynomialRing F n)
      (x : ColorPaths.ExteriorColorTensor F m) (y : ColorPaths.ExteriorColorTensor F l),
    gradedPureTensor hn m p x*gradedPureTensor hn l q y=
      (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
        (strictInitialProjection (data (F := F) hn)
          ((p*q) ⊗ₜ[F] (NaturalColor.assemble (fun i ↦ (m i).val) x*
            NaturalColor.assemble (fun i ↦ (l i).val) y)))

end PaperVerification.Fermion.TypeA

namespace PaperVerification.Fermion

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

set_option maxRecDepth 2048 in
/-- Theorem8.1 in full: actual smallest initial ideal, coefficient Hilbert
polynomials, equivariant finite-free flat degeneration, actual associated
graded, natural exterior tensor blocks and their complete multiplication.
Specializing F=Complex gives the paper's exact coefficient field. -/
theorem theorem_8_1 (hn : 0<n) : TypeA.TheoremEightOneClaim (F := F) hn where
  initial_coefficients := TypeA.equation_21 hn
  inadmissible_blocks := TypeA.inadmissible_coefficientIdeal_eq_top hn
  coefficient_hilbert := TypeA.coefficientPolynomialPiece_finrank hn
  actual_filtration := strictMultiplicityDescendingFiltration_piece (TypeA.data (F := F) hn)
  actual_rees := strictMultiplicityRees_mem_iff (TypeA.data (F := F) hn)
  finite_free_flat := TypeA.colorRees_finite_free_flat hn
  family_color_coefficients := TypeA.reesColorAction_coeff hn
  zero_fiber := by
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (0 : F)).toAlgebra
    exact ⟨⟨TypeA.zeroFiberAssociatedEquiv (F := F) hn⟩,
      TypeA.zeroFiberAssociatedEquiv_intertwines (F := F) hn⟩
  unit_fiber := by
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom (1 : F)).toAlgebra
    exact ⟨⟨strictMultiplicityFiberOne (TypeA.data (F := F) hn)⟩,
      TypeA.fiberOne_color_equivariant (F := F) hn⟩
  nonzero_fibers := by
    intro c hc
    letI : Algebra (Polynomial F) F := (Polynomial.evalRingHom c).toAlgebra
    exact ⟨⟨TypeA.nonzeroFiberEquiv (F := F) hn c hc⟩,
      TypeA.nonzeroFiberEquiv_intertwines (F := F) hn c hc⟩
  graded_initial_algebra := ⟨strictMultiplicityAssociatedGradedEquiv (TypeA.data (F := F) hn)⟩
  graded_exterior_blocks := ⟨TypeA.naturalAssociatedGradedEquiv hn⟩
  graded_color_equivariance := TypeA.naturalAssociatedGradedEquiv_intertwines hn
  independent_color_representatives := fun g z ↦
    ColorAction.initialQuotientEquiv_mk g (TypeA.data (F := F) hn) z
  independent_color_equivariance := TypeA.naturalInitialAdmissibleEquiv_intertwines hn
  products_span := TypeA.gradedPureTensor_span hn
  original_products := TypeA.gradedPureTensor_mul hn

end PaperVerification.Fermion
