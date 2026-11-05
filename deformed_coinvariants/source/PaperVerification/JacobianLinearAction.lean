module

public import PaperVerification.JacobianDefect
public import PaperVerification.JacobianHamiltonian
public import PaperVerification.JacobianParameter
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RepresentationTheory.Basic

/-!
# Naturality under arbitrary invertible linear changes of coordinates

The polynomial action is literal substitution by a matrix. Polynomial vector
fields transform by the inverse matrix. The chain rule proves contraction
naturality, while the conjugation formula for the Jacobian matrix proves
divergence naturality. These identities establish stability of the actual
Jacobian ideal, Hamiltonian relation space, and perturbed hit space.

A group representation on the coordinate space acts on polynomial functions
by substitution with the inverse matrix. The resulting representations on the
actual Milnor and Brieskorn quotients intertwine their quotient maps and the
potential action. Weight preservation is checked from the matrix entries.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.JacobianLinearAction

open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ

/-- The same matrix with its entries embedded as constant polynomials. -/
def polynomialMatrix (M : Matrix ι ι K) : Matrix ι ι P :=
  (C : K →+* P).mapMatrix M

@[simp] theorem polynomialMatrix_apply (M : Matrix ι ι K) (i j : ι) :
    polynomialMatrix M i j = C (M i j) := rfl

theorem polynomialMatrix_mul_inv (M : GL) :
    polynomialMatrix (M : Matrix ι ι K) * polynomialMatrix (M⁻¹ : GL) = 1 := by
  change (C : K →+* P).mapMatrix (M : Matrix ι ι K) *
    (C : K →+* P).mapMatrix (M⁻¹ : GL) = 1
  rw [← map_mul, Units.mul_inv, map_one]

/-- Invertibility is witnessed by substitution with the genuine inverse matrix. -/
def substitutionEquiv (M : GL) : P ≃ₐ[K] P :=
  AlgEquiv.ofAlgHom (linearSubst (M : Matrix ι ι K))
    (linearSubst (M⁻¹ : GL))
    (by rw [← linearSubst_mul, Units.inv_mul, linearSubst_one])
    (by rw [← linearSubst_mul, Units.mul_inv, linearSubst_one])

@[simp] theorem substitutionEquiv_apply (M : GL) (p : P) :
    substitutionEquiv M p = linearSubst (M : Matrix ι ι K) p := rfl

/-- The usual inverse-matrix transformation of a polynomial vector field. -/
def transformVectorField (M : GL) (g : ι → P) : ι → P :=
  polynomialMatrix (M⁻¹ : GL) *ᵥ fun i => linearSubst (M : Matrix ι ι K) (g i)

theorem gradient_linearSubst (M : Matrix ι ι K) (p : P) :
    gradient (linearSubst M p) =
      (polynomialMatrix M)ᵀ *ᵥ fun i => linearSubst M (gradient p i) := by
  funext j
  exact pderiv_linearSubst M j p

/-- Contraction transforms by the chain rule, without any hypothesis on `F`. -/
theorem coefficient_transform (M : GL) (F : P) (g : ι → P) :
    KoszulSyzygies.coefficient (gradient (linearSubst (M : Matrix ι ι K) F))
        (transformVectorField M g) =
      linearSubst (M : Matrix ι ι K) (KoszulSyzygies.coefficient (gradient F) g) := by
  change (polynomialMatrix (M⁻¹ : GL) *ᵥ
      (fun i => linearSubst (M : Matrix ι ι K) (g i))) ⬝ᵥ
      gradient (linearSubst (M : Matrix ι ι K) F) =
    linearSubst (M : Matrix ι ι K) (g ⬝ᵥ gradient F)
  rw [gradient_linearSubst, Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, polynomialMatrix_mul_inv, Matrix.one_mulVec,
    dotProduct_comm]
  exact (RingHom.map_dotProduct
    (linearSubst (M : Matrix ι ι K)).toRingHom g (gradient F)).symm

/-- Rows index vector-field components and columns index differentiations. -/
def derivativeMatrix (g : ι → P) : Matrix ι ι P :=
  Matrix.of fun i j => pderiv j (g i)

/-- The Jacobian matrix changes by conjugation with the actual coordinate matrix. -/
theorem derivativeMatrix_transform (M : GL) (g : ι → P) :
    derivativeMatrix (transformVectorField M g) =
      polynomialMatrix (M⁻¹ : GL) *
        (derivativeMatrix g).map (linearSubst (M : Matrix ι ι K)) *
          polynomialMatrix (M : Matrix ι ι K) := by
  funext r j
  change pderiv j
      (∑ i, C ((M⁻¹ : GL).val r i) * linearSubst (M : Matrix ι ι K) (g i)) =
    ∑ k, (∑ i, C ((M⁻¹ : GL).val r i) *
      linearSubst (M : Matrix ι ι K) (pderiv k (g i))) * C (M.val k j)
  rw [map_sum]
  simp_rw [pderiv_C_mul, pderiv_linearSubst, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Divergence is invariant under linear coordinate changes; this is a proved
trace identity, not an assumed invariance of the relation subspace. -/
theorem divergence_transform (M : GL) (g : ι → P) :
    divergence (transformVectorField M g) =
      linearSubst (M : Matrix ι ι K) (divergence g) := by
  change (derivativeMatrix (transformVectorField M g)).trace =
    linearSubst (M : Matrix ι ι K) (derivativeMatrix g).trace
  rw [derivativeMatrix_transform, Matrix.trace_mul_cycle,
    polynomialMatrix_mul_inv, one_mul]
  exact (AddMonoidHom.map_trace (linearSubst (M : Matrix ι ι K))
    (derivativeMatrix g)).symm

theorem transform_mem_tangent (M : GL) (F : P)
    (hF : linearSubst (M : Matrix ι ι K) F = F) (g : ι → P)
    (hg : g ∈ tangent F) : transformVectorField M g ∈ tangent F := by
  change KoszulSyzygies.coefficient (gradient F) (transformVectorField M g) = 0
  rw [← hF, coefficient_transform]
  have hz : KoszulSyzygies.coefficient (gradient F) g = 0 := hg
  rw [hz, map_zero]

theorem linearSubst_mem_divergenceSpace (M : GL) (F : P)
    (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P)
    (hp : p ∈ divergenceSpace F) :
    linearSubst (M : Matrix ι ι K) p ∈ divergenceSpace F := by
  obtain ⟨g, hg, rfl⟩ := hp
  exact ⟨transformVectorField M g, transform_mem_tangent M F hF g hg,
    divergence_transform M g⟩

theorem linearSubst_mem_jacobianSubmodule (M : GL) (F : P)
    (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P)
    (hp : p ∈ jacobianSubmodule F) :
    linearSubst (M : Matrix ι ι K) p ∈ jacobianSubmodule F := by
  rw [← coefficientMap_range] at hp ⊢
  obtain ⟨g, rfl⟩ := hp
  refine ⟨transformVectorField M g, ?_⟩
  change KoszulSyzygies.coefficient (gradient F) (transformVectorField M g) =
    linearSubst (M : Matrix ι ι K) (KoszulSyzygies.coefficient (gradient F) g)
  simpa only [hF] using coefficient_transform M F g

/-- Stability of the literal `i < j` Hamiltonian relation space follows from
its proved equality with the divergence presentation. -/
theorem linearSubst_mem_paper_relations {n : ℕ}
    (M : (Matrix (Fin n) (Fin n) K)ˣ) (F p : MvPolynomial (Fin n) K)
    (hF : linearSubst (M : Matrix (Fin n) (Fin n) K) F = F)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F))) (hp : p ∈ orderedHamiltonianSpace F) :
    linearSubst (M : Matrix (Fin n) (Fin n) K) p ∈ orderedHamiltonianSpace F := by
  rw [← divergenceSpace_eq_paper_relations F hreg] at hp ⊢
  exact linearSubst_mem_divergenceSpace M F hF p hp

theorem aggregateOperator_transform (M : GL) (F : P) (t : K) (g : ι → P) :
    aggregateOperator (linearSubst (M : Matrix ι ι K) F) t (transformVectorField M g) =
      linearSubst (M : Matrix ι ι K) (aggregateOperator F t g) := by
  change KoszulSyzygies.coefficient (gradient (linearSubst (M : Matrix ι ι K) F))
      (transformVectorField M g) +
      t • (linearSubst (M : Matrix ι ι K) F * divergence (transformVectorField M g)) =
    linearSubst (M : Matrix ι ι K)
      (KoszulSyzygies.coefficient (gradient F) g + t • (F * divergence g))
  rw [coefficient_transform, divergence_transform, map_add, map_smul, map_mul]

theorem linearSubst_mem_hit (M : GL) (F : P) (t : K)
    (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P)
    (hp : p ∈ EulerJacobian.hit (gradient F) F t) :
    linearSubst (M : Matrix ι ι K) p ∈ EulerJacobian.hit (gradient F) F t := by
  rw [← aggregate_range_eq_hit] at hp ⊢
  obtain ⟨g, rfl⟩ := hp
  refine ⟨transformVectorField M g, ?_⟩
  simpa only [hF] using aggregateOperator_transform M F t g

section Weights

variable {D : Type*} [AddCommMonoid D]

/-- A matrix preserves the prescribed grading exactly when each nonzero
entry mixes variables of the same weight. -/
def RespectsWeights (w : ι → D) (M : Matrix ι ι K) : Prop :=
  ∀ i j, M i j ≠ 0 → w i = w j

theorem coeff_linearSubst_X (M : Matrix ι ι K) (i j : ι) :
    (linearSubst M (X i : P)).coeff (Finsupp.single j 1) = M i j := by
  rw [linearSubst_X, coeff_sum]
  simp only [coeff_C_mul, coeff_X, Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0),
    mul_ite, mul_one, mul_zero]
  simp

theorem respectsWeights_comp {D' : Type*} (w : ι → D) (f : D → D')
    (M : Matrix ι ι K) (hM : RespectsWeights w M) :
    ∀ i j, M i j ≠ 0 → f (w i) = f (w j) :=
  fun i j hij => congrArg f (hM i j hij)

theorem linearSubst_weightedHomogeneous (M : Matrix ι ι K) (w : ι → D)
    (hM : RespectsWeights w M) {p : P} {d : D}
    (hp : p.IsWeightedHomogeneous w d) :
    (linearSubst M p).IsWeightedHomogeneous w d := by
  rw [linearSubst_eq_aeval]
  apply hp.aeval
  intro i
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j _
  by_cases hij : M i j = 0
  · rw [hij, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero K w _
  · rw [hM i j hij]
    exact (MvPolynomial.isWeightedHomogeneous_X K w j).C_mul (M i j)

/-- The matrix-entry condition is equivalent to preservation of the assigned
degree of every coordinate, so it adds no restriction to a weight-preserving
linear substitution. -/
theorem respectsWeights_iff_coordinates (M : Matrix ι ι K) (w : ι → D) :
    RespectsWeights w M ↔
      ∀ i, (linearSubst M (X i : P)).IsWeightedHomogeneous w (w i) := by
  constructor
  · intro hM i
    exact linearSubst_weightedHomogeneous M w hM (isWeightedHomogeneous_X K w i)
  · intro hM i j hij
    have hc : (linearSubst M (X i : P)).coeff (Finsupp.single j 1) ≠ 0 := by
      rwa [coeff_linearSubst_X]
    have hw := hM i hc
    simpa only [Finsupp.weight_single, one_smul] using hw.symm

/-- A weight-preserving substitution commutes with the actual homogeneous
projection, including on arbitrary inhomogeneous polynomials. -/
theorem linearSubst_weightedHomogeneousComponent (M : Matrix ι ι K) (w : ι → D)
    (hM : RespectsWeights w M) (p : P) (d : D) :
    linearSubst M (weightedHomogeneousComponent w d p) =
      weightedHomogeneousComponent w d (linearSubst M p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial a c =>
    have hm := isWeightedHomogeneous_monomial w a c rfl
    have hsm := linearSubst_weightedHomogeneous M w hM hm
    rw [weightedHomogeneousComponent_of_mem hm,
      weightedHomogeneousComponent_of_mem hsm]
    split_ifs <;> simp

end Weights

section GroupAction

variable {G : Type*} [Group G]

/-- The usual left action on polynomial functions: `g` substitutes `g⁻¹ x`. -/
def polynomialRepresentation (ρ : G →* GL) : Representation K G P where
  toFun g := (linearSubst (ρ g⁻¹ : Matrix ι ι K)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    change linearSubst (ρ ((1 : G)⁻¹) : Matrix ι ι K) p = p
    simp only [inv_one, map_one, Units.val_one, linearSubst_one, AlgHom.id_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    change linearSubst (ρ ((g * h)⁻¹) : Matrix ι ι K) p =
      linearSubst (ρ g⁻¹ : Matrix ι ι K) (linearSubst (ρ h⁻¹ : Matrix ι ι K) p)
    rw [_root_.mul_inv_rev, map_mul, Units.val_mul, linearSubst_mul_apply]

@[simp] theorem polynomialRepresentation_apply (ρ : G →* GL) (g : G) (p : P) :
    polynomialRepresentation ρ g p = linearSubst (ρ g⁻¹ : Matrix ι ι K) p := rfl

/-- The Milnor quotient action uses the actual Jacobian ideal and its proved stability. -/
def milnorRepresentation (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (MilnorQuotient F) :=
  (polynomialRepresentation ρ).quotient (jacobianSubmodule F)
    (fun g p hp => linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hF g⁻¹) p hp)

@[simp] theorem milnorRepresentation_mk (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (g : G) (p : P) :
    milnorRepresentation ρ F hF g ((jacobianSubmodule F).mkQ p) =
      (jacobianSubmodule F).mkQ (polynomialRepresentation ρ g p) := rfl

/-- The actual perturbed differential quotient carries the coordinate action. -/
def hitQuotientRepresentation (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (polynomialRepresentation ρ).quotient (EulerJacobian.hit (gradient F) F t)
    (fun g p hp => linearSubst_mem_hit (ρ g⁻¹) F t (hF g⁻¹) p hp)

@[simp] theorem hitQuotientRepresentation_mk (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (g : G) (p : P) :
    hitQuotientRepresentation ρ F t hF g
        ((EulerJacobian.hit (gradient F) F t).mkQ p) =
      (EulerJacobian.hit (gradient F) F t).mkQ (polynomialRepresentation ρ g p) := rfl

/-- Multiplication by the given invariant potential intertwines the actual
polynomial and hit-quotient actions. -/
theorem potentialToHitQuotient_intertwines (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (g : G) (p : P) :
    potentialToHitQuotient F t (polynomialRepresentation ρ g p) =
      hitQuotientRepresentation ρ F t hF g (potentialToHitQuotient F t p) := by
  change (EulerJacobian.hit (gradient F) F t).mkQ
      (F * linearSubst (ρ g⁻¹ : Matrix ι ι K) p) =
    hitQuotientRepresentation ρ F t hF g
      ((EulerJacobian.hit (gradient F) F t).mkQ (F * p))
  rw [hitQuotientRepresentation_mk]
  change (EulerJacobian.hit (gradient F) F t).mkQ
      (F * linearSubst (ρ g⁻¹ : Matrix ι ι K) p) =
    (EulerJacobian.hit (gradient F) F t).mkQ
      (linearSubst (ρ g⁻¹ : Matrix ι ι K) (F * p))
  rw [map_mul (linearSubst (ρ g⁻¹ : Matrix ι ι K)), hF]

theorem hitQuotientRepresentation_preserves_defect (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (g : G) (x : P ⧸ EulerJacobian.hit (gradient F) F t)
    (hx : x ∈ defectImage F t) :
    hitQuotientRepresentation ρ F t hF g x ∈ defectImage F t := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [hitQuotientRepresentation_mk]
  exact ⟨polynomialRepresentation ρ g p,
    linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hF g⁻¹) p hp, rfl⟩

/-- The defect action is the restriction of the actual quotient action to
the image of the actual Jacobian ideal. -/
def defectRepresentation (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (defectImage F t) :=
  (hitQuotientRepresentation ρ F t hF).subrepresentation (defectImage F t)
    (fun g x hx => hitQuotientRepresentation_preserves_defect ρ F t hF g x hx)

@[simp] theorem defectRepresentation_coe (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (g : G) (x : defectImage F t) :
    (defectRepresentation ρ F t hF g x).val =
      hitQuotientRepresentation ρ F t hF g x.val := rfl

/-- The divergence quotient action is obtained from the actual vector-field identity. -/
def brieskornQuotientRepresentation (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (BrieskornQuotient F) :=
  (polynomialRepresentation ρ).quotient (divergenceSpace F)
    (fun g p hp => linearSubst_mem_divergenceSpace (ρ g⁻¹) F (hF g⁻¹) p hp)

/-- The same action on the polynomial-module presentation of the Brieskorn quotient. -/
def brieskornRepresentation (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (BrieskornModule F) :=
  (Module.AEval'.of (potentialAction F)).conjRingEquiv.toMonoidHom.comp
    (brieskornQuotientRepresentation ρ F hF)

@[simp] theorem brieskornRepresentation_classOf (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (g : G) (p : P) :
    brieskornRepresentation ρ F hF g (classOf F p) =
      classOf F (polynomialRepresentation ρ g p) := rfl

theorem brieskornRepresentation_polynomial_smul (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (g : G) (q : Polynomial K) (x : BrieskornModule F) :
    brieskornRepresentation ρ F hF g (q • x) =
      q • brieskornRepresentation ρ F hF g x := by
  obtain ⟨p, rfl⟩ := classOf_surjective F x
  rw [polynomial_smul_classOf, brieskornRepresentation_classOf,
    brieskornRepresentation_classOf, polynomial_smul_classOf]
  congr 1
  change linearSubst (ρ g⁻¹ : Matrix ι ι K) (Polynomial.aeval F q * p) =
    Polynomial.aeval F q * linearSubst (ρ g⁻¹ : Matrix ι ι K) p
  rw [map_mul, ← Polynomial.aeval_algHom_apply, hF]

/-- The actual Milnor quotient map intertwines the two actual coordinate actions. -/
theorem milnorMap_intertwines {n : ℕ}
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ) (F : MvPolynomial (Fin n) K)
    (hF : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) F = F)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F))) (g : G) (x : BrieskornModule F) :
    milnorMap F hreg (brieskornRepresentation ρ F hF g x) =
      milnorRepresentation ρ F hF g (milnorMap F hreg x) := by
  obtain ⟨p, rfl⟩ := classOf_surjective F x
  rw [brieskornRepresentation_classOf, milnorMap_classOf,
    milnorMap_classOf, milnorRepresentation_mk]

theorem polynomialRepresentation_preserves_weights {D : Type*} [AddCommMonoid D]
    (ρ : G →* GL) (w : ι → D)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) {p : P} {d : D} (hp : p.IsWeightedHomogeneous w d) :
    (polynomialRepresentation ρ g p).IsWeightedHomogeneous w d :=
  linearSubst_weightedHomogeneous _ w (hW g⁻¹) hp

theorem milnorRepresentation_preserves_pieces {D : Type*} [AddCommMonoid D]
    (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (w : ι → D) (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (d : D) (x : MilnorQuotient F)
    (hx : x ∈ (weightedHomogeneousSubmodule K w d).map (jacobianSubmodule F).mkQ) :
    milnorRepresentation ρ F hF g x ∈
      (weightedHomogeneousSubmodule K w d).map (jacobianSubmodule F).mkQ := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨polynomialRepresentation ρ g p,
    polynomialRepresentation_preserves_weights ρ w hW g hp,
    (milnorRepresentation_mk ρ F hF g p).symm⟩

theorem brieskornRepresentation_preserves_pieces {D : Type*} [AddCommMonoid D]
    (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (w : ι → D) (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (d : D) (x : BrieskornModule F)
    (hx : x ∈ (weightedHomogeneousSubmodule K w d).map (classOf F)) :
    brieskornRepresentation ρ F hF g x ∈
      (weightedHomogeneousSubmodule K w d).map (classOf F) := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨polynomialRepresentation ρ g p,
    polynomialRepresentation_preserves_weights ρ w hW g hp,
    (brieskornRepresentation_classOf ρ F hF g p).symm⟩

end GroupAction

end PaperVerification.JacobianLinearAction
