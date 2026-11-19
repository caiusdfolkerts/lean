module
public import Lean.Elab.Command
public import Mathlib
@[expose] public section
-- Match the retained source's general polynomial-module constructor.
attribute [-instance] MvPolynomial.instModuleSelf
example {K V : Type*} [Field K] :
    (inferInstance : Module K (MvPolynomial V K)) = MvPolynomial.instModuleSelf := rfl

/-!
# Singular-vector spans beyond boundary format

The full main rank, defect and tensor-span theorems and their substantive
corollaries, with the literal symmetric-power quotient, ordinary tensor
products, projective spans, every field characteristic, and every printed
format and excess range. These definitions copy the substantive development;
no generic rank or reducedness premise is introduced as a substitute proof.
-/
noncomputable section
set_option maxHeartbeats 0
namespace PaperVerification.Segre.ActualQuotient end PaperVerification.Segre.ActualQuotient
namespace PaperVerification.Segre.ActualTensorSpan end PaperVerification.Segre.ActualTensorSpan
namespace PaperVerification.Segre.Artinian end PaperVerification.Segre.Artinian
namespace PaperVerification.Segre.Balanced end PaperVerification.Segre.Balanced
namespace PaperVerification.Segre.BooleanBase end PaperVerification.Segre.BooleanBase
namespace PaperVerification.Segre.ChainClassification end PaperVerification.Segre.ChainClassification
namespace PaperVerification.Segre.ChainInduction end PaperVerification.Segre.ChainInduction
namespace PaperVerification.Segre.CoreAttachment end PaperVerification.Segre.CoreAttachment
namespace PaperVerification.Segre.CriticalChartReindex end PaperVerification.Segre.CriticalChartReindex
namespace PaperVerification.Segre.CriticalGraph end PaperVerification.Segre.CriticalGraph
namespace PaperVerification.Segre.Degeneration end PaperVerification.Segre.Degeneration
namespace PaperVerification.Segre.DiagonalBoxNeighbors end PaperVerification.Segre.DiagonalBoxNeighbors
namespace PaperVerification.Segre.DiagonalCore end PaperVerification.Segre.DiagonalCore
namespace PaperVerification.Segre.ExcessPropagation end PaperVerification.Segre.ExcessPropagation
namespace PaperVerification.Segre.FixedLefschetzRanks end PaperVerification.Segre.FixedLefschetzRanks
namespace PaperVerification.Segre.FullGraphChartReindex end PaperVerification.Segre.FullGraphChartReindex
namespace PaperVerification.Segre.GenericFirstLefschetz end PaperVerification.Segre.GenericFirstLefschetz
namespace PaperVerification.Segre.GenericRigidity end PaperVerification.Segre.GenericRigidity
namespace PaperVerification.Segre.GenericSurjectivity end PaperVerification.Segre.GenericSurjectivity
namespace PaperVerification.Segre.GraphCriticalElimination end PaperVerification.Segre.GraphCriticalElimination
namespace PaperVerification.Segre.GraphKernel end PaperVerification.Segre.GraphKernel
namespace PaperVerification.Segre.GraphQuotientElimination end PaperVerification.Segre.GraphQuotientElimination
namespace PaperVerification.Segre.GraphSpan end PaperVerification.Segre.GraphSpan
namespace PaperVerification.Segre.HigherPieces end PaperVerification.Segre.HigherPieces
namespace PaperVerification.Segre.KoszulDimension end PaperVerification.Segre.KoszulDimension
namespace PaperVerification.Segre.Monomials end PaperVerification.Segre.Monomials
namespace PaperVerification.Segre.ProjectiveCharts end PaperVerification.Segre.ProjectiveCharts
namespace PaperVerification.Segre.ProjectivePointSpan end PaperVerification.Segre.ProjectivePointSpan
namespace PaperVerification.Segre.RankParameters end PaperVerification.Segre.RankParameters
namespace PaperVerification.Segre.RigidityRank end PaperVerification.Segre.RigidityRank
namespace PaperVerification.Segre.SingularSpan end PaperVerification.Segre.SingularSpan
namespace PaperVerification.Segre.Staircase end PaperVerification.Segre.Staircase
namespace PaperVerification.Segre.StressFree end PaperVerification.Segre.StressFree
namespace PaperVerification.Segre.SymmetricRealization end PaperVerification.Segre.SymmetricRealization
namespace PaperVerification.Segre.TensorFactorReindex end PaperVerification.Segre.TensorFactorReindex
namespace PaperVerification.Segre.ThreeChainCores end PaperVerification.Segre.ThreeChainCores
namespace PaperVerification.Segre.TwoFactorActual end PaperVerification.Segre.TwoFactorActual
namespace PaperVerification.Segre.TwoFactorOneDimension end PaperVerification.Segre.TwoFactorOneDimension
namespace PaperVerification.Segre.TwoFactorPropagation end PaperVerification.Segre.TwoFactorPropagation
namespace PaperVerification.Segre.TwoFactorTranspose end PaperVerification.Segre.TwoFactorTranspose
namespace TauCeti.AlgebraicGeometry end TauCeti.AlgebraicGeometry
namespace TauCeti.CategoryTheory end TauCeti.CategoryTheory
namespace PaperVerification.Segre.Staircase section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false variable {I : Type*} [Fintype I]
/-- Exact source definition of Cell. -/
abbrev Cell (n : I → ℕ) := ∀ i, Fin (n i + 1)
/-- Exact source definition of rank. -/
def rank {n : I → ℕ} (u : Cell n) : ℕ := ∑ i, (u i).val
/-- Exact source definition of sideSum. -/
def sideSum (n : I → ℕ) : ℕ := ∑ i, n i
/-- Exact source definition of weight. -/
def weight {n : I → ℕ} (u : Cell n) : ℕ := rank u * (sideSum n - rank u)
end end PaperVerification.Segre.Staircase
namespace PaperVerification.Segre.Monomials section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open _root_.MvPolynomial open PaperVerification.Segre.Staircase variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] variable {n : I → ℕ}
/-- Exact source definition of Variables. -/
abbrev Variables (n : I → ℕ) := Σ i, Fin (n i + 1)
/-- One copy of the chosen coordinate in each factor. -/
noncomputable def cellExponent (u : Cell n) : Variables n →₀ ℕ := ∑ i, Finsupp.single ⟨i, u i⟩ 1
/-- A literal rank-one Segre coordinate monomial. -/
noncomputable def cellPolynomial (u : Cell n) : MvPolynomial (Variables n) K := monomial (cellExponent u) 1
end end PaperVerification.Segre.Monomials
namespace PaperVerification.Segre.Balanced section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials _root_.MvPolynomial variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {n : I → ℕ}
/-- The multidegree of one factor variable. -/
def factorWeight (z : Variables n) : I → ℕ := fun i => if z.1 = i then 1 else 0
/-- Equal degree in all factors. -/
def diagonalDegree (q : ℕ) : I → ℕ := fun _ => q
/-- Exact source definition of diagonalDegree_add. -/
theorem diagonalDegree_add (q r : ℕ) : diagonalDegree (I := I) (q + r) = diagonalDegree q + diagonalDegree r := by sorry
/-- The weighted exponent is exactly the vector of sums in the individual factor blocks. -/
theorem factorWeight_apply (a : Variables n →₀ ℕ) (i : I) : Finsupp.weight (factorWeight (n := n)) a i = ∑ j : Fin (n i + 1), a ⟨i,j⟩ := by sorry
end end PaperVerification.Segre.Balanced
namespace PaperVerification.Segre.RankParameters section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase _root_.Matrix open scoped Matrix variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {n : I → ℕ}
/-- Exact source definition of Ranks. -/
abbrev Ranks (n : I → ℕ) := Fin (sideSum n + 1)
/-- The literal comparability graph of the full product of chains. -/
def chainGraph (n : I → ℕ) : SimpleGraph (Cell n) where
  Adj u v := u ≠ v ∧ (u ≤ v ∨ v ≤ u)
  symm.symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := fun _ h => h.1 rfl
/-- Exact source definition of chainGraph_decidable. -/
instance chainGraph_decidable (n : I → ℕ) : DecidableRel (chainGraph n).Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u ≤ v ∨ v ≤ u)))
end end PaperVerification.Segre.RankParameters
namespace PaperVerification.Segre.HigherPieces section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Balanced PaperVerification.Segre.Artinian _root_.MvPolynomial variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {n : I → ℕ}
/-- Exact source definition of wordPolynomial. -/
noncomputable def wordPolynomial (q : ℕ) (w : Fin q → Cell n) : MvPolynomial (Variables n) K := ∏ j, cellPolynomial (w j)
/-- Exact source definition of piece. -/
noncomputable def piece (q : ℕ) : Submodule K (MvPolynomial (Variables n) K) := Submodule.span K (Set.range (wordPolynomial (K := K) (n := n) q))
/-- Equality with the entire balanced homogeneous component. -/
theorem piece_eq_balanced (q : ℕ) : piece (K := K) (n := n) q = weightedHomogeneousSubmodule K (factorWeight (n := n)) (diagonalDegree q) := by sorry
end end PaperVerification.Segre.HigherPieces
namespace SymmetricPower section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open scoped TensorProduct universe u v w variable {R ι : Type u} {M : Type v} {N : Type w} variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] variable (f : MultilinearMap R (fun _ : ι ↦ M) N)
/-- A permutation-invariant multilinear map takes the same value on a pure tensor and on each of its reorderings, so it is constant on the classes of the defining relation of the symmetric power. -/
public theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : addConGen (Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by sorry
/-- **The universal property of the symmetric tensor power**: a multilinear map that is unchanged by permuting its arguments descends to a linear map on the symmetric power. -/
noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x
end end SymmetricPower
namespace SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 universe u v w x variable (R : Type u) [CommSemiring R] variable {M : Type v} {N : Type w} {P : Type x} variable [AddCommMonoid M] [Module R M] variable [AddCommMonoid N] [Module R N] variable [AddCommMonoid P] [Module R P]
/-- The algebra homomorphism between symmetric algebras induced by a linear map. -/
noncomputable def map (f : M →ₗ[R] N) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N := lift ((ι R N).comp f)
/-- A surjective linear map induces a surjective map of symmetric algebras. -/
theorem map_surjective (f : M →ₗ[R] N) (h : Function.Surjective f) : Function.Surjective (map R f) := by sorry
end end SymmetricAlgebra
namespace SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 variable {R : Type u} [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
/-- **Right exactness of the symmetric algebra**: the kernel of the map of symmetric algebras induced by a surjective linear map `f` is the ideal generated by the kernel of `f`. -/
theorem ker_map_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) : RingHom.ker (map R f) = Ideal.span (ι R M '' LinearMap.ker f) := by sorry
end end SymmetricAlgebra
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 universe u v variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
theorem palomarSymmetricSubmoduleAdd : AddSubmonoidClass (Submodule R (SymmetricAlgebra R M)) (SymmetricAlgebra R M) := by infer_instance
attribute [instance 2400] palomarSymmetricSubmoduleAdd
/-- The degree-`n` homogeneous part of `SymmetricAlgebra R M`: the `n`-th power of the range of the canonical generator map. -/
abbrev homogeneousSubmodule (n : ℕ) : Submodule R (SymmetricAlgebra R M) := LinearMap.range (SymmetricAlgebra.ι R M) ^ n
/-- A symmetric-algebra generator is homogeneous of degree one. -/
theorem ι_mem_homogeneousSubmodule (x : M) : SymmetricAlgebra.ι R M x ∈ homogeneousSubmodule R M 1 := by sorry
/-- The homogeneous submodules form a graded monoid: the unit is homogeneous of degree zero, and multiplication adds degrees. -/
instance instGradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule R M) := Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))
end end TauCeti.SymmetricAlgebra
namespace TauCeti section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.MvPolynomial
/-- The monomial basis of a homogeneous component, indexed by exponent vectors of its degree. -/
noncomputable def homogeneousMonomialBasis {σ R : Type*} [CommSemiring R] (n : ℕ) : Module.Basis {s : σ →₀ ℕ // s.degree = n} R (homogeneousSubmodule σ R n) := (basisRestrictSupport R {s : σ →₀ ℕ | s.degree = n}).map (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R n).symm)
end end TauCeti
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.Module universe u v w variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
/-- Exact source definition of map_homogeneousSubmodule_equivMvPolynomial. -/
theorem map_homogeneousSubmodule_equivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) : (homogeneousSubmodule R M n).map (SymmetricAlgebra.equivMvPolynomial b).toLinearMap = MvPolynomial.homogeneousSubmodule ι R n := by sorry
/-- The restriction of the polynomial equivalence induced by `b` to homogeneous components. -/
noncomputable def homogeneousSubmoduleEquivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) : homogeneousSubmodule R M n ≃ₗ[R] MvPolynomial.homogeneousSubmodule ι R n := (Submodule.equivMapOfInjective (SymmetricAlgebra.equivMvPolynomial b).toLinearMap (SymmetricAlgebra.equivMvPolynomial b).injective _).trans (LinearEquiv.ofEq _ _ (map_homogeneousSubmodule_equivMvPolynomial R M b n))
/-- Degree-`n` multisets of basis indices are equivalent to exponent vectors of total degree `n`. -/
noncomputable def _root_.Sym.equivFinsuppDegree (ι : Type w) (n : ℕ) : Sym ι n ≃ {d : ι →₀ ℕ // d.degree = n} := by
  classical
  exact (Sym.equivNatSum ι n).trans
    (Equiv.subtypeEquiv (Equiv.refl _) (fun d => by
      simp [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Function.id_def]))
end end TauCeti.SymmetricAlgebra
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.Module universe u v w variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R M} in
/-- A basis of a module induces the monomial basis on each homogeneous component of its symmetric algebra. The basis vectors are indexed by degree-`n` multisets of basis indices. -/
noncomputable def _root_.Module.Basis.symmetricAlgebraHomogeneous {ι : Type w} (b : Basis ι R M) (n : ℕ) : Basis (Sym ι n) R (homogeneousSubmodule R M n) := by
  exact ((TauCeti.homogeneousMonomialBasis (R := R) n).map
    (homogeneousSubmoduleEquivMvPolynomial R M b n).symm).reindex
      (Sym.equivFinsuppDegree ι n).symm
end end TauCeti.SymmetricAlgebra
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.Module universe u v w variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
/-- Each homogeneous component of the symmetric algebra of a free module is free, with the monomial basis `Module.Basis.symmetricAlgebraHomogeneous`. -/
instance instModuleFreeHomogeneousSubmodule [Module.Free R M] (n : ℕ) : Module.Free R (homogeneousSubmodule R M n) := .of_basis ((Module.Free.chooseBasis R M).symmetricAlgebraHomogeneous n)
/-- Each homogeneous component of the symmetric algebra of a finite free module is finite: its monomial basis is indexed by the degree-`n` multisets of a finite basis. -/
instance instModuleFiniteHomogeneousSubmodule [Module.Free R M] [Module.Finite R M] (n : ℕ) : Module.Finite R (homogeneousSubmodule R M n) := .of_basis ((Module.Free.chooseBasis R M).symmetricAlgebraHomogeneous n)
end end TauCeti.SymmetricAlgebra
namespace TauCeti.SymmetricPower section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open scoped TensorProduct open _root_.SymmetricPower universe v w variable (R : Type) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
/-- Exact source definition of algebraMultilinear. -/
public noncomputable def algebraMultilinear (n : ℕ) : MultilinearMap R (fun _ : Fin n ↦ M) (SymmetricAlgebra R M) := (MultilinearMap.mkPiAlgebra R (Fin n) (SymmetricAlgebra R M)).compLinearMap (fun _ ↦ SymmetricAlgebra.ι R M)
/-- Exact source definition of algebraMultilinear_invariant. -/
public theorem algebraMultilinear_invariant (n : ℕ) (e : Equiv.Perm (Fin n)) : (algebraMultilinear R M n).domDomCongr e = algebraMultilinear R M n := by sorry
/-- Multiplication of the canonical generators, descended to the symmetric tensor power. -/
noncomputable def toSymmetricAlgebra (n : ℕ) : Sym[R]^n M →ₗ[R] SymmetricAlgebra R M := lift (algebraMultilinear R M n) (algebraMultilinear_invariant R M n)
/-- Multiplication preserves the degree of a symmetric tensor. -/
theorem toSymmetricAlgebra_mem_homogeneousSubmodule (n : ℕ) (x : Sym[R]^n M) : toSymmetricAlgebra R M n x ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by sorry
/-- Multiplication with codomain restricted to the homogeneous component of the same degree. -/
noncomputable def toHomogeneous (n : ℕ) : Sym[R]^n M →ₗ[R] TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := (toSymmetricAlgebra R M n).codRestrict _ (toSymmetricAlgebra_mem_homogeneousSubmodule R M n)
/-- The image of multiplication is exactly the homogeneous component of the same degree. -/
theorem range_toSymmetricAlgebra (n : ℕ) : LinearMap.range (toSymmetricAlgebra R M n) = TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by sorry
end end TauCeti.SymmetricPower
namespace TauCeti.SymmetricPower section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open scoped TensorProduct open _root_.SymmetricPower universe v w variable (R : Type) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] variable {R M}
/-- Multiplication embeds the symmetric tensor power of any module into its symmetric algebra, over any commutative semiring. -/
theorem toSymmetricAlgebra_injective (n : ℕ) : Function.Injective (toSymmetricAlgebra R M n) := by sorry
/-- The symmetric tensor power of a module is canonically its degree-`n` homogeneous symmetric-algebra component. -/
noncomputable def equivHomogeneous (n : ℕ) : Sym[R]^n M ≃ₗ[R] TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  refine LinearEquiv.ofBijective (toHomogeneous R M n) ⟨?_, ?_⟩
  · intro x y h
    exact toSymmetricAlgebra_injective n (congrArg Subtype.val h)
  · intro p
    obtain ⟨x, hx⟩ := (range_toSymmetricAlgebra R M n).ge p.property
    exact ⟨x, Subtype.ext hx⟩
end end TauCeti.SymmetricPower
namespace PaperVerification.Segre.SymmetricRealization section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Balanced PaperVerification.Segre.HigherPieces _root_.MvPolynomial _root_.Module open scoped TensorProduct variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {n : I → ℕ}
/-- Exact source definition of BalancedExponent. -/
abbrev BalancedExponent (q : ℕ) := {a : Variables n →₀ ℕ // Finsupp.weight (factorWeight (n := n)) a = diagonalDegree q}
/-- Exact source definition of FactorExponent. -/
abbrev FactorExponent (q : ℕ) := ∀ i : I, {a : Fin (n i+1) →₀ ℕ // a.degree=q}
/-- Concatenate exponent vectors in the disjoint factor-variable blocks. -/
noncomputable def assembleExponent (q : ℕ) (a : FactorExponent (n := n) q) :
    BalancedExponent (n := n) q :=
  ⟨Finsupp.sigmaFinsuppEquivPiFinsupp.symm (fun i => (a i).val),by
    funext i
    rw [factorWeight_apply]
    change (∑ j : Fin (n i+1), (a i).val j)=q
    simpa only [Finsupp.degree_eq_sum] using (a i).property⟩
/-- Read the factor degrees from a balanced exponent vector. -/
noncomputable def splitExponent (q : ℕ) (a : BalancedExponent (n := n) q) :
    FactorExponent (n := n) q := fun i =>
  ⟨Finsupp.sigmaFinsuppEquivPiFinsupp a.val i,by
    have h := congrFun a.property i
    rw [factorWeight_apply] at h
    simpa only [Finsupp.degree_eq_sum,Finsupp.sigmaFinsuppEquivPiFinsupp_apply,diagonalDegree] using h⟩
/-- Exact source definition of exponentEquiv. -/
noncomputable def exponentEquiv (q : ℕ) :
    FactorExponent (n := n) q ≃ BalancedExponent (n := n) q where
  toFun := assembleExponent q
  invFun := splitExponent q
  left_inv a := by
    funext i
    apply Subtype.ext
    ext j
    rfl
  right_inv a := by
    apply Subtype.ext
    ext z
    cases z
    rfl
/-- The monomial basis of the entire balanced homogeneous component. -/
noncomputable def balancedBasis (q : ℕ) : Basis (BalancedExponent (n := n) q) K (piece (K := K) (n := n) q) :=
  (basisRestrictSupport K {a | Finsupp.weight (factorWeight (n := n)) a = diagonalDegree q}).map
    (LinearEquiv.ofEq _ _ (by
      rw [piece_eq_balanced,weightedHomogeneousSubmodule_eq_finsupp_supported]
      rfl))
/-- The tensor product of the usual factor-polynomial homogeneous spaces. -/
abbrev PolynomialTensor (q : ℕ) := ⨂[K] i : I, MvPolynomial.homogeneousSubmodule (Fin (n i+1)) K q
/-- Exact source definition of polynomialTensorBasis. -/
noncomputable def polynomialTensorBasis (q : ℕ) : Basis (FactorExponent (n := n) q) K (PolynomialTensor (K := K) (n := n) q) := Basis.piTensorProduct (fun i : I => TauCeti.homogeneousMonomialBasis (σ := Fin (n i+1)) (R := K) q)
/-- Basis-level equivalence; the next results identify its underlying map. -/
noncomputable def polynomialTensorEquiv (q : ℕ) : PolynomialTensor (K := K) (n := n) q ≃ₗ[K] piece (K := K) (n := n) q := (polynomialTensorBasis (K := K) q).equiv (balancedBasis q) (exponentEquiv q)
end end PaperVerification.Segre.SymmetricRealization
namespace PaperVerification.Segre.SymmetricRealization section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Balanced PaperVerification.Segre.HigherPieces _root_.MvPolynomial _root_.Module open scoped TensorProduct variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {n : I → ℕ} variable {F : Type} [Field F]
/-- The actual symmetric tensor power of the i-th vector-space factor. -/
abbrev FactorSymmetric (q : ℕ) (i : I) := Sym[F]^q (Fin (n i+1) → F)
/-- The component displayed in the paper, using actual symmetric quotient tensors. -/
abbrev SymmetricTensor (q : ℕ) := ⨂[F] i : I, FactorSymmetric (F := F) (n := n) q i
/-- Exact source definition of factorSymmetricEquiv. -/
noncomputable def factorSymmetricEquiv (q : ℕ) (i : I) : FactorSymmetric (F := F) (n := n) q i ≃ₗ[F] MvPolynomial.homogeneousSubmodule (Fin (n i+1)) F q := (TauCeti.SymmetricPower.equivHomogeneous (R := F) (M := Fin (n i+1) → F) q).trans (TauCeti.SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial F (Fin (n i+1) → F) (Pi.basisFun F (Fin (n i+1))) q)
/-- Every degree of the paper's tensor-symmetric-power Segre ring agrees with its literal balanced polynomial realization. -/
noncomputable def symmetricTensorEquiv (q : ℕ) : SymmetricTensor (F := F) (n := n) q ≃ₗ[F] piece (K := F) (n := n) q := (PiTensorProduct.congr (factorSymmetricEquiv (F := F) (n := n) q)).trans (polynomialTensorEquiv q)
/-- The ordinary product between two homogeneous polynomial components. -/
noncomputable def factorHomogeneousMul (p q : ℕ) (i : I) :
    MvPolynomial.homogeneousSubmodule (Fin (n i+1)) F p →ₗ[F]
      MvPolynomial.homogeneousSubmodule (Fin (n i+1)) F q →ₗ[F]
        MvPolynomial.homogeneousSubmodule (Fin (n i+1)) F (p+q) where
  toFun x :=
    { toFun := fun y => ⟨x.val*y.val,x.property.mul y.property⟩
      map_add' := fun y z => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c y => Subtype.ext (mul_smul_comm _ _ _) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact Subtype.ext (add_mul _ _ _)
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (smul_mul_assoc _ _ _)
/-- Multiplication in a symmetric algebra, restricted to actual symmetric powers through the proved canonical homogeneous-component equivalence. -/
noncomputable def factorSymmetricMul (p q : ℕ) (i : I) : FactorSymmetric (F := F) (n := n) p i →ₗ[F] FactorSymmetric (F := F) (n := n) q i →ₗ[F] FactorSymmetric (F := F) (n := n) (p+q) i := ((factorHomogeneousMul p q i).compl₁₂ (factorSymmetricEquiv p i).toLinearMap (factorSymmetricEquiv q i).toLinearMap).compr₂ (factorSymmetricEquiv (p+q) i).symm.toLinearMap
/-- Componentwise multiplication of the tensor factors, extended bilinearly by the universal property of the tensor product. -/
noncomputable def tensorMul (p q : ℕ) : SymmetricTensor (F := F) (n := n) p →ₗ[F] SymmetricTensor (F := F) (n := n) q →ₗ[F] SymmetricTensor (F := F) (n := n) (p+q) := PiTensorProduct.map₂ (factorSymmetricMul p q)
/-- The canonical degreewise equivalence respects the paper's componentwise symmetric-power multiplication in every pair of degrees. -/
theorem symmetricTensorEquiv_mul (p q : ℕ) (x : SymmetricTensor (F := F) (n := n) p) (y : SymmetricTensor (F := F) (n := n) q) : (symmetricTensorEquiv (p+q) (tensorMul p q x y)).val = (symmetricTensorEquiv p x).val * (symmetricTensorEquiv q y).val := by sorry
end end PaperVerification.Segre.SymmetricRealization
namespace PaperVerification.Segre.SymmetricRealization section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false set_option backward.isDefEq.respectTransparency false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Balanced PaperVerification.Segre.HigherPieces _root_.MvPolynomial _root_.Module open scoped TensorProduct DirectSum variable {I : Type*} [Fintype I] [DecidableEq I] {n : I → ℕ} variable {F : Type} [Field F]
/-- Exact source definition of piece_gradedMonoid. -/
instance piece_gradedMonoid : SetLike.GradedMonoid (piece (K := F) (n := n)) where
  one_mem := by
    rw [piece_eq_balanced]
    exact isWeightedHomogeneous_one F _
  mul_mem p q x y hx hy := by
    rw [piece_eq_balanced,mem_weightedHomogeneousSubmodule] at hx hy ⊢
    simpa only [← diagonalDegree_add] using hx.mul hy
/-- Exact source definition of scalarPiece. -/
noncomputable def scalarPiece : F →ₗ[F] piece (K := F) (n := n) 0 where
  toFun c := ⟨MvPolynomial.C c,by
    rw [piece_eq_balanced]
    exact isWeightedHomogeneous_C _ _⟩
  map_add' x y := Subtype.ext (map_add MvPolynomial.C x y)
  map_smul' c x := by
    apply Subtype.ext
    change MvPolynomial.C (c*x)=c • MvPolynomial.C x
    rw [MvPolynomial.smul_eq_C_mul,map_mul]
/-- Exact source definition of tensorGMul. -/
noncomputable instance tensorGMul : GradedMonoid.GMul (SymmetricTensor (F := F) (n := n)) where
  mul := fun {p q} x y => tensorMul p q x y
/-- Exact source definition of tensorGOne. -/
noncomputable instance tensorGOne : GradedMonoid.GOne (SymmetricTensor (F := F) (n := n)) where
  one := (symmetricTensorEquiv 0).symm (scalarPiece 1)
/-- Exact source definition of gradedRealization. -/
noncomputable def gradedRealization : GradedMonoid (SymmetricTensor (F := F) (n := n)) ≃ GradedMonoid (fun q => piece (K := F) (n := n) q) := Equiv.sigmaCongrRight (fun q => (symmetricTensorEquiv q).toEquiv)
/-- Exact source definition of gradedRealization_mul. -/
@[simp] theorem gradedRealization_mul (x y : GradedMonoid (SymmetricTensor (F := F) (n := n))) : gradedRealization (x*y)=gradedRealization x*gradedRealization y := by sorry
/-- Exact source definition of gradedRealization_one. -/
@[simp] theorem gradedRealization_one : gradedRealization (1 : GradedMonoid (SymmetricTensor (F := F) (n := n)))=1 := by sorry
/-- Exact source definition of gradedRealization_smul. -/
@[simp] theorem gradedRealization_smul (c : F) (x : GradedMonoid (SymmetricTensor (F := F) (n := n))) : gradedRealization (c • x)=c • gradedRealization x := by sorry
/-- Exact source definition of tensorGCommMonoid. -/
noncomputable instance tensorGCommMonoid :
    GradedMonoid.GCommMonoid (SymmetricTensor (F := F) (n := n)) where
  one_mul x := by
    apply gradedRealization.injective
    rw [gradedRealization_mul,gradedRealization_one,one_mul]
  mul_one x := by
    apply gradedRealization.injective
    rw [gradedRealization_mul,gradedRealization_one,mul_one]
  mul_assoc x y z := by
    apply gradedRealization.injective
    simp only [gradedRealization_mul,mul_assoc]
  mul_comm x y := by
    apply gradedRealization.injective
    rw [gradedRealization_mul,gradedRealization_mul,mul_comm]
/-- Exact source definition of tensorGNonUnitalNonAssocSemiring. -/
noncomputable instance tensorGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (SymmetricTensor (F := F) (n := n)) where
  mul_zero x := (tensorMul _ _ x).map_zero
  zero_mul y := LinearMap.congr_fun (tensorMul _ _).map_zero y
  mul_add x y z := (tensorMul _ _ x).map_add y z
  add_mul x y z := LinearMap.congr_fun ((tensorMul _ _).map_add x y) z
/-- Exact source definition of tensorGSemiring. -/
noncomputable instance tensorGSemiring :
    DirectSum.GSemiring (SymmetricTensor (F := F) (n := n)) where
  natCast k := (symmetricTensorEquiv 0).symm (scalarPiece (k : F))
  natCast_zero := by simp only [Nat.cast_zero,map_zero]
  natCast_succ k := by
    change (symmetricTensorEquiv 0).symm (scalarPiece ((k+1 : ℕ) : F)) =
      (symmetricTensorEquiv 0).symm (scalarPiece (k : F)) +
        (symmetricTensorEquiv 0).symm (scalarPiece 1)
    rw [Nat.cast_add_one,map_add,map_add]
/-- Exact source definition of tensorGCommSemiring. -/
noncomputable instance tensorGCommSemiring :
    DirectSum.GCommSemiring (SymmetricTensor (F := F) (n := n)) where
/-- Exact source definition of tensorGCommRing. -/
noncomputable instance tensorGCommRing :
    DirectSum.GCommRing (SymmetricTensor (F := F) (n := n)) where
  intCast k := (symmetricTensorEquiv 0).symm (scalarPiece (k : F))
  intCast_ofNat k := by
    simp only [Int.cast_natCast] <;> rfl
  intCast_negSucc_ofNat k := by
    simp only [Int.cast_negSucc,map_neg] <;> rfl
/-- The usual scalar inclusion in degree zero. -/
noncomputable instance tensorGAlgebra :
    DirectSum.GAlgebra F (SymmetricTensor (F := F) (n := n)) where
  toFun := ((symmetricTensorEquiv 0).symm.toLinearMap.comp scalarPiece).toAddMonoidHom
  map_one := rfl
  map_mul c d := by
    apply gradedRealization.injective
    apply Sigma.subtype_ext
    · rfl
    · change (symmetricTensorEquiv 0 ((symmetricTensorEquiv 0).symm (scalarPiece (c*d)))).val =
        (symmetricTensorEquiv (0+0) (tensorMul 0 0
          ((symmetricTensorEquiv 0).symm (scalarPiece c))
          ((symmetricTensorEquiv 0).symm (scalarPiece d)))).val
      rw [symmetricTensorEquiv_mul,LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
      exact map_mul MvPolynomial.C c d
  commutes c x := mul_comm _ _
  smul_def c x := by
    apply gradedRealization.injective
    rw [gradedRealization_smul,gradedRealization_mul]
    apply Sigma.subtype_ext (zero_add x.1).symm
    change c • (symmetricTensorEquiv x.1 x.2).val =
      (symmetricTensorEquiv 0 ((symmetricTensorEquiv 0).symm (scalarPiece c))).val *
        (symmetricTensorEquiv x.1 x.2).val
    rw [LinearEquiv.apply_symm_apply]
    exact MvPolynomial.smul_eq_C_mul _ _
/-- Exactly the direct sum displayed in the paper, with the verified componentwise tensor-symmetric-power algebra structure above. -/
abbrev SymmetricSegre := ⨁ q : ℕ, SymmetricTensor (F := F) (n := n) q
end end PaperVerification.Segre.SymmetricRealization
namespace PaperVerification.Segre section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open _root_.Matrix open scoped Matrix variable {K I V : Type*} [Field K] [Fintype I] [DecidableEq I]
/-- Infinitesimal rigidity restricted to a chosen vertex set. Velocities are allowed on all vertices, so the definition does not assume any extension theorem. -/
def InfinitesimallyRigidOn (G : SimpleGraph V) (p : V → I → K) (S : Set V) : Prop := ∀ u : V → I → K, (∀ v ∈ S, ∀ w ∈ S, G.Adj v w → (p v - p w) ⬝ᵥ (u v - u w) = 0) → ∃ (M : Matrix I I K) (t : I → K), Mᵀ = -M ∧ (∀ i, M i i = 0) ∧ ∀ v ∈ S, u v = M *ᵥ p v + t
end end PaperVerification.Segre
namespace PaperVerification.Segre.SymmetricRealization section set_option maxRecDepth 2048 set_option autoImplicit false set_option backward.isDefEq.respectTransparency false set_option synthInstance.maxHeartbeats 100000 open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Balanced PaperVerification.Segre.HigherPieces PaperVerification.Segre.Artinian open scoped TensorProduct DirectSum variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype D] [DecidableEq D] {n : I → ℕ} variable {F : Type} [Field F]
/-- Cache the canonical graded direct-sum ring before concrete parameter ideals are elaborated. No operations or algebra structure are transported anew. -/
noncomputable instance symmetricSegreCommRing : CommRing (SymmetricSegre (F := F) (n := n)) := by
  letI : DirectSum.GCommRing (SymmetricTensor (F := F) (n := n)) :=
    tensorGCommRing (F := F) (n := n)
  exact DirectSum.commRing (A := SymmetricTensor (F := F) (n := n))
/-- Exact source definition of symmetricSegreAlgebra. -/
noncomputable instance symmetricSegreAlgebra : Algebra F (SymmetricSegre (F := F) (n := n)) := inferInstance
/-- Exact source definition of symmetricSegreModule. -/
noncomputable instance symmetricSegreModule : Module F (SymmetricSegre (F := F) (n := n)) := inferInstance
/-- A tensor of the coordinate vectors, each regarded in its actual first symmetric power. -/
noncomputable def coordinateTensor (u : Cell n) : SymmetricTensor (F := F) (n := n) 1 := PiTensorProduct.tprod F (fun i => SymmetricPower.tprod F (fun _ : Fin 1 => Pi.basisFun F (Fin (n i+1)) (u i)))
/-- Exact source definition of symmetricCoordinate. -/
noncomputable def symmetricCoordinate (u : Cell n) : SymmetricSegre (F := F) (n := n) := DirectSum.of _ 1 (coordinateTensor u)
/-- An arbitrary linear parameter, with exactly the paper's coordinate coefficients. -/
noncomputable def symmetricParameter (A : Matrix (Cell n) D F) (d : D) : SymmetricSegre (F := F) (n := n) := ∑ u, A u d • symmetricCoordinate u
/-- Exact source definition of symmetricParameterIdeal. -/
noncomputable def symmetricParameterIdeal (A : Matrix (Cell n) D F) : Ideal (SymmetricSegre (F := F) (n := n)) := Ideal.span (Set.range (symmetricParameter A))
theorem palomarSymmetricParameterTwoSided (A : Matrix (Cell n) D F) : (symmetricParameterIdeal A).IsTwoSided := by infer_instance
attribute [instance 2400] palomarSymmetricParameterTwoSided
/-- Exact source definition of SymmetricReduction. -/
abbrev SymmetricReduction (A : Matrix (Cell n) D F) := SymmetricSegre (F := F) (n := n) ⧸ symmetricParameterIdeal A
/-- These are the standard ideal-quotient instances on the literal reduction. -/
noncomputable instance symmetricReductionCommRing (A : Matrix (Cell n) D F) : CommRing (SymmetricReduction A) := Ideal.Quotient.commRing _
/-- Exact source definition of symmetricReductionAlgebra. -/
noncomputable instance symmetricReductionAlgebra (A : Matrix (Cell n) D F) : Algebra F (SymmetricReduction A) := inferInstance
/-- Exact source definition of symmetricReductionModule. -/
noncomputable instance symmetricReductionModule (A : Matrix (Cell n) D F) : Module F (SymmetricReduction A) := inferInstance
/-- Exact source definition of symmetricPieceToReduction. -/
noncomputable def symmetricPieceToReduction (A : Matrix (Cell n) D F) (q : ℕ) : SymmetricTensor (F := F) (n := n) q →ₗ[F] SymmetricReduction A := (Ideal.Quotient.mkₐ F (symmetricParameterIdeal A)).toLinearMap.comp (DirectSum.lof F ℕ (SymmetricTensor (F := F) (n := n)) q)
/-- Exact source definition of symmetricActualPiece. -/
noncomputable def symmetricActualPiece (A : Matrix (Cell n) D F) (q : ℕ) : Submodule F (SymmetricReduction A) := LinearMap.range (symmetricPieceToReduction A q)
end end PaperVerification.Segre.SymmetricRealization
namespace PaperVerification.Segre.RigidityRank section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open _root_.Matrix PaperVerification.Segre.GraphKernel PaperVerification.Segre.KoszulDimension open scoped Matrix variable {K V I E : Type*} [Field K] [Fintype I] [DecidableEq I]
/-- Use oriented edges to give a finite index type without choosing an orientation. Repeated opposite rows have the same kernel and rank. -/
abbrev Edges (G : SimpleGraph V) := {vw : V × V // G.Adj vw.1 vw.2}
/-- Exact source definition of endpoints. -/
def endpoints (G : SimpleGraph V) : Edges G → V × V := Subtype.val
end end PaperVerification.Segre.RigidityRank
namespace PaperVerification.Segre.RigidityRank section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open _root_.Matrix PaperVerification.Segre.GraphKernel PaperVerification.Segre.KoszulDimension open scoped Matrix variable {K V I E : Type*} [Field K] [Fintype I] [DecidableEq I] variable [Fintype V]
/-- The literal rigidity matrix, with one column for each vertex-coordinate pair. The formula is polynomial and is valid over any coefficient ring. -/
noncomputable def rigidityMatrix {R : Type*} [CommRing R] (p : Matrix V I R) (edges : E → V × V) : Matrix E (V × I) R := by
  classical
  exact fun e vi =>
    (if vi.1 = (edges e).1 then p (edges e).1 vi.2 - p (edges e).2 vi.2 else 0) -
      (if vi.1 = (edges e).2 then p (edges e).1 vi.2 - p (edges e).2 vi.2 else 0)
theorem palomarFlattenIdentityInvPair : RingHomInvPair (RingHom.id K) (RingHom.id K) := by infer_instance
attribute [instance 2400] palomarFlattenIdentityInvPair
/-- Flatten the vertex-indexed velocity coordinates into matrix-column coordinates. -/
def flattenVelocity : (V → I → K) ≃ₗ[K] (V × I → K) where
  toFun u vi := u vi.1 vi.2
  invFun u v i := u (v, i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end end PaperVerification.Segre.RigidityRank
namespace PaperVerification.Segre.ThreeChainCores section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.GenericRigidity PaperVerification.Segre.BooleanBase PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters PaperVerification.Segre.StressFree variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
/-- Exact source definition of shape111. -/
def shape111 : Fin 3 → ℕ := ![1,1,1]
/-- Exact source definition of shape112. -/
def shape112 : Fin 3 → ℕ := ![1,1,2]
/-- Exact source definition of shape113. -/
def shape113 : Fin 3 → ℕ := ![1,1,3]
end end PaperVerification.Segre.ThreeChainCores
namespace PaperVerification.Segre.ChainClassification section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters PaperVerification.Segre.GenericRigidity PaperVerification.Segre.ChainInduction PaperVerification.Segre.ThreeChainCores variable {K : Type*} [Field K]
/-- The exact three exceptions, including all permutations of the factors. -/
def ExceptionalTriple (n : Fin 3 → ℕ) : Prop := ∃ e : Equiv.Perm (Fin 3), (fun i => n (e i)) = shape111 ∨ (fun i => n (e i)) = shape112 ∨ (fun i => n (e i)) = shape113
end end PaperVerification.Segre.ChainClassification
namespace PaperVerification.Segre.SymmetricRealization section set_option maxRecDepth 2048 set_option autoImplicit false set_option backward.isDefEq.respectTransparency false set_option synthInstance.maxHeartbeats 100000 open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials open scoped TensorProduct DirectSum variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype D] [DecidableEq D] {n : I → ℕ} variable {F : Type} [Field F]
/-- The whole-quotient residue map respects componentwise symmetric-power multiplication. -/
theorem symmetricPieceToReduction_product (A : Matrix (Cell n) D F) (p q : ℕ) (x : SymmetricTensor (F := F) (n := n) p) (y : SymmetricTensor (F := F) (n := n) q) : symmetricPieceToReduction A (p+q) (tensorMul p q x y)= symmetricPieceToReduction A p x * symmetricPieceToReduction A q y := by sorry
/-- Actual multiplication by an actual degree-one element of the paper's quotient. -/
noncomputable def symmetricFirstLefschetz (A : Matrix (Cell n) D F)
    (ℓ : symmetricActualPiece A 1) :
    symmetricActualPiece A 1 →ₗ[F] symmetricActualPiece A 2 where
  toFun x := ⟨ℓ.val*x.val,by
    obtain ⟨f,hf⟩ := ℓ.property
    obtain ⟨g,hg⟩ := x.property
    refine ⟨tensorMul 1 1 f g,?_⟩
    rw [symmetricPieceToReduction_product A 1 1 f g,hf,hg]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)
end end PaperVerification.Segre.SymmetricRealization
namespace PaperVerification.Segre.TwoFactorActual section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Balanced PaperVerification.Segre.RankParameters variable {K : Type*} [Field K]
/-- Exact source definition of shape. -/
def shape (a b : ℕ) : Fin 2 → ℕ := ![a,b]
end end PaperVerification.Segre.TwoFactorActual
namespace PaperVerification.Segre.TwoFactorInjectivity section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Monomials PaperVerification.Segre.ActualQuotient PaperVerification.Segre.TwoFactorActual PaperVerification.Segre.TwoFactorPropagation PaperVerification.Segre.TwoFactorTranspose variable {K : Type*} [Field K] [Infinite K]
/-- Exact source definition of Exceptional. -/
def Exceptional (a b : ℕ) : Prop := (a=2 ∧ (b=2 ∨ b=3 ∨ b=4)) ∨ (b=2 ∧ (a=2 ∨ a=3 ∨ a=4))
end end PaperVerification.Segre.TwoFactorInjectivity
namespace PaperVerification.Segre.TwoFactorGeneric section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.RankParameters PaperVerification.Segre.TwoFactorActual PaperVerification.Segre.FixedLefschetzRanks open PaperVerification.Segre.GenericFirstLefschetz PaperVerification.Segre.GenericSurjectivity PaperVerification.Segre.TwoFactorOneDimension variable {K : Type*} [Field K] [Infinite K]
/-- Exact source definition of kernelDefect. -/
noncomputable def kernelDefect (a b : ℕ) : ℕ := by
  classical
  exact if a=1 ∨ b=1 then a*b else
    if TwoFactorInjectivity.Exceptional a b then (if a=4 ∨ b=4 then 2 else 3) else 0
end end PaperVerification.Segre.TwoFactorGeneric
namespace PaperVerification.Segre.ThreeFactorLefschetz section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.RankParameters PaperVerification.Segre.GenericFirstLefschetz PaperVerification.Segre.GenericSurjectivity open PaperVerification.Segre.ChainClassification PaperVerification.Segre.ThreeChainCores _root_.Matrix variable {K : Type*} [Field K]
/-- Exact first-Lefschetz defect for positive triples. The exceptional predicate is independently specified by literal factor permutations. -/
noncomputable def kernelDefect (n : Fin 3 → ℕ) : ℕ := by
  classical
  exact if ExceptionalTriple n then (if sideSum n ≤ 4 then 3 else 1) else 0
end end PaperVerification.Segre.ThreeFactorLefschetz
namespace PaperVerification.Segre.Principal section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false set_option backward.isDefEq.respectTransparency false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.RankParameters PaperVerification.Segre.GenericFirstLefschetz variable {K : Type*} [Field K] [Infinite K]
/-- The literal defect list in Theorem1.1, with no bounded-parameter convention. -/
noncomputable def kernelDefect (k : ℕ) (n : Fin k → ℕ) : ℕ := by
  classical
  exact if h : k=2 then
    TwoFactorGeneric.kernelDefect (n (Fin.cast h.symm (0 : Fin 2)))
      (n (Fin.cast h.symm (1 : Fin 2)))
    else if h : k=3 then
      ThreeFactorLefschetz.kernelDefect (fun i => n (Fin.cast h.symm i))
    else 0
end end PaperVerification.Segre.Principal
namespace PaperVerification.Segre.SymmetricPrincipal section set_option maxRecDepth 2048 set_option autoImplicit false set_option backward.isDefEq.respectTransparency false set_option synthInstance.maxHeartbeats 100000 open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.RankParameters PaperVerification.Segre.SymmetricRealization variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype D] [DecidableEq D] {n : I → ℕ} variable {F : Type} [Field F]
theorem palomarSymmetricReductionScalarTower (A : Matrix (Cell n) D F) : IsScalarTower F F (SymmetricReduction A) := by infer_instance
attribute [instance 2400] palomarSymmetricReductionScalarTower
/-- General forms are defined in coordinates of a basis of the entire actual first homogeneous piece of the symmetric-tensor quotient. -/
def GenericSymmetricForms (A : Matrix (Cell n) D F) (P : symmetricActualPiece A 1 → Prop) : Prop := ∃ b : Module.Basis (Fin (Module.finrank F (symmetricActualPiece A 1))) F (symmetricActualPiece A 1), ∃ h : MvPolynomial (Fin (Module.finrank F (symmetricActualPiece A 1))) F, h≠0 ∧ ∀ c : Fin (Module.finrank F (symmetricActualPiece A 1)) → F, MvPolynomial.eval c h≠0 → P (∑ i,c i • b i)
/-- The same literal symmetric-tensor theorem with maximal rank expressed as the minimum of the two actual homogeneous dimensions. Their finiteness comes from the quotient certificate and is not an extra hypothesis. -/
theorem theorem_1_1_symmetric_rank [Infinite F] (k : ℕ) [NeZero k] (n : Fin k → ℕ) (hpos : ∀ i,1≤n i) : ∃ g : MvPolynomial (Cell n × Ranks n) F,g≠0 ∧ ∀ A : Matrix (Cell n) (Ranks n) F, MvPolynomial.eval (fun j => A j.1 j.2) g≠0 → Module.Finite F (SymmetricReduction A) ∧ IsArtinianRing (SymmetricReduction A) ∧ GenericSymmetricForms A (fun ℓ => Module.finrank F (LinearMap.range (symmetricFirstLefschetz A ℓ)) = min (Module.finrank F (symmetricActualPiece A 1)) (Module.finrank F (symmetricActualPiece A 2)) ∧ Module.finrank F (LinearMap.ker (symmetricFirstLefschetz A ℓ))= Principal.kernelDefect k n) := by sorry
/-- Explicit nonvacuity of the full principal certificate. The parameter matrix and the form in the actual quotient both exist over every infinite field; neither generic quantifier can hold through an empty parameter space. -/
theorem theorem_1_1_symmetric_nonempty [Infinite F] (k : ℕ) [NeZero k] (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) : ∃ (A : Matrix (Cell n) (Ranks n) F) (ℓ : symmetricActualPiece A 1), Module.Finite F (SymmetricReduction A) ∧ IsArtinianRing (SymmetricReduction A) ∧ Module.finrank F (LinearMap.range (symmetricFirstLefschetz A ℓ)) = min (Module.finrank F (symmetricActualPiece A 1)) (Module.finrank F (symmetricActualPiece A 2)) ∧ Module.finrank F (LinearMap.ker (symmetricFirstLefschetz A ℓ)) = Principal.kernelDefect k n := by sorry
/-- The complete one-factor quotient algebra is K also in the literal symmetric-tensor presentation. -/
theorem theorem_1_1_symmetric_one_factor [Infinite F] (n : Fin 1 → ℕ) : ∃ g : MvPolynomial (Cell n × Ranks n) F,g≠0 ∧ ∀ A : Matrix (Cell n) (Ranks n) F, MvPolynomial.eval (fun j => A j.1 j.2) g≠0 → Nonempty (SymmetricReduction A ≃ₐ[F] F) := by sorry
/-- The full second homogeneous piece vanishes in each projective-line case, with the same unrestricted parameter open and both factor orders. -/
theorem theorem_1_1_symmetric_projective_line [Infinite F] (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hline : a=1 ∨ b=1) : ∃ g : MvPolynomial (Cell (TwoFactorActual.shape a b) × Ranks (TwoFactorActual.shape a b)) F,g≠0 ∧ ∀ A : Matrix (Cell (TwoFactorActual.shape a b)) (Ranks (TwoFactorActual.shape a b)) F, MvPolynomial.eval (fun j => A j.1 j.2) g≠0 → symmetricActualPiece A 2=⊥ := by sorry
end end PaperVerification.Segre.SymmetricPrincipal
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
/-- The localization of `A` at the homogeneous prime ideal of a point of `Proj A`: the stalks of all twisting sheaves embed into it. -/
abbrev Localizations (x : ProjectiveSpectrum 𝒜) : Type u := Localization.AtPrime x.asHomogeneousIdeal.toIdeal
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {𝒜} in
/-- A dependent function on an open `U` is a *fraction of degree `n`* if it is a fixed fraction `r / s` with `r` and `s` homogeneous, `deg r = deg s + n` and `s` outside every point of `U`. -/
def IsFraction (n : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, Localizations 𝒜 x.1) : Prop := ∃ (i j : ℕ) (_ : (j : ℤ) = i + n) (r : 𝒜 j) (s : 𝒜 i) (s_nin : ∀ x : U, (s : A) ∉ x.1.asHomogeneousIdeal.toIdeal), ∀ x : U, f x = Localization.mk (r : A) ⟨s, s_nin x⟩
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
/-- Being a fraction of degree `n` is preserved by restriction to smaller opens. -/
def isFractionPrelocal (n : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Localizations 𝒜 x where
  pred f := IsFraction n f
  res := by rintro V U i f ⟨a, b, h, r, s, hs, w⟩; exact ⟨a, b, h, r, s, (hs <| i ·), (w <| i ·)⟩
/-- The local predicate of being locally a fraction of degree `n`; the sections of the twisting sheaf `𝒪(n)` are the dependent functions satisfying it. -/
def isLocallyFraction (n : ℤ) : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Localizations 𝒜 x := (isFractionPrelocal 𝒜 n).sheafify
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] variable {𝒜}
/-- The zero function is locally a fraction of every degree. -/
theorem isLocallyFraction_zero (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) : (isLocallyFraction 𝒜 n).pred (0 : ∀ x : U, Localizations 𝒜 x.1) := by sorry
/-- Exact source definition of isLocallyFraction_add. -/
theorem isLocallyFraction_add {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)} {f g : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 n).pred f) (hg : (isLocallyFraction 𝒜 n).pred g) : (isLocallyFraction 𝒜 n).pred (f + g) := by sorry
/-- Exact source definition of isLocallyFraction_neg. -/
theorem isLocallyFraction_neg {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)} {f : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 n).pred f) : (isLocallyFraction 𝒜 n).pred (-f) := by sorry
/-- The product of a local fraction of degree `m` and a local fraction of degree `n` is a local fraction of degree `m + n`. -/
theorem isLocallyFraction_mul {m n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)} {f g : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 m).pred f) (hg : (isLocallyFraction 𝒜 n).pred g) : (isLocallyFraction 𝒜 (m + n)).pred (f * g) := by sorry
/-- Sections of the structure sheaf of `Proj`, viewed in the localizations, are local fractions of degree `0`. -/
theorem isLocallyFraction_val {U : Opens (ProjectiveSpectrum.top 𝒜)} (a : Γ(Proj 𝒜, U)) : (isLocallyFraction 𝒜 0).pred fun x ↦ (a.1 x).val := by sorry
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] variable {𝒜}
variable (𝒜) in
/-- The local fractions of degree `n` on `U`, as an additive subgroup of all dependent functions into the localizations. -/
def sectionsAddSubgroup (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Localizations 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 n).pred f}
  zero_mem' := isLocallyFraction_zero n U
  add_mem' := isLocallyFraction_add
  neg_mem' := isLocallyFraction_neg
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] variable {𝒜}
/-- Sections of the structure sheaf of `Proj` act on local fractions of degree `n` pointwise, through the inclusions `A_{(x)} → A_x` of the homogeneous localizations. -/
instance sectionsAddSubgroup.smul (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    SMul Γ(Proj 𝒜, U) (sectionsAddSubgroup 𝒜 n U) where
  smul a f := ⟨fun x ↦ (a.1 x).val * f.1 x, by
    have := isLocallyFraction_mul (isLocallyFraction_val a) f.2
    rw [zero_add] at this
    exact this⟩
/-- The local fractions of degree `n` on `U` form a module over the sections of the structure sheaf of `Proj` on `U`. -/
instance sectionsAddSubgroup.module (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module Γ(Proj 𝒜, U) (sectionsAddSubgroup 𝒜 n U) where
  one_smul f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) HomogeneousLocalization.val_one).trans (one_mul _)
  mul_smul _ _ f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) (HomogeneousLocalization.val_mul _ _)).trans (mul_assoc _ _ _)
  smul_zero _ := Subtype.ext <| funext fun _ ↦ mul_zero _
  smul_add _ _ _ := Subtype.ext <| funext fun _ ↦ mul_add _ _ _
  add_smul _ _ f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) (HomogeneousLocalization.val_add _ _)).trans (add_mul _ _ _)
  zero_smul f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) HomogeneousLocalization.val_zero).trans (zero_mul _)
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] variable {𝒜} variable (𝒜)
/-- The twisting sheaf `𝒪(n)` as a sheaf of types: the subsheaf of dependent functions into the localizations which are locally fractions of degree `n`. -/
def twistingSheafInType (n : ℤ) : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) := subsheafToTypes (isLocallyFraction 𝒜 n)
/-- The twisting sheaf `𝒪(n)` as a presheaf of abelian groups. -/
def twistingPresheafInAb (n : ℤ) : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (sectionsAddSubgroup 𝒜 n U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun f := ⟨fun x ↦ f.1 (i.unop x), (isLocallyFraction 𝒜 n).res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl
/-- The presheaf of abelian groups `𝒪(n)` has the sheaf of types `𝒪(n)` as underlying presheaf of types. -/
def twistingPresheafInAbCompForget (n : ℤ) : twistingPresheafInAb 𝒜 n ⋙ forget Ab ≅ (twistingSheafInType 𝒜 n).obj := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl
/-- The twisting sheaf `𝒪(n)` as a presheaf of modules over the structure sheaf of `Proj`. -/
def twistingPresheaf (n : ℤ) : PresheafOfModules.{u} (Proj 𝒜).ringCatSheaf.obj :=
  letI (U : (Proj 𝒜).Opensᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((twistingPresheafInAb 𝒜 n).obj U) :=
    sectionsAddSubgroup.module n U.unop
  .ofPresheaf (twistingPresheafInAb 𝒜 n) fun _ _ _ _ _ ↦ rfl
end end AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
namespace AlgebraicGeometry.Proj section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf
/-- The **twisting sheaf** `𝒪(n)` on `Proj A`, for `n ∈ ℤ`: the sheaf of `𝒪_{Proj A}`-modules whose sections over `U` are the dependent functions `x ↦ f x ∈ A_x` on `U` which are locally fractions `r / s` of homogeneous elements with `deg r ... -/
def twistingSheaf (n : ℤ) : (Proj 𝒜).Modules where
  val := twistingPresheaf 𝒜 n
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (TopCat.Presheaf.isSheaf_of_iso (twistingPresheafInAbCompForget 𝒜 n).symm
      (twistingSheafInType 𝒜 n).2)
end end AlgebraicGeometry.Proj
namespace AlgebraicGeometry.Proj.twistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf variable {𝒜} {n : ℤ} {U V : (Proj 𝒜).Opens}
/-- Exact source definition of ext. -/
theorem ext {s t : Γ(twistingSheaf 𝒜 n, U)} (h : ∀ x, s.1 x = t.1 x) : s = t := by sorry
end end AlgebraicGeometry.Proj.twistingSheaf
namespace AlgebraicGeometry.Proj.twistingSheaf section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.TopCat _root_.TopologicalSpace _root_.CategoryTheory _root_.Opposite universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable (𝒜 : ℕ → σ) [GradedRing 𝒜] open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf variable {𝒜} {n : ℤ} {U V : (Proj 𝒜).Opens}
variable (𝒜 U) in
/-- The multiplication `Γ(U, 𝒪(m)) × Γ(U, 𝒪(n)) → Γ(U, 𝒪(m + n))`, bilinear over the sections of the structure sheaf: sections are multiplied pointwise in the localizations. -/
def mul (m n : ℤ) : Γ(twistingSheaf 𝒜 m, U) →ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 n, U) →ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 (m + n), U) := LinearMap.mk₂ Γ(Proj 𝒜, U) (fun s t ↦ ⟨s.1 * t.1, isLocallyFraction_mul s.2 t.2⟩) (fun _ _ _ ↦ ext fun _ ↦ add_mul _ _ _) (fun _ _ _ ↦ ext fun _ ↦ mul_assoc _ _ _) (fun _ _ _ ↦ ext fun _ ↦ mul_add _ _ _) (fun _ _ _ ↦ ext fun _ ↦ mul_left_comm _ _ _)
end end AlgebraicGeometry.Proj.twistingSheaf
namespace TauCeti.SheafOfModules section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory Category Limits universe u v v₁ u₁ variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
/-- The sheaf of rings underlying a sheaf of commutative rings on a site; the site-level analogue of `AlgebraicGeometry.Scheme.ringCatSheaf`. -/
abbrev ringCatSheaf (R : Sheaf J CommRingCat.{u}) [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] : Sheaf J RingCat.{u} := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R
end end TauCeti.SheafOfModules
namespace TauCeti.SheafOfModules section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory universe u v₁ u₁ variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}] [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] {M N : SheafOfModules.{u} R}
/-- Local generators exhibit a sheaf of modules as invertible when they freely generate it on a cover and every local generating type has exactly one element. -/
structure _root_.SheafOfModules.LocalGeneratorsData.IsInvertible
    (q : SheafOfModules.LocalGeneratorsData M) : Prop where
  /-- The local generators freely generate the restricted sheaf. -/
  isLocallyFreeData : q.IsLocallyFreeData
  /-- Every local free basis has at least one element. -/
  basisNonempty (i : q.I) : Nonempty (q.generators i).I
  /-- Every local free basis has at most one element. -/
  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I
end end TauCeti.SheafOfModules
namespace TauCeti.SheafOfModules section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory universe u v₁ u₁ variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}] [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] {M N : SheafOfModules.{u} R}
variable (M) in
/-- A sheaf of modules is invertible if it is locally free of rank one. The witness is local generator data whose free presentations are isomorphisms and whose basis types have exactly one element. -/
class IsInvertible : Prop where
  /-- A rank-one local trivialization of the sheaf. -/
  exists_isInvertible :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u₁} M,
      SheafOfModules.LocalGeneratorsData.IsInvertible q
end end TauCeti.SheafOfModules
namespace TauCeti.AlgebraicGeometry.SheafOfModules section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace universe u variable (X : Scheme.{u})
/-- The object property of being an invertible sheaf on a scheme. -/
abbrev isInvertible : ObjectProperty X.Modules := TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf)
end end TauCeti.AlgebraicGeometry.SheafOfModules
namespace TauCeti.AlgebraicGeometry section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace universe u variable {X : Scheme.{u}}
/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of `𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) : Type _ := ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)
end end TauCeti.AlgebraicGeometry
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 universe u v variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
/-- The symmetric algebra of a finite module is of finite type over the coefficient semiring, without any freeness assumption. -/
instance instFiniteType [Module.Finite R M] : Algebra.FiniteType R (SymmetricAlgebra R M) := by
  -- This finite-free presentation argument follows the original proof in
  -- `TauCeti.LinearAlgebra.SymmetricAlgebra.Noetherian`, using Mathlib's
  -- `SymmetricAlgebra.equivMvPolynomial` and Tau Ceti's `SymmetricAlgebra.map_surjective`.
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  let : Algebra.FiniteType R (SymmetricAlgebra R (Fin n → R)) :=
    Algebra.FiniteType.equiv inferInstance
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n))).symm
  exact Algebra.FiniteType.of_surjective (SymmetricAlgebra.map R g)
    (SymmetricAlgebra.map_surjective R g hg)
/-- A finite module has a symmetric algebra of finite type over its degree-zero part. -/
instance instFiniteTypeGradeZero [Module.Finite R M] : Algebra.FiniteType (homogeneousSubmodule R M 0) (SymmetricAlgebra R M) := by
  let : IsScalarTower R (homogeneousSubmodule R M 0) (SymmetricAlgebra R M) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := homogeneousSubmodule R M 0)
      (A := SymmetricAlgebra R M) fun r => by simp
  exact Algebra.FiniteType.of_restrictScalars_finiteType R
    (homogeneousSubmodule R M 0) (SymmetricAlgebra R M)
end end TauCeti.SymmetricAlgebra
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 universe u v variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
/-- The symmetric algebra of a finitely presented module is a finitely presented algebra: a surjection `g : Rⁿ → M` with finitely generated kernel presents `SymmetricAlgebra R M` as the polynomial ring in `n` variables modulo the ideal gener... -/
instance instFinitePresentation [Module.FinitePresentation R M] : Algebra.FinitePresentation R (SymmetricAlgebra R M) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.FinitePresentation.fg_ker g hg
  let : Algebra.FinitePresentation R (SymmetricAlgebra R (Fin n → R)) :=
    Algebra.FinitePresentation.equiv
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n))).symm
  classical
  refine Algebra.FinitePresentation.of_surjective (SymmetricAlgebra.map_surjective R g hg)
    ⟨s.image (SymmetricAlgebra.ι R _), ?_⟩
  -- the kernel is generated by the images of the generators of `ker g`
  rw [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom,
    SymmetricAlgebra.ker_map_of_surjective g hg, ← hs, Finset.coe_image]
  refine le_antisymm (Ideal.span_mono (Set.image_mono Submodule.subset_span)) (Ideal.span_le.2 ?_)
  have key : Submodule.span R (s : Set (Fin n → R)) ≤
      ((Ideal.span (SymmetricAlgebra.ι R _ '' s)).restrictScalars R).comap
        (SymmetricAlgebra.ι R (Fin n → R)) :=
    Submodule.span_le.2 fun x hx ↦ Ideal.subset_span ⟨x, hx, rfl⟩
  rintro _ ⟨m, hm, rfl⟩
  exact key hm
end end TauCeti.SymmetricAlgebra
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.Module open scoped DirectSum universe u v variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
/-- A version of `SymmetricAlgebra.ι` that maps directly into the graded structure. This is primarily an auxiliary construction used to provide `gradedAlgebra`. -/
noncomputable def GradedAlgebra.ι : M →ₗ[R] ⨁ n, homogeneousSubmodule R M n := DirectSum.lof R ℕ (fun n ↦ homogeneousSubmodule R M n) 1 ∘ₗ (SymmetricAlgebra.ι R M).codRestrict _ (ι_mem_homogeneousSubmodule R M)
/-- The defining formula for `GradedAlgebra.ι`. -/
theorem GradedAlgebra.ι_apply (m : M) : GradedAlgebra.ι R M m = DirectSum.of (fun n ↦ homogeneousSubmodule R M n) 1 ⟨SymmetricAlgebra.ι R M m, ι_mem_homogeneousSubmodule R M m⟩ := by sorry
/-- A symmetric algebra is graded by its homogeneous pieces, without a freeness assumption on `M`. This supplies both the canonical decomposition and the multiplicative graded-algebra API. -/
noncomputable instance gradedAlgebra : GradedAlgebra (homogeneousSubmodule R M) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (GradedAlgebra.ι R M))
    (by
      ext m
      simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, AlgHom.coe_comp, Function.comp_apply,
        SymmetricAlgebra.lift_ι_apply, GradedAlgebra.ι_apply, DirectSum.coeAlgHom_of,
        AlgHom.coe_id, id_eq])
    -- A homogeneous element is a sum of products of `n` generators, so induction on the power
    -- reduces to the degree-one case.
    fun n x ↦ by
      obtain ⟨x, hx⟩ := x
      dsimp only [DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r => rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
      | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, ← map_add]; rfl
      | mem_mul m hm i x hx ih =>
          obtain ⟨_, rfl⟩ := hm
          rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, GradedAlgebra.ι_apply,
            DirectSum.of_mul_of]
          exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/-- The homogeneous decomposition sends each algebra element through the algebra map generated by the degree-one inclusion. -/
theorem gradedAlgebra_decompose (x : SymmetricAlgebra R M) :
    DirectSum.decompose (homogeneousSubmodule R M) x = SymmetricAlgebra.lift (GradedAlgebra.ι R M) x := by sorry
/-- The irrelevant ideal of a symmetric algebra, of the elements with zero degree-zero component, is the kernel of the augmentation `SymmetricAlgebra.algebraMapInv`. -/
theorem toIdeal_irrelevant_eq_ker_algebraMapInv : (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).toIdeal = RingHom.ker (SymmetricAlgebra.algebraMapInv : SymmetricAlgebra R M →ₐ[R] R) := by sorry
/-- Over a domain, the irrelevant ideal of a symmetric algebra is prime: the quotient by it is the base ring. -/
instance isPrime_toIdeal_irrelevant [IsDomain R] : (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).toIdeal.IsPrime := by
  rw [toIdeal_irrelevant_eq_ker_algebraMapInv]
  exact RingHom.ker_isPrime _
/-- Over a field, the irrelevant ideal of a symmetric algebra is maximal: the quotient by it is the base field. -/
instance isMaximal_toIdeal_irrelevant (K : Type*) [Field K] [Module K M] : (HomogeneousIdeal.irrelevant (homogeneousSubmodule K M)).toIdeal.IsMaximal := by
  rw [toIdeal_irrelevant_eq_ker_algebraMapInv]
  exact RingHom.ker_isMaximal_of_surjective _ (SymmetricAlgebra.algebraMap_leftInverse M).surjective
end end TauCeti.SymmetricAlgebra
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory _root_.AlgebraicGeometry universe u variable (R : Type u) (M : Type u) [CommRing R] [AddCommMonoid M] [Module R M]
/-- The structural morphism from the projective spectrum of a symmetric algebra to the spectrum of its coefficient ring. -/
noncomputable def projToSpec : @Quiver.Hom Scheme AlgebraicGeometry.Scheme.instCategory.toCategoryStruct.toQuiver (Proj (homogeneousSubmodule R M)) (Spec (.of R)) := Proj.toSpecZero (homogeneousSubmodule R M) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0)))
/-- The coefficient morphism is `Proj.toSpecZero` followed by the scalar identification. -/
theorem projToSpec_def : projToSpec R M = Proj.toSpecZero (homogeneousSubmodule R M) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0))) := by sorry
/-- Exact source definition of isIso_scalarSpecMap. -/
public theorem isIso_scalarSpecMap : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0)))) := by sorry
attribute [local instance 2500] ConditionallyCompletePartialOrderSup.toSupSet in
/-- The standard opens `D₊(v j)` of a spanning family `v` of linear forms cover the projective spectrum of the symmetric algebra. -/
theorem iSup_basicOpen_ι_eq_top {κ : Type*} (v : κ → M) (hv : Submodule.span R (Set.range v) = ⊤) : ⨆ j, Proj.basicOpen (homogeneousSubmodule R M) (_root_.SymmetricAlgebra.ι R M (v j)) = ⊤ := by sorry
/-- The projective spectrum of a finite module is proper over the coefficient ring. Freeness and projectivity are not required. -/
instance instIsProperProjToSpec [Module.Finite R M] : IsProper (projToSpec R M) := by
  -- Use Mathlib's properness theorem for `Proj.toSpecZero` and the degree-zero equivalence.
  have := isIso_scalarSpecMap R M
  rw [projToSpec_def]
  infer_instance
/-- The projective spectrum of a symmetric algebra is a scheme over its coefficient ring, through the coefficient morphism `projToSpec`. -/
noncomputable instance instOverProj : (Proj (homogeneousSubmodule R M)).Over (Spec (.of R)) := ⟨projToSpec R M⟩
/-- The projective spectrum of a finite module is proper over the coefficient ring, as a scheme over it. -/
instance instIsProperOver [Module.Finite R M] : IsProper (Proj (homogeneousSubmodule R M) ↘ Spec (.of R)) := instIsProperProjToSpec R M
/-- The projective spectrum of a finite module is quasi-compact, over any coefficient ring. -/
instance instCompactSpaceProj [Module.Finite R M] : CompactSpace (Proj (homogeneousSubmodule R M)) := QuasiCompact.compactSpace_of_compactSpace (projToSpec R M)
/-- Over a Noetherian ring, the projective spectrum of a finite module is Noetherian. -/
instance instIsNoetherianProj [Module.Finite R M] [IsNoetherianRing R] :
    IsNoetherian (Proj (homogeneousSubmodule R M)) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (projToSpec R M)
  toCompactSpace := inferInstance
/-- The projective spectrum of a finite module over a Jacobson spectrum is Jacobson. -/
instance instJacobsonSpaceProj [Module.Finite R M] [JacobsonSpace (Spec (.of R))] : JacobsonSpace (Proj (homogeneousSubmodule R M)) := LocallyOfFiniteType.jacobsonSpace (projToSpec R M)
end end TauCeti.SymmetricAlgebra
namespace AlgebraicGeometry.Proj section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory _root_.TopologicalSpace universe u variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
attribute [local instance 2500] ConditionallyCompletePartialOrderSup.toSupSet in
/-- All integer twists are invertible if the standard opens of a family of degree-one elements cover `Proj`. -/
theorem isInvertible_twistingSheaf_of_iSup_eq_top {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1) (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤) (n : ℤ) : TauCeti.SheafOfModules.IsInvertible (R := (Proj 𝒜).ringCatSheaf) (twistingSheaf 𝒜 n) := by sorry
end end AlgebraicGeometry.Proj
namespace TauCeti.SymmetricAlgebra section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.CategoryTheory _root_.TopologicalSpace variable (R M : Type u) [CommRing R] [AddCommMonoid M] [Module R M]
/-- Every integer twisting sheaf on the projective spectrum of a symmetric algebra is invertible, over an arbitrary commutative base ring. -/
instance isInvertible_twistingSheaf (n : ℤ) : TauCeti.SheafOfModules.IsInvertible (R := (AlgebraicGeometry.Proj (homogeneousSubmodule R M)).ringCatSheaf)
      (AlgebraicGeometry.Proj.twistingSheaf (homogeneousSubmodule R M) n) :=
  AlgebraicGeometry.Proj.isInvertible_twistingSheaf_of_iSup_eq_top
    (_root_.SymmetricAlgebra.ι R M)
    (ι_mem_homogeneousSubmodule R M)
    (iSup_basicOpen_ι_eq_top R M id (by simp)) n
end end TauCeti.SymmetricAlgebra
namespace TauCeti.AlgebraicGeometry section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory universe u v
/-- The type of isomorphism classes of line bundles on a scheme. -/
def LineBundleClass (X : Scheme.{u}) : Type _ := Skeleton (InvertibleSheaf X)
end end TauCeti.AlgebraicGeometry
namespace TauCeti.AlgebraicGeometry.LineBundleClass section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory universe u v variable {X : Scheme.{u}}
/-- The isomorphism class of a line bundle. -/
def mk (L : InvertibleSheaf X) : LineBundleClass X := toSkeleton L
end end TauCeti.AlgebraicGeometry.LineBundleClass
namespace PaperVerification.Segre.DiagonalCore section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters PaperVerification.Segre.GenericRigidity PaperVerification.Segre.DiagonalBoxNeighbors open PaperVerification.Segre.ChainInduction variable {J : Type*} [Fintype J] [DecidableEq J]
/-- Exact source definition of minimumSide. -/
def minimumSide (k : ℕ) : ℕ := if k = 3 then 2 else 1
end end PaperVerification.Segre.DiagonalCore
namespace PaperVerification.Segre.TangentKernel section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical open scoped BigOperators variable {ι : Type*} [Fintype ι] [DecidableEq ι] variable {σ : ι → Type*} {R : Type*} [CommRing R] variable [∀ i, Fintype (σ i)]
/-- The coordinate bilinear form as a linear functional in its second argument. -/
def pairing {S : Type*} [Fintype S] (v : S → R) : (S → R) →ₗ[R] R where
  toFun w := ∑ a, v a * w a
  map_add' w z := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_left_comm _ _ _
end end PaperVerification.Segre.TangentKernel
namespace PaperVerification.Segre.FullGraphChartReindex section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical BigOperators open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.Degeneration PaperVerification.Segre.GraphSpan PaperVerification.Segre.CriticalGraph PaperVerification.Segre.SingularSpan PaperVerification.Segre.ProjectiveCharts open PaperVerification.Segre.ProjectivePointSpan PaperVerification.Segre.GraphQuotientElimination PaperVerification.Segre.GraphCriticalElimination open PaperVerification.Segre.CriticalChartReindex _root_.MvPolynomial variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Field K] {n : I → ℕ}
/-- All original factors, with the final factor placed at `none`. -/
abbrev FullFactor (n : I → ℕ) (J : Type) : Option I → Type | none => J | some i => Fin (n i+1)
instance (i : Option I) : Fintype (FullFactor n J i) := by
  cases i <;> dsimp [FullFactor] <;> infer_instance
end end PaperVerification.Segre.FullGraphChartReindex
namespace PaperVerification.Segre.ActualTensorSpan section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical BigOperators TensorProduct open PaperVerification.Segre.TensorFactorReindex variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I] variable (σ : I → Type*) [∀ i,Fintype (σ i)]
/-- The paper's tensor space, using the actual universal tensor product. -/
abbrev Tensor := ⨂[K] i, (σ i → K)
/-- The actual tensor product of the standard coordinate bases. -/
def tensorBasis : Module.Basis (∀ i,σ i) K (Tensor K σ) := Basis.piTensorProduct (fun i => Pi.basisFun K (σ i))
/-- Every tensor entry, in the tensor product of the original coordinate bases. -/
def coefficients : Tensor K σ ≃ₗ[K] ((∀ i,σ i) → K) := (tensorBasis K σ).equivFun
/-- Literal contraction: all other slots are evaluated against their coordinate bilinear pairings, and the remaining slot against a coordinate functional. This uses the actual tensor product of dual maps. -/
def tensorContraction (v : ∀ i,σ i → K) (i : I) : Tensor K σ →ₗ[K] (σ i → K) := LinearMap.pi (fun a => PiTensorProduct.dualDistrib (PiTensorProduct.tprod K (Function.update (fun j => TangentKernel.pairing (v j)) i (LinearMap.proj a : (σ i → K) →ₗ[K] K))))
/-- All original nonzero factor vectors satisfy every genuine tensor contraction proportionality condition. -/
def IsSingularTuple (T : Tensor K σ) (v : ∀ i,σ i → K) : Prop := (∀ i,v i≠0) ∧ ∀ i,∃ c : K,tensorContraction K σ v i T=c • v i
/-- Actual singular rank-one tensors in the actual tensor product. -/
def singularRankOneSet (T : Tensor K σ) : Set (Tensor K σ) := {B | ∃ v : ∀ i,σ i → K,IsSingularTuple K σ T v ∧ B=PiTensorProduct.tprod K v}
/-- Their ordinary linear span inside the original tensor product. -/
def singularSpan (T : Tensor K σ) : Submodule K (Tensor K σ) := Submodule.span K (singularRankOneSet K σ T)
end end PaperVerification.Segre.ActualTensorSpan
namespace PaperVerification.Segre.CriticalFactorReindex section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical BigOperators open PaperVerification.Segre.TensorFactorReindex variable {I I' K : Type*} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Field K] variable {σ : I → Type*} [∀ i, Fintype (σ i)]
/-- The original ordered critical coordinate, with the complete sum over all remaining factor coordinates. The indicator merely avoids introducing a separate index type for the remaining coordinates. -/
def coefficient (T B : (∀ i : I, σ i) → K) (i : I) (a b : σ i) : K := ∑ v : ∀ i, σ i, if v i = a then T v * B (Function.update v i b) - T (Function.update v i b) * B v else 0
/-- Every original critical equation, before restriction to pure tensors. -/
def criticalOperator (T : (∀ i : I, σ i) → K) :
    ((∀ i : I, σ i) → K) →ₗ[K] ((Σ i : I, σ i × σ i) → K) where
  toFun B q := coefficient T B q.1 q.2.1 q.2.2
  map_add' B C := by
    funext q
    unfold coefficient
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v q.1 = q.2.1 <;> simp [h] <;> ring
  map_smul' c B := by
    funext q
    simp only [coefficient, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v q.1 = q.2.1 <;> simp [h] <;> ring
end end PaperVerification.Segre.CriticalFactorReindex
namespace PaperVerification.Segre.ActualTensorCriticalSpace section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical BigOperators TensorProduct open PaperVerification.Segre.ActualTensorSpan variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I] variable (σ : I → Type*) [∀ i, Fintype (σ i)]
/-- The complete linear critical operator on the actual tensor product. Its intrinsic pure-tensor characterization and uniqueness are proved below. -/
def criticalOperator (T : Tensor K σ) : Tensor K σ →ₗ[K] ((Σ i, σ i × σ i) → K) := (CriticalFactorReindex.criticalOperator (coefficients K σ T)).comp (coefficients K σ).toLinearMap
/-- The original full critical subspace of the actual tensor space. -/
def criticalSpace (T : Tensor K σ) : Submodule K (Tensor K σ) := LinearMap.ker (criticalOperator K σ T)
end end PaperVerification.Segre.ActualTensorCriticalSpace
namespace PaperVerification.Segre.ProjectiveSpan section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical LinearAlgebra.Projectivization variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
/-- The original nonzero vectors, regarded as actual projective points. -/
def projectiveImage (s : Set V) : Set (Projectivization K V) := {p | ∃ (v : V) (hv : v ≠ 0), v ∈ s ∧ p = Projectivization.mk K v hv}
end end PaperVerification.Segre.ProjectiveSpan
namespace PaperVerification.Segre.ProjectiveSpan section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical LinearAlgebra.Projectivization variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I] variable (σ : I → Type*) [∀ i, Fintype (σ i)]
/-- Actual singular rank-one projective points of the original tensor. -/
def singularPoints (T : ActualTensorSpan.Tensor K σ) : Set (Projectivization K (ActualTensorSpan.Tensor K σ)) := projectiveImage (ActualTensorSpan.singularRankOneSet K σ T)
end end PaperVerification.Segre.ProjectiveSpan
namespace PaperVerification.Segre.ExcessSixThree section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase PaperVerification.Segre.Monomials PaperVerification.Segre.RankParameters PaperVerification.Segre.GenericRigidity PaperVerification.Segre.DiagonalCore open PaperVerification.Segre.DiagonalBoxNeighbors PaperVerification.Segre.CoreAttachment PaperVerification.Segre.ExcessPropagation PaperVerification.Segre.Degeneration PaperVerification.Segre.KoszulDimension open scoped Matrix
/-- Exact source definition of threshold. -/
def threshold (k e L : ℕ) : ℕ := 2 * L + minimumSide k * (e - 2)
end end PaperVerification.Segre.ExcessSixThree
namespace PaperVerification.Segre.PrincipalTensor section set_option maxRecDepth 2048 set_option backward.isDefEq.respectTransparency false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open PaperVerification.Segre.Staircase variable {K : Type} [Field K] [IsAlgClosed K]
/-- Theorem 1.3, faithfully stated in the actual tensor product, over every algebraically closed field and for every nonempty finite numeric format. -/
theorem theorem_1_3 (r : ℕ) (n : Fin (r+1) → ℕ) : ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧ (∃ T : ActualTensorSpan.Tensor K (fun i => Fin (n i+1)), MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i+1)) T) p ≠ 0) ∧ ∀ T : ActualTensorSpan.Tensor K (fun i => Fin (n i+1)), MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i+1)) T) p ≠ 0 → T ∈ ActualTensorSpan.singularSpan K (fun i => Fin (n i+1)) T := by sorry
end end PaperVerification.Segre.PrincipalTensor
namespace PaperVerification.Segre.OriginalProjectivePrincipal section set_option maxRecDepth 2048 set_option backward.isDefEq.respectTransparency false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical LinearAlgebra.Projectivization open PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters PaperVerification.Segre.FullGraphChartReindex PaperVerification.Segre.ActualTensorSpan variable (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I] (σ : I → Type) [∀ i, Fintype (σ i)]
/-- A nonempty principal open in the complete original coefficient space on which the actual tensor and projective statements hold. -/
def GenericProjectiveDefect (d : ℕ) : Prop := ∃ p : MvPolynomial (∀ i, σ i) K, p ≠ 0 ∧ (∃ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0) ∧ ∀ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0 → ∃ hT : T ≠ 0, T ∈ ActualTensorSpan.singularSpan K σ T ∧ Projectivization.mk K T hT ∈ Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) ∧ Module.finrank K (ActualTensorCriticalSpace.criticalSpace K σ T) - Module.finrank K (ActualTensorSpan.singularSpan K σ T) = d ∧ (Module.finrank K (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization.submodule - 1) - (Module.finrank K (Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T)).submodule - 1) = d ∧ (Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) = (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization ↔ d = 0)
/-- A full-span conclusion states equality of the independently defined linear and projective subspaces and membership of the nonzero original tensor. Its coefficient open is explicitly nonempty. -/
def GenericProjectiveFullSpan : Prop := ∃ p : MvPolynomial (∀ i, σ i) K, p ≠ 0 ∧ (∃ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0) ∧ ∀ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0 → ∃ hT : T ≠ 0, T ∈ ActualTensorSpan.singularSpan K σ T ∧ ActualTensorSpan.singularSpan K σ T = ActualTensorCriticalSpace.criticalSpace K σ T ∧ Projectivization.mk K T hT ∈ Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) ∧ Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) = (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization
end end PaperVerification.Segre.OriginalProjectivePrincipal
namespace PaperVerification.Segre.OriginalProjectivePrincipal section set_option maxRecDepth 2048 set_option backward.isDefEq.respectTransparency false set_option backward.isDefEq.respectTransparency.instanceSearchTypes false set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped Classical LinearAlgebra.Projectivization open PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters PaperVerification.Segre.FullGraphChartReindex PaperVerification.Segre.ActualTensorSpan variable {K : Type} [Field K] [IsAlgClosed K]
/-- Corollary 1.2, its projective-line addendum, and every permutation of all factors, in the original genuine tensor and projective spaces. The independent defect-table lemmas evaluate `Principal.kernelDefect` exactly. -/
theorem corollary_1_2 (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveDefect K (fun i => FullFactor n (Option (Ranks n)) (ρ i)) (Principal.kernelDefect k n) := by sorry
/-- The full unbounded projective-line family in every order, including orders in which the originally distinguished factor is moved. If the other small dimension is `b`, the stated defect is exactly `b`. -/
theorem projective_line_family (n : Fin 2 → ℕ) (hpos : ∀ i, 1 ≤ n i) (hline : n 0 = 1 ∨ n 1 = 1) (ρ : Equiv.Perm (Option (Fin 2))) : GenericProjectiveDefect K (fun i => FullFactor n (Option (Ranks n)) (ρ i)) (n 0 * n 1) := by sorry
/-- The matrix addendum includes every nonnegative projective dimension and both factor orders, with no independence premise on the oversized slice family. It asserts equality of actual linear and projective subspaces. -/
theorem matrix_first_excess (n : Fin 1 → ℕ) (ρ : Equiv.Perm (Option (Fin 1))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Ranks n)) (ρ i)) := by sorry
/-- The complete first criterion of Theorem 6.1, in every factor order. -/
theorem theorem_6_1_first (k e : ℕ) (he : 1 ≤ e) (hk : 4 * e ≤ k) (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
/-- The complete three-block criterion of Theorem 6.1, preserving the unbounded ranges of the excess and every smaller factor dimension. -/
theorem theorem_6_1_second (b e k : ℕ) (hb : 4 ≤ b) (he : 1 ≤ e) (hbound : e ≤ 2 ^ b - 3 * b + 1) (hk : 3 * b ≤ k) (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
/-- The literal logarithmic ceiling consequence, with the paper's exact range `e ≥ 3`, and any order of all original tensor factors. -/
theorem theorem_6_1_logarithmic (k e : ℕ) (he : 3 ≤ e) (hk : 3 * ⌈Real.logb 2 (4 * (e : ℝ))⌉ ≤ (k : ℤ)) (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
/-- The exact criterion of Theorem 6.3 and its entire range of larger tuples, as equality of actual linear and projective subspaces. -/
theorem theorem_6_3 (k e L : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e) (hL : DiagonalCore.minimumSide k ≤ L) (hbound : k * ExcessSixThree.threshold k e L + e ≤ (L + 1) ^ (k / 2) + (L + 1) ^ ((k + 1) / 2)) (n : Fin k → ℕ) (hn : ∀ i, ExcessSixThree.threshold k e L ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
/-- The uniform sufficient bound following Theorem 6.3, with membership of the actual nonzero tensor and its projective point on the same open. -/
theorem uniform_large_factors (k e : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e) (n : Fin k → ℕ) (hn : ∀ i, 3 * e ^ 2 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
/-- The improved excess-two bound, for every `k ≥ 3`, every tuple of smaller dimensions at least six, and every order of all tensor factors. -/
theorem excess_two_six (k : ℕ) (hk : 3 ≤ k) (n : Fin k → ℕ) (hn : ∀ i, 6 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + 2))) (ρ i)) := by sorry
/-- The square-root bound following Theorem 6.3, for all excesses at least two and all larger three-factor tuples, in every order of the four tensor factors. -/
theorem three_factor_sqrt_bound (e : ℕ) (he : 2 ≤ e) (n : Fin 3 → ℕ) (hn : ∀ i, 2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊ ≤ n i) (ρ : Equiv.Perm (Option (Fin 3))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
/-- The exact real-root bound following Theorem 6.3 for every number of smaller factors at least four, with the full generic projective conclusion. The root and ceiling are actual real operations, not asymptotic estimates. -/
theorem many_factor_root_bound (k e : ℕ) (hk : 4 ≤ k) (he : 2 ≤ e) (n : Fin k → ℕ) (hn : ∀ i, e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^ (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊ + 4 * k - 2 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) : GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by sorry
end end PaperVerification.Segre.OriginalProjectivePrincipal
namespace PaperVerification.Segre.ThreeChainCores
open PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters
/-- Literal decidability construction from Stage004, used by the source Proposition 5.1. -/
def chainGraph_decidable {J : Type*} [Fintype J] [DecidableEq J] (n : J → ℕ) : DecidableRel (chainGraph n).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))
end PaperVerification.Segre.ThreeChainCores
namespace PaperVerification.Segre.RigidityPrincipal section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 open scoped BigOperators TensorProduct set_option autoImplicit false open _root_.Matrix PaperVerification.Segre.RigidityRank PaperVerification.Segre.GenericRigidity PaperVerification.Segre.Staircase PaperVerification.Segre.RankParameters variable {K I V : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype V]
/-- Proposition 5.1, the nonexceptional case, on an explicitly nonempty open of all actual placements, with no bound on the positive chain lengths. -/
theorem proposition_5_1_rigid [Infinite K] (k : ℕ) (hk : 3 ≤ k) (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) (hex : ∀ h : k = 3, ¬ ChainClassification.ExceptionalTriple (fun i => n (Fin.cast h.symm i))) : ∃ f : MvPolynomial (Cell n × Fin (sideSum n + 1)) K, f ≠ 0 ∧ (∃ p : Matrix (Cell n) (Fin (sideSum n + 1)) K, MvPolynomial.eval (flattenVelocity p) f ≠ 0) ∧ ∀ p : Matrix (Cell n) (Fin (sideSum n + 1)) K, MvPolynomial.eval (flattenVelocity p) f ≠ 0 → affineSpan K (Set.range p) = ⊤ ∧ InfinitesimallyRigidOn (chainGraph n) p Set.univ := by sorry
attribute [local instance] PaperVerification.Segre.ThreeChainCores.chainGraph_decidable in
/-- Proposition 5.1, all three exceptional triples and every factor order, on an explicitly nonempty open of actual stress-free placements. -/
theorem proposition_5_1_stress_free [Infinite K] (n : Fin 3 → ℕ) (hex : ChainClassification.ExceptionalTriple n) : ∃ f : MvPolynomial (Cell n × Fin (sideSum n + 1)) K, f ≠ 0 ∧ (∃ p : Matrix (Cell n) (Fin (sideSum n + 1)) K, MvPolynomial.eval (flattenVelocity p) f ≠ 0) ∧ ∀ p : Matrix (Cell n) (Fin (sideSum n + 1)) K, MvPolynomial.eval (flattenVelocity p) f ≠ 0 → affineSpan K (Set.range p) = ⊤ ∧ 2 * (rigidityMatrix p (endpoints (chainGraph n))).rank = Fintype.card (Edges (chainGraph n)) ∧ ¬ InfinitesimallyRigidOn (chainGraph n) p Set.univ := by sorry
end end PaperVerification.Segre.RigidityPrincipal
namespace PaperVerification.Segre.AsymptoticGrowth section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped BigOperators TensorProduct open _root_.Asymptotics _root_.Filter
/-- The exact three-factor threshold on page 17. -/
def threeFactorThreshold (e : ℕ) : ℕ := 2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊
/-- The reciprocal of the integer ceiling of half the factor count. -/
def rootExponent (k : ℕ) : ℝ := 1 / (((k + 1) / 2 : ℕ) : ℝ)
/-- The exact threshold for a fixed number of at least four smaller factors. -/
def manyFactorThreshold (k e : ℕ) : ℕ := e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉₊ + 4 * k - 2
/-- The exact three-factor sufficient threshold is `2e + O(sqrt e)` as the natural excess tends to infinity. -/
theorem three_factor_growth : (fun e : ℕ => (threeFactorThreshold e : ℝ) - 2 * (e : ℝ)) =O[atTop] (fun e : ℕ => Real.sqrt (e : ℝ)) := by sorry
/-- For every fixed `k ≥ 4`, the exact sufficient threshold is `e + O_k(e^(1/ceil(k/2)))`, with the literal ordinary ceiling in the exponent. -/
theorem many_factor_growth (k : ℕ) (hk : 4 ≤ k) : (fun e : ℕ => (manyFactorThreshold k e : ℝ) - (e : ℝ)) =O[atTop] (fun e : ℕ => (e : ℝ) ^ (1 / ((⌈(k : ℝ) / 2⌉ : ℤ) : ℝ))) := by sorry
end end PaperVerification.Segre.AsymptoticGrowth
namespace PaperVerification.Segre.PrincipalTensor section set_option maxRecDepth 2048 set_option synthInstance.maxHeartbeats 200000 set_option autoImplicit false open scoped BigOperators TensorProduct open PaperVerification.Segre.Staircase variable {K : Type} [Field K] [IsAlgClosed K]
/-- Theorem 1.3 as an explicit finite linear combination. -/
theorem theorem_1_3_finite_linear_combination (r : ℕ) (n : Fin (r + 1) → ℕ) : ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧ (∃ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)), MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0) ∧ ∀ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)), MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0 → ∃ (m : ℕ) (v : Fin m → (∀ i, Fin (n i + 1) → K)) (c : Fin m → K), (∀ j i, v j i ≠ 0) ∧ (∀ j i, ∃ a : K, ActualTensorSpan.tensorContraction K (fun i => Fin (n i + 1)) (v j) i T = a • v j i) ∧ T = ∑ j, c j • PiTensorProduct.tprod K (v j) := by sorry
/-- Theorem 1.3 for every natural number of factors, including the empty format. For a nonempty format this is exactly the original endpoint; for zero factors the actual singular span is the whole empty tensor product. -/
theorem theorem_1_3_all_arities (r : ℕ) (n : Fin r → ℕ) : ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧ (∃ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)), MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0) ∧ ∀ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)), MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0 → T ∈ ActualTensorSpan.singularSpan K (fun i => Fin (n i + 1)) T := by sorry
end end PaperVerification.Segre.PrincipalTensor
