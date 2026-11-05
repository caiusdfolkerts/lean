module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import paper_verification.literal003
public import paper_verification.literal005
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Basis.Prod
import Lean.Elab.Tactic.Omega
public import paper_verification.literal001
public import paper_verification.literal000
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic.Module
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import paper_verification.literal005
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import paper_verification.literal002
public import Mathlib.RingTheory.SimpleModule.Rank
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option Elab.async false

section TAF_LiteralSource_0354
/- Original module: TauCeti.RepresentationTheory.ExteriorPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Exterior powers of representations

This file equips each exterior power of a representation with the induced diagonal action.
Intertwining maps and equivalences pass functorially to exterior powers, and the zeroth and first
exterior powers recover the trivial and original representations.

## Main definitions

* `Representation.exteriorPower` is the induced action on `⋀[R]^d M`.
* `IntertwiningMap.exteriorPower` is the induced map between exterior-power representations.
* `Representation.Equiv.exteriorPower` is the induced equivalence.

## References

The functorial exterior-power API transported here — `exteriorPower.map`, its identity and
composition laws, and the equivalences `exteriorPower.zeroEquiv` and `exteriorPower.oneEquiv` —
is Mathlib's `Mathlib.LinearAlgebra.ExteriorPower.Basic`, by Sophie Morel and Joël Riou.
-/

public section

open scoped TensorProduct

universe u v w w'

variable {R : Type u} {G : Type v} {M : Type w} {N : Type w'}

namespace Representation

section CommRing

variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M]

/-- The action induced by a representation on its `d`th exterior power. -/
noncomputable def exteriorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⋀[R]^d M) where
  toFun g := _root_.exteriorPower.map d (ρ g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

/-- The action on an exterior power is induced by the action on the original representation. -/
@[simp]
theorem exteriorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.exteriorPower d g = _root_.exteriorPower.map d (ρ g) :=
  (rfl)

/-- The exterior-power action applies the original action to every factor of a pure wedge.

This is intentionally not a simp lemma: `exteriorPower_apply` followed by Mathlib's
`exteriorPower.map_apply_ιMulti` already performs this simplification. -/
theorem exteriorPower_apply_ιMulti (ρ : Representation R G M) (d : ℕ) (g : G) (m : Fin d → M) :
    ρ.exteriorPower d g (_root_.exteriorPower.ιMulti R d m) =
      _root_.exteriorPower.ιMulti R d (ρ g ∘ m) := by
  rw [exteriorPower_apply, _root_.exteriorPower.map_apply_ιMulti]

/-- The zeroth exterior power is equivalent to the trivial representation on the scalars. -/
noncomputable def exteriorPowerZeroEquiv (ρ : Representation R G M) :
    (ρ.exteriorPower 0).Equiv (trivial R G R) :=
  .mk (_root_.exteriorPower.zeroEquiv R M) fun g => by
    ext
    simp

/-- The underlying linear equivalence is Mathlib's identification of the zeroth exterior power
with the scalars. -/
@[simp]
theorem exteriorPowerZeroEquiv_toLinearEquiv (ρ : Representation R G M) :
    ρ.exteriorPowerZeroEquiv.toLinearEquiv = _root_.exteriorPower.zeroEquiv R M :=
  (rfl)

/-- The first exterior power is equivalent to the original representation. -/
noncomputable def exteriorPowerOneEquiv (ρ : Representation R G M) : (ρ.exteriorPower 1).Equiv ρ :=
  .mk (_root_.exteriorPower.oneEquiv R M) fun g =>
    _root_.exteriorPower.oneEquiv_naturality (ρ g)

/-- The underlying linear equivalence is Mathlib's identification of the first exterior power
with the module itself. -/
@[simp]
theorem exteriorPowerOneEquiv_toLinearEquiv (ρ : Representation R G M) :
    ρ.exteriorPowerOneEquiv.toLinearEquiv = _root_.exteriorPower.oneEquiv R M :=
  (rfl)

end CommRing

end Representation

namespace Representation.IntertwiningMap

section CommRing

variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- An intertwining map induces an intertwining map on every exterior power. -/
noncomputable def exteriorPower (f : IntertwiningMap ρ σ) (d : ℕ) :
    IntertwiningMap (ρ.exteriorPower d) (σ.exteriorPower d) where
  toLinearMap := _root_.exteriorPower.map d f.toLinearMap
  isIntertwining' g := by
    simp only [Representation.exteriorPower_apply, ← _root_.exteriorPower.map_comp,
      f.isIntertwining']

/-- The underlying linear map is the usual map induced on exterior powers. -/
@[simp]
theorem exteriorPower_toLinearMap (f : IntertwiningMap ρ σ) (d : ℕ) :
    (f.exteriorPower d).toLinearMap = _root_.exteriorPower.map d f.toLinearMap :=
  (rfl)

/-- The induced map sends a pure wedge to the wedge of the images of its factors. -/
@[simp]
theorem exteriorPower_apply_ιMulti (f : IntertwiningMap ρ σ) (d : ℕ) (m : Fin d → M) :
    f.exteriorPower d (_root_.exteriorPower.ιMulti R d m) =
      _root_.exteriorPower.ιMulti R d (f ∘ m) :=
  _root_.exteriorPower.map_apply_ιMulti f.toLinearMap m

/-- Exterior powers preserve identity intertwining maps. -/
@[simp]
theorem exteriorPower_id (d : ℕ) :
    (IntertwiningMap.id ρ).exteriorPower d = IntertwiningMap.id (ρ.exteriorPower d) :=
  IntertwiningMap.ext _root_.exteriorPower.map_id

/-- Exterior powers preserve composition of intertwining maps. -/
@[simp]
theorem exteriorPower_comp {P : Type*} [AddCommGroup P] [Module R P]
    {τ : Representation R G P} (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ) (d : ℕ) :
    (g.comp f).exteriorPower d = (g.exteriorPower d).comp (f.exteriorPower d) :=
  IntertwiningMap.ext <| _root_.exteriorPower.map_comp f.toLinearMap g.toLinearMap

end CommRing

end Representation.IntertwiningMap

namespace Representation.Equiv

section CommRing

variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- An equivalence of representations induces an equivalence of every exterior power. Its
underlying linear map is the map induced by `e` on `d`th exterior powers, and its inverse is the
map induced by `e.symm`. -/
noncomputable def exteriorPower (e : ρ.Equiv σ) (d : ℕ) :
    (ρ.exteriorPower d).Equiv (σ.exteriorPower d) :=
  -- The inverse is given explicitly, rather than obtained from bijectivity, so that
  -- `exteriorPower_symm` holds by definition, as for `TensorProduct.congr`.
  .mk (.ofLinearMap (_root_.exteriorPower.map d e.toLinearMap)
    (_root_.exteriorPower.map d e.symm.toLinearMap) (by ext; simp [Function.comp_def])
    (by ext; simp [Function.comp_def])) (e.toIntertwiningMap.exteriorPower d).isIntertwining'

/-- The underlying linear map is the usual map induced on exterior powers. -/
@[simp]
theorem exteriorPower_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (e.exteriorPower d).toLinearMap = _root_.exteriorPower.map d e.toLinearMap :=
  (rfl)

/-- The induced equivalence sends a pure wedge to the wedge of the images of its factors. -/
@[simp]
theorem exteriorPower_apply_ιMulti (e : ρ.Equiv σ) (d : ℕ) (m : Fin d → M) :
    e.exteriorPower d (_root_.exteriorPower.ιMulti R d m) =
      _root_.exteriorPower.ιMulti R d (e ∘ m) :=
  _root_.exteriorPower.map_apply_ιMulti e.toLinearMap m

/-- Exterior powers preserve identity equivalences. -/
@[simp]
theorem exteriorPower_refl (d : ℕ) :
    (Equiv.refl ρ).exteriorPower d = .refl (ρ.exteriorPower d) :=
  toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective <| by simp

/-- Exterior powers preserve inverses of equivalences. -/
@[simp]
theorem exteriorPower_symm (e : ρ.Equiv σ) (d : ℕ) :
    e.symm.exteriorPower d = (e.exteriorPower d).symm :=
  (rfl)

/-- Exterior powers preserve composition of equivalences. -/
@[simp]
theorem exteriorPower_trans {P : Type*} [AddCommGroup P] [Module R P]
    {τ : Representation R G P} (e : ρ.Equiv σ) (f : σ.Equiv τ) (d : ℕ) :
    (e.trans f).exteriorPower d = (e.exteriorPower d).trans (f.exteriorPower d) :=
  toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective <| by simp

end CommRing

end Representation.Equiv
end
end TAF_LiteralSource_0354

section TAF_LiteralSource_0355
/- Original module: PaperVerification.AlternatingFormsSymmetricPencil -/


/-!
# The actual symmetric-power action preserving the odd pencil

The vector space is `(Symᵗ U)∨ ⊕ Symᵗ⁺¹ U`.  A multiplication operator
`Symᵗ U → Symᵗ⁺¹ U` gives a tensor and hence an exterior two-form.
Naturality of the tensor--Hom equivalence proves covariance of the pencil.
The binary monomial bases identify these two forms, including their signs,
with the original interleaved path quadrics.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct BigOperators Classical

namespace PaperVerification.AlternatingForms.SymmetricPencil

section CrossTensor

variable {K A B G : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

/-- The canonical cross summand in the second exterior power of a direct sum. -/
def crossTensor : A ⊗[K] B →ₗ[K] ⋀[K]^2 (A × B) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => exteriorPair (a, 0) (0, b)
          map_add' := by
            intro b c
            apply Subtype.ext
            simp only [exteriorPair_coe,Submodule.coe_add]
            have he : ((0,b+c) : A×B)=(0,b)+(0,c) := by simp
            rw [he,map_add,mul_add]
          map_smul' := by
            intro r b
            apply Subtype.ext
            simp only [exteriorPair_coe,Submodule.coe_smul,RingHom.id_apply]
            have he : ((0,r • b) : A×B)=r • (0,b) := by simp
            rw [he,map_smul,mul_smul_comm] }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        apply Subtype.ext
        change (exteriorPair ((a+b,0) : A×B) (0,c)).val=
          (exteriorPair (a,0) (0,c)).val+(exteriorPair (b,0) (0,c)).val
        rw [exteriorPair_coe,exteriorPair_coe,exteriorPair_coe]
        have he : ((a+b,0) : A×B)=(a,0)+(b,0) := by simp
        rw [he,map_add,add_mul]
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro b
        apply Subtype.ext
        change (exteriorPair ((r • a,0) : A×B) (0,b)).val=
          r • (exteriorPair (a,0) (0,b)).val
        rw [exteriorPair_coe,exteriorPair_coe]
        have he : ((r • a,0) : A×B)=r • (a,0) := by simp
        rw [he,map_smul,smul_mul_assoc] }

@[simp] theorem crossTensor_tmul (a : A) (b : B) :
    crossTensor (a ⊗ₜ[K] b) = exteriorPair (a, 0) (0, b) := rfl

theorem crossTensor_natural (f : A →ₗ[K] A) (g : B →ₗ[K] B) :
    exteriorPower.map 2 (f.prodMap g) ∘ₗ crossTensor =
      crossTensor ∘ₗ TensorProduct.map f g := by
  apply TensorProduct.ext'
  intro a b
  apply Subtype.ext
  simp [crossTensor_tmul, exteriorPower.coe_map, exteriorPair_coe]

variable [FiniteDimensional K A]

/-- A linear operator defines its canonical cross two-form through the
ordinary tensor--Hom equivalence. -/
def homQuadratic : (A →ₗ[K] B) →ₗ[K] ⋀[K]^2 (Module.Dual K A × B) :=
  crossTensor ∘ₗ (dualTensorHomEquiv K A B).symm.toLinearMap

theorem homQuadratic_eq_matching {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Module.Basis ι K A) (f : A →ₗ[K] B) :
    homQuadratic f = matchingQuadratic
      (fun i => (a.dualBasis i, 0)) (fun i => (0, f (a i))) := by
  have ht : (dualTensorHomEquiv K A B).symm f =
      ∑ i, a.dualBasis i ⊗ₜ[K] f (a i) := by
    apply (dualTensorHomEquiv K A B).injective
    apply LinearMap.ext
    intro x
    simp only [LinearEquiv.apply_symm_apply, map_sum,
      LinearMap.sum_apply, dualTensorHomEquiv_tmul, Module.Basis.dualBasis_apply]
    simp only [← map_smul, ← map_sum, a.sum_repr]
  simp only [homQuadratic, LinearMap.comp_apply, LinearEquiv.coe_coe, ht,
    map_sum, crossTensor_tmul, matchingQuadratic]

variable [Group G]

/-- Naturality is proved for the actual induced exterior action. -/
theorem homQuadratic_equivariant (ρ : Representation K G A)
    (σ : Representation K G B) (g : G) (f : A →ₗ[K] B) :
    (ρ.dual.prod σ).exteriorPower 2 g (homQuadratic f) =
      homQuadratic (ρ.linHom σ g f) := by
  have ht : TensorProduct.map (ρ.dual g) (σ g)
        ((dualTensorHomEquiv K A B).symm f) =
      (dualTensorHomEquiv K A B).symm (ρ.linHom σ g f) := by
    apply (dualTensorHomEquiv K A B).injective
    rw [LinearEquiv.apply_symm_apply]
    change dualTensorHom K A B (TensorProduct.map (ρ.dual g) (σ g)
      ((dualTensorHomEquiv K A B).symm f)) = _
    simpa only [LinearMap.comp_apply,
      dualTensorHom_dualTensorHomEquiv_symm] using
      LinearMap.congr_fun (ρ.dualTensorHom_comm σ g)
        ((dualTensorHomEquiv K A B).symm f)
  rw [Representation.exteriorPower_apply]
  change exteriorPower.map 2 ((ρ.dual g).prodMap (σ g))
    (crossTensor ((dualTensorHomEquiv K A B).symm f)) = _
  rw [← LinearMap.comp_apply, crossTensor_natural, LinearMap.comp_apply, ht]
  rfl

end CrossTensor

section BinaryBasis

variable (K : Type) [Field K]

abbrev Standard := Fin 2 → K
abbrev SymmetricDegree (d : ℕ) := Sym[K]^d (Standard K)

/-- The index counts the second basis vector, as in `bⱼ=xᵈ⁻ʲyʲ`. -/
def binaryIndex (d : ℕ) : Sym (Fin 2) d ≃ Fin (d+1) :=
  (TauCeti.symFinTwoEquiv d).trans Fin.revPerm

def binaryBasis (d : ℕ) : Module.Basis (Fin (d+1)) K (SymmetricDegree K d) :=
  ((Pi.basisFun K (Fin 2)).symmetricPower d).reindex (binaryIndex d)

theorem consMul_symmetricBasis {ι : Type*} {M : Type*} [AddCommGroup M]
    [Module K M] (a : Module.Basis ι K M) (d : ℕ) (i : ι) (s : Sym ι d) :
    SymmetricPower.consMul K M d (a i) (a.symmetricPower d s) =
      a.symmetricPower (d+1) (i ::ₛ s) := by
  obtain ⟨f, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  simp only [Module.Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn,
    SymmetricPower.consMul_tprod, ← TauCeti.Sym.ofFn_cons,
    SymmetricPower.tprodOfSym_ofFn]
  congr 1
  funext j
  cases j using Fin.cases <;> rfl

theorem binaryIndex_cons_zero (d : ℕ) (s : Sym (Fin 2) d) :
    binaryIndex (d+1) (0 ::ₛ s) = (binaryIndex d s).castSucc := by
  apply Fin.ext
  simp only [binaryIndex, Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev,
    TauCeti.coe_symFinTwoEquiv_apply, Sym.coe_cons, Multiset.count_cons_self,
    Fin.val_castSucc]
  have hc : Multiset.count (0 : Fin 2) (s : Multiset (Fin 2)) ≤ d := by
    simpa only [Sym.card_coe] using
      Multiset.count_le_card (0 : Fin 2) (s : Multiset (Fin 2))
  omega

theorem binaryIndex_cons_one (d : ℕ) (s : Sym (Fin 2) d) :
    binaryIndex (d+1) (1 ::ₛ s) = (binaryIndex d s).succ := by
  apply Fin.ext
  simp only [binaryIndex, Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev,
    TauCeti.coe_symFinTwoEquiv_apply, Sym.coe_cons, Multiset.count_cons_of_ne
      (by decide : (0 : Fin 2) ≠ 1), Fin.val_succ]
  have hc : Multiset.count (0 : Fin 2) (s : Multiset (Fin 2)) ≤ d := by
    simpa only [Sym.card_coe] using
      Multiset.count_le_card (0 : Fin 2) (s : Multiset (Fin 2))
  omega

theorem consMul_binaryBasis_zero (d : ℕ) (i : Fin (d+1)) :
    SymmetricPower.consMul K (Standard K) d (Pi.basisFun K (Fin 2) 0)
      (binaryBasis K d i) = binaryBasis K (d+1) i.castSucc := by
  simp only [binaryBasis, Module.Basis.reindex_apply]
  rw [consMul_symmetricBasis]
  change (Pi.basisFun K (Fin 2)).symmetricPower (d+1) _ =
    (Pi.basisFun K (Fin 2)).symmetricPower (d+1) ((binaryIndex (d+1)).symm _)
  apply congrArg ((Pi.basisFun K (Fin 2)).symmetricPower (d+1))
  apply (binaryIndex (d+1)).injective
  rw [binaryIndex_cons_zero, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem consMul_binaryBasis_one (d : ℕ) (i : Fin (d+1)) :
    SymmetricPower.consMul K (Standard K) d (Pi.basisFun K (Fin 2) 1)
      (binaryBasis K d i) = binaryBasis K (d+1) i.succ := by
  simp only [binaryBasis, Module.Basis.reindex_apply]
  rw [consMul_symmetricBasis]
  change (Pi.basisFun K (Fin 2)).symmetricPower (d+1) _ =
    (Pi.basisFun K (Fin 2)).symmetricPower (d+1) ((binaryIndex (d+1)).symm _)
  apply congrArg ((Pi.basisFun K (Fin 2)).symmetricPower (d+1))
  apply (binaryIndex (d+1)).injective
  rw [binaryIndex_cons_one, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end BinaryBasis

section Pencil

variable (K : Type) [Field K]

abbrev Model (t : ℕ) := Module.Dual K (SymmetricDegree K t) × SymmetricDegree K (t+1)

def modelRepresentation (t : ℕ) : Representation K (GL (Fin 2) K) (Model K t) :=
  (TauCeti.symPowerRep K 2 t).dual.prod (TauCeti.symPowerRep K 2 (t+1))

/-- Multiplication by a vector is the two-dimensional pencil, without a
choice of basis or any presumed invariance. -/
def pencil (t : ℕ) : Standard K →ₗ[K] ⋀[K]^2 (Model K t) :=
  homQuadratic ∘ₗ SymmetricPower.consMul K (Standard K) t

theorem symmetricPower_map_consMul (t : ℕ) (L : Standard K →ₗ[K] Standard K)
    (u : Standard K) (v : SymmetricDegree K t) :
    SymmetricPower.map (ι := Fin (t+1)) L
      (SymmetricPower.consMul K (Standard K) t u v) =
    SymmetricPower.consMul K (Standard K) t (L u)
      (SymmetricPower.map (ι := Fin t) L v) := by
  suffices h : SymmetricPower.map (ι := Fin (t+1)) L ∘ₗ
      SymmetricPower.consMul K (Standard K) t u =
      SymmetricPower.consMul K (Standard K) t (L u) ∘ₗ
        SymmetricPower.map (ι := Fin t) L from LinearMap.congr_fun h v
  apply SymmetricPower.ext
  intro f
  simp only [LinearMap.comp_apply, SymmetricPower.consMul_tprod,
    SymmetricPower.map_tprod]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

theorem multiplication_equivariant (t : ℕ) (g : GL (Fin 2) K) (u : Standard K) :
    (TauCeti.symPowerRep K 2 t).linHom (TauCeti.symPowerRep K 2 (t+1)) g
      (SymmetricPower.consMul K (Standard K) t u) =
    SymmetricPower.consMul K (Standard K) t (TauCeti.stdRep K 2 g u) := by
  apply LinearMap.ext
  intro v
  simp only [Representation.linHom_apply, LinearMap.comp_apply,
    TauCeti.symPowerRep, Representation.symmetricPower_apply]
  rw [symmetricPower_map_consMul]
  have hi : SymmetricPower.map (ι := Fin t) (TauCeti.stdRep K 2 g)
      (SymmetricPower.map (ι := Fin t) (TauCeti.stdRep K 2 g⁻¹) v) = v := by
    have hinv : (TauCeti.symPowerRep K 2 t g)
        (TauCeti.symPowerRep K 2 t g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    simpa only [TauCeti.symPowerRep, Representation.symmetricPower_apply] using hinv
  rw [hi]

/-- The actual group action carries multiplication by `u` to multiplication
by `g u`, so the original two-dimensional relation space is invariant. -/
theorem pencil_equivariant (t : ℕ) (g : GL (Fin 2) K) (u : Standard K) :
    (modelRepresentation K t).exteriorPower 2 g (pencil K t u) =
      pencil K t (TauCeti.stdRep K 2 g u) := by
  change (modelRepresentation K t).exteriorPower 2 g
    (homQuadratic (SymmetricPower.consMul K (Standard K) t u)) = _
  rw [modelRepresentation, homQuadratic_equivariant, multiplication_equivariant]
  exact (LinearMap.comp_apply homQuadratic
    (SymmetricPower.consMul K (Standard K) t) (TauCeti.stdRep K 2 g u)).symm

def modelBasis (t : ℕ) : Module.Basis (Fin (2*(t+1)+1)) K (Model K t) :=
  ((binaryBasis K t).dualBasis.prod (binaryBasis K (t+1))).reindex (TopInterlacing.abIndex (t+1))

theorem modelBasis_middle (t : ℕ) (i : Fin (t+1)) :
    modelBasis K t (oddPathMiddle i) = ((binaryBasis K t).dualBasis i, 0) := by
  change modelBasis K t ((TopInterlacing.abIndex (t+1)) (Sum.inl i)) = _
  simp [modelBasis, Module.Basis.prod_apply]

theorem modelBasis_first (t : ℕ) (i : Fin (t+1)) :
    modelBasis K t (oddPathFirstLeft i) = (0, binaryBasis K (t+1) i.castSucc) := by
  change modelBasis K t ((TopInterlacing.abIndex (t+1)) (Sum.inr i.castSucc)) = _
  simp [modelBasis, Module.Basis.prod_apply]

theorem modelBasis_second (t : ℕ) (i : Fin (t+1)) :
    modelBasis K t (oddPathSecondRight i) = (0, binaryBasis K (t+1) i.succ) := by
  change modelBasis K t ((TopInterlacing.abIndex (t+1)) (Sum.inr i.succ)) = _
  simp [modelBasis, Module.Basis.prod_apply]

theorem pencil_zero_eq_path (t : ℕ) :
    pencil K t (Pi.basisFun K (Fin 2) 0) = -oddPathFirstQuadratic (modelBasis K t) := by
  rw [pencil, LinearMap.comp_apply, homQuadratic_eq_matching (binaryBasis K t)]
  simp only [oddPathFirstQuadratic, matchingQuadratic, consMul_binaryBasis_zero,
    modelBasis_first, modelBasis_middle, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Subtype.ext
  simp only [exteriorPair_coe, Submodule.coe_neg]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem pencil_one_eq_path (t : ℕ) :
    pencil K t (Pi.basisFun K (Fin 2) 1) = oddPathSecondQuadratic (modelBasis K t) := by
  rw [pencil, LinearMap.comp_apply, homQuadratic_eq_matching (binaryBasis K t)]
  simp only [oddPathSecondQuadratic, matchingQuadratic, consMul_binaryBasis_one,
    modelBasis_second, modelBasis_middle]

end Pencil
end PaperVerification.AlternatingForms.SymmetricPencil
end
end
end TAF_LiteralSource_0355

section TAF_LiteralSource_0356
/- Original module: PaperVerification.AlternatingFormsBidegreeScaling -/


/-!
# The actual diagonal action distinguishing the two exterior degrees

In the path order `b₀,a₁,b₁,…,aₖ,bₖ`, scale the odd positions by a scalar
and fix the even positions.  Both actual canonical quadratic relations are
scaled by that same scalar.  Hence the action descends to the genuine
exterior quotient in every total degree.  On an exterior word its eigenvalue
is the scalar raised to the number of `a`-letters.  No grading or dimension
formula for the quotient is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.Bidegree

section Diagonal

variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A literal diagonal linear map in the specified original vector basis. -/
def basisScaling (B : Module.Basis I K M) (δ : I → ℕ) (c : K) : M →ₗ[K] M :=
  B.constr K (fun i => c ^ δ i • B i)

@[simp] theorem basisScaling_basis (B : Module.Basis I K M) (δ : I → ℕ)
    (c : K) (i : I) : basisScaling B δ c (B i)=c ^ δ i • B i :=
  Module.Basis.constr_basis _ _ _ _

/-- Scaling on an actual alternating word multiplies the diagonal weights. -/
theorem basisScaling_word (B : Module.Basis I K M) (δ : I → ℕ)
    (c : K) (s : ℕ) (a : Fin s → I) :
    exteriorPower.map s (basisScaling B δ c)
        (exteriorPower.ιMulti K s (fun j => B (a j)))=
      c ^ (∑ j,δ (a j)) • exteriorPower.ιMulti K s (fun j => B (a j)) := by
  rw [exteriorPower.map_apply_ιMulti]
  have he : basisScaling B δ c ∘ (fun j => B (a j))=
      fun j => c ^ δ (a j) • B (a j) := by
    funext j
    exact basisScaling_basis B δ c (a j)
  rw [he,AlternatingMap.map_smul_univ,Finset.prod_pow_eq_pow_sum]

end Diagonal

section Relations

variable {K M J : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype J] [DecidableEq J]

/-- Functoriality of the actual matching quadratic, with both endpoint weights. -/
theorem map_matchingQuadratic (L : M →ₗ[K] M) (u v : J → M) (c d : K)
    (hu : ∀ i,L (u i)=c • u i) (hv : ∀ i,L (v i)=d • v i) :
    exteriorPower.map 2 L (matchingQuadratic u v)=(c*d) • matchingQuadratic u v := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map,matchingQuadratic_coe,Submodule.coe_smul,
    map_sum,map_mul,ExteriorAlgebra.map_apply_ι,hu,hv,map_smul,
    smul_mul_assoc,mul_smul_comm,smul_smul,Finset.smul_sum,mul_comm]

/-- The generated relation ideal is carried into itself whenever both
of its actual generators are eigenvectors. -/
theorem relationIdeal_map_mem (L : M →ₗ[K] M) (f g : ⋀[K]^2 M) (c d : K)
    (hf : exteriorPower.map 2 L f=c • f) (hg : exteriorPower.map 2 L g=d • g)
    (x : ExteriorAlgebra K M) (hx : x∈exteriorRelationIdeal f g) :
    ExteriorAlgebra.map L x∈exteriorRelationIdeal f g := by
  have hf' : ExteriorAlgebra.map L (f : ExteriorAlgebra K M)=c • (f : ExteriorAlgebra K M) := by
    simpa only [exteriorPower.coe_map,Submodule.coe_smul] using congrArg Subtype.val hf
  have hg' : ExteriorAlgebra.map L (g : ExteriorAlgebra K M)=d • (g : ExteriorAlgebra K M) := by
    simpa only [exteriorPower.coe_map,Submodule.coe_smul] using congrArg Subtype.val hg
  obtain ⟨a,b,rfl⟩ := Ideal.mem_span_pair.mp hx
  apply Ideal.mem_span_pair.mpr
  refine ⟨c • ExteriorAlgebra.map L a,d • ExteriorAlgebra.map L b,?_⟩
  simp only [map_add,map_mul,hf',hg',smul_mul_assoc,mul_smul_comm]

/-- The quotient action is justified on the complete homogeneous relation
space, including coefficients of every possible exterior degree. -/
theorem degreeRelations_map_le (L : M →ₗ[K] M) (f g : ⋀[K]^2 M) (c d : K)
    (hf : exteriorPower.map 2 L f=c • f) (hg : exteriorPower.map 2 L g=d • g)
    (s : ℕ) :
    exteriorDegreeRelations f g s≤
      (exteriorDegreeRelations f g s).comap (exteriorPower.map s L) := by
  intro x hx
  change ((exteriorPower.map s L x : ⋀[K]^s M) : ExteriorAlgebra K M)∈
    exteriorRelationIdeal f g
  rw [exteriorPower.coe_map]
  exact relationIdeal_map_mem L f g c d hf hg x hx

end Relations

section OddPath

variable {K : Type*} [Field K]

/-- Zero-based odd path positions are the `a`-variables. -/
def aIndexDegree {k : ℕ} (i : Fin (2*k+1)) : ℕ := if i.val%2=1 then 1 else 0

def aWordDegree {k s : ℕ} (a : Fin s → Fin (2*k+1)) : ℕ :=
  ∑ j,aIndexDegree (a j)

/-- The original vector-space action; in particular no quotient basis is
used to define this endomorphism. -/
def oddScaling (k : ℕ) (c : K) : (Fin (2*k+1) → K) →ₗ[K] (Fin (2*k+1) → K) :=
  basisScaling (Pi.basisFun K (Fin (2*k+1))) aIndexDegree c

@[simp] theorem aIndexDegree_firstLeft {k : ℕ} (i : Fin k) :
    aIndexDegree (oddPathFirstLeft i)=0 := by
  have h : (2*i.val)%2≠1 := by omega
  change (if (2*i.val)%2=1 then 1 else 0)=0
  exact if_neg h

@[simp] theorem aIndexDegree_middle {k : ℕ} (i : Fin k) :
    aIndexDegree (oddPathMiddle i)=1 := by
  have h : (2*i.val+1)%2=1 := by omega
  change (if (2*i.val+1)%2=1 then 1 else 0)=1
  exact if_pos h

@[simp] theorem aIndexDegree_secondRight {k : ℕ} (i : Fin k) :
    aIndexDegree (oddPathSecondRight i)=0 := by
  have h : (2*i.val+2)%2≠1 := by omega
  change (if (2*i.val+2)%2=1 then 1 else 0)=0
  exact if_neg h

@[simp] theorem oddScaling_first (k : ℕ) (c : K) :
    exteriorPower.map 2 (oddScaling k c)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))=
      c • oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) := by
  unfold oddPathFirstQuadratic
  simpa only [one_mul] using
    (map_matchingQuadratic (oddScaling k c)
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathFirstLeft i))
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathMiddle i)) 1 c
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_firstLeft,pow_zero,one_smul])
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_middle,pow_one]))

@[simp] theorem oddScaling_second (k : ℕ) (c : K) :
    exteriorPower.map 2 (oddScaling k c)
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))=
      c • oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) := by
  unfold oddPathSecondQuadratic
  simpa only [mul_one] using
    (map_matchingQuadratic (oddScaling k c)
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathMiddle i))
      (fun i : Fin k => Pi.basisFun K (Fin (2*k+1)) (oddPathSecondRight i)) c 1
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_middle,pow_one])
      (by intro i; simp only [oddScaling,basisScaling_basis,aIndexDegree_secondRight,pow_zero,one_smul]))

/-- The induced endomorphism of the paper's actual homogeneous exterior
quotient.  Ideal preservation is a theorem used in the construction. -/
def quotientScaling (k s : ℕ) (c : K) :
    Module.End K (ExteriorQuotientDegree (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s) :=
  (exteriorDegreeRelations (K := K)
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s).mapQ
    (exteriorDegreeRelations (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s)
    (exteriorPower.map s (oddScaling k c))
    (degreeRelations_map_le (oddScaling k c) _ _ c c
      (oddScaling_first k c) (oddScaling_second k c) s)

@[simp] theorem quotientScaling_word (k s : ℕ) (c : K)
    (a : Fin s → Fin (2*k+1)) :
    quotientScaling k s c (Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j))))=
      c ^ aWordDegree a • Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j))) := by
  rw [quotientScaling,Submodule.mapQ_apply]
  rw [show exteriorPower.map s (oddScaling k c)
      (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j)))=
      c ^ aWordDegree a • exteriorPower.ιMulti K s
        (fun j => Pi.basisFun K (Fin (2*k+1)) (a j)) from
    basisScaling_word _ _ _ _ _]
  exact Submodule.Quotient.mk_smul (R := K) (S := K)
    (p := exteriorDegreeRelations (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s)
    (c ^ aWordDegree a)
    (exteriorPower.ιMulti K s (fun j => Pi.basisFun K (Fin (2*k+1)) (a j)))

/-- Distinct `a`-degrees have distinct eigenvalues in every characteristic-zero
coefficient field; no order on that field is required. -/
theorem two_pow_injective [CharZero K] : Function.Injective (fun p : ℕ => (2 : K)^p) := by
  intro p q h
  apply Nat.pow_right_injective (by decide : 2≤(2 : ℕ))
  apply (Nat.cast_injective (R := K))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

end OddPath
end PaperVerification.AlternatingForms.Bidegree
end
end
end TAF_LiteralSource_0356

section TAF_LiteralSource_0357
/- Original module: PaperVerification.AlternatingFormsBigradedPieces -/


/-!
# The original bidegree pieces of the odd exterior quotient

A piece is defined as the image of the span of the original exterior words
having the specified numbers of `a`- and `b`-letters.  It is not defined by
counting good indices.  The diagonal action constructed from the original
vector space proves that the good basis restricts to these actual images:
scaling the `a`-variables by two separates their degrees over any
characteristic-zero field.  Thus their dimensions really are the weighted
good-word counts that enter Proposition 5.1.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.Bidegree

section EigenCoordinates

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinates of an endomorphism diagonal in a genuine basis. -/
theorem repr_diagonal (B : Module.Basis I K V) (T : Module.End K V) (eigenvalue : I → K)
    (hT : ∀ i,T (B i)=eigenvalue i • B i) (x : V) (i : I) :
    B.repr (T x) i=eigenvalue i * B.repr x i := by
  have he : (B.coord i).comp T=eigenvalue i • B.coord i := by
    apply B.ext
    intro j
    by_cases hji : j=i
    · subst j
      simp only [LinearMap.comp_apply,hT,map_smul,Module.Basis.coord_apply,
        Module.Basis.repr_self,Finsupp.single_eq_same,LinearMap.smul_apply,
        smul_eq_mul,mul_one]
    · simp only [LinearMap.comp_apply,hT,map_smul,Module.Basis.coord_apply,
        Module.Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hji),
        LinearMap.smul_apply,smul_zero]
  simpa only [LinearMap.comp_apply,LinearMap.smul_apply,
    Module.Basis.coord_apply,smul_eq_mul] using LinearMap.congr_fun he x

/-- An actual eigenvector has zero coefficients at all different eigenvalues. -/
theorem eigenvector_coordinate_zero (B : Module.Basis I K V)
    (T : Module.End K V) (eigenvalue : I → K) (hT : ∀ i,T (B i)=eigenvalue i • B i)
    (c : K) (x : V) (hx : T x=c • x) (i : I) (hi : eigenvalue i≠c) :
    B.repr x i=0 := by
  have he := congrArg (fun y : V => B.repr y i) hx
  rw [repr_diagonal B T eigenvalue hT,map_smul,Finsupp.smul_apply,smul_eq_mul] at he
  by_contra hne
  exact hi (mul_right_cancel₀ hne he)

end EigenCoordinates

section ActualPieces

variable {K : Type*} [Field K] [CharZero K]

/-- The original exterior word span with `p` odd-position letters and total
degree `s`, before taking the generated-ideal quotient. -/
def exteriorASubdegree (k s p : ℕ) :
    Submodule K (⋀[K]^s (Fin (2*k+1) → K)) :=
  Submodule.span K {x | ∃ I : PluckerIndex s (2*k+1),
    aWordDegree I.val=p ∧ x=exteriorPluckerBasis s (2*k+1) I}

/-- The image of that original span in the genuine quotient by both quadrics. -/
def quotientASubdegree (k s p : ℕ) :
    Submodule K (OddExteriorQuotientDegree (K := K) k s) :=
  (exteriorASubdegree k s p).map
    (exteriorDegreeRelations
      (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*k+1)))) s).mkQ

/-- The paper's original `(p,q)` piece: total exterior degree `p+q`, with
exactly `p` of the `a`-variables. -/
def actualBigradedPiece (k p q : ℕ) :
    Submodule K (OddExteriorQuotientDegree (K := K) k (p+q)) :=
  quotientASubdegree k (p+q) p

def goodADegree {k s : ℕ} (I : GoodOddIndex k s) : ℕ :=
  aWordDegree I.val.val

theorem quotientScaling_goodBasis (k s : ℕ) (c : K) (I : GoodOddIndex k s) :
    quotientScaling k s c (oddExteriorBasis k s I)=
      c ^ goodADegree I • oddExteriorBasis k s I := by
  rw [oddExteriorBasis_apply,exteriorPluckerBasis_apply]
  exact quotientScaling_word k s c I.val.val

/-- The equality between a piece defined from the original quotient and
the subspace supported on good words of that degree.  The diagonal action
proves the nontrivial direction; the good-word count is not a hypothesis. -/
theorem quotientASubdegree_eq_basisPiece (k s p : ℕ) :
    quotientASubdegree (K := K) k s p=
      BasisDegree.piece (oddExteriorBasis k s) goodADegree p := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro x ⟨I,hI,rfl⟩
    change Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I)∈
      BasisDegree.piece (oddExteriorBasis k s) goodADegree p
    rw [BasisDegree.mem_piece]
    intro J hJ
    apply eigenvector_coordinate_zero (oddExteriorBasis k s)
      (quotientScaling k s (2 : K)) (fun J => (2 : K)^goodADegree J)
      (quotientScaling_goodBasis k s 2) ((2 : K)^p)
      (Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I)) ?_ J
      (fun he => hJ (two_pow_injective he))
    rw [exteriorPluckerBasis_apply,quotientScaling_word,hI]
  · rw [BasisDegree.piece_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨I,hI,rfl⟩
    refine ⟨exteriorPluckerBasis s (2*k+1) I.val,?_,?_⟩
    · exact Submodule.subset_span ⟨I.val,hI,rfl⟩
    · exact (oddExteriorBasis_apply k s I).symm

/-- A genuine direct-sum grading of every actual total-degree quotient,
whose pieces are exactly the images of the original bidegree word spans. -/
def quotientAGrading (k s : ℕ) :
    TauCeti.InternalGrading K (OddExteriorQuotientDegree (K := K) k s) ℕ :=
  BasisDegree.grading (oddExteriorBasis k s) goodADegree

theorem quotientAGrading_piece (k s p : ℕ) :
    (quotientAGrading (K := K) k s).piece p=quotientASubdegree k s p :=
  (quotientASubdegree_eq_basisPiece k s p).symm

/-- Exact all-degree dimension formula for the genuine bidegree image. -/
theorem finrank_quotientASubdegree (k s p : ℕ) :
    Module.finrank K (quotientASubdegree (K := K) k s p)=
      Nat.card {I : GoodOddIndex k s // goodADegree I=p} := by
  rw [←quotientAGrading_piece]
  exact PaperVerification.GradedComponentBasis.finrank_piece
    (quotientAGrading k s) (oddExteriorBasis k s) goodADegree
    (BasisDegree.basis_mem_piece (oddExteriorBasis k s) goodADegree) p

/-- This is the coefficient interpretation used by Proposition5.1; the
remaining weighted path bijection and transfer recurrence are separate proofs. -/
theorem finrank_actualBigradedPiece (k p q : ℕ) :
    Module.finrank K (actualBigradedPiece (K := K) k p q)=
      Nat.card {I : GoodOddIndex k (p+q) // goodADegree I=p} :=
  finrank_quotientASubdegree k (p+q) p

end ActualPieces
end PaperVerification.AlternatingForms.Bidegree
end
end
end TAF_LiteralSource_0357

section TAF_LiteralSource_0358
/- Original module: PaperVerification.AlternatingFormsSymmetricPencilAction -/


/-!
# The compatible group action on the original exterior quotient

The action is induced from the original vector space through the exterior
algebra functor.  Preservation of the generated ideal is proved from the
covariance of its two displayed generators.  Commutation with scaling the
`a`-span proves preservation of every original bidegree component.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.SymmetricPencil

section General

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem degreeRelations_map_le_of_span (f g : ⋀[K]^2 M) (L : M →ₗ[K] M)
    (hf : exteriorPower.map 2 L f ∈ Submodule.span K ({f,g} : Set (⋀[K]^2 M)))
    (hg : exteriorPower.map 2 L g ∈ Submodule.span K ({f,g} : Set (⋀[K]^2 M)))
    (s : ℕ) : exteriorDegreeRelations f g s ≤
      (exteriorDegreeRelations f g s).comap (exteriorPower.map s L) := by
  have h : exteriorRelationIdeal f g ≤
      (exteriorRelationIdeal f g).comap (ExteriorAlgebra.map L) := by
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · have hh := quadraticSpan_le_exteriorDegreeRelations f g hf
      change (exteriorPower.map 2 L f : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g at hh
      change ExteriorAlgebra.map L (f : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g
      rw [exteriorPower.coe_map] at hh
      exact hh
    · have hh := quadraticSpan_le_exteriorDegreeRelations f g hg
      change (exteriorPower.map 2 L g : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g at hh
      change ExteriorAlgebra.map L (g : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g
      rw [exteriorPower.coe_map] at hh
      exact hh
  intro x hx
  change exteriorPower.map s L x ∈ exteriorDegreeRelations f g s
  change (exteriorPower.map s L x : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g
  rw [exteriorPower.coe_map]
  exact h hx

end General

section OriginalAction

variable (K : Type) [Field K]

abbrev Coordinates (t : ℕ) := Fin (2*(t+1)+1) → K

def coordinateEquiv (t : ℕ) : Coordinates K t ≃ₗ[K] Model K t :=
  standardBasisEquiv (modelBasis K t)

/-- The actual original vector representation, obtained by the displayed
monomial-basis coordinate change. -/
def coordinateRepresentation (t : ℕ) :
    Representation K (GL (Fin 2) K) (Coordinates K t) where
  toFun g := (coordinateEquiv K t).symm.toLinearMap ∘ₗ
    modelRepresentation K t g ∘ₗ (coordinateEquiv K t).toLinearMap
  map_one' := by
    ext x
    simp only [map_one, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    ext x
    simp only [map_mul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply]

@[simp] theorem coordinateRepresentation_equiv (t : ℕ) (g : GL (Fin 2) K)
    (x : Coordinates K t) :
    coordinateEquiv K t (coordinateRepresentation K t g x) =
      modelRepresentation K t g (coordinateEquiv K t x) := by
  change coordinateEquiv K t ((coordinateEquiv K t).symm _) = _
  exact (coordinateEquiv K t).apply_symm_apply _

def coordinateRepresentationEquiv (t : ℕ) :
    (coordinateRepresentation K t).Equiv (modelRepresentation K t) :=
  .mk (coordinateEquiv K t) (fun g => by
    apply LinearMap.ext
    intro x
    exact coordinateRepresentation_equiv K t g x)

theorem coordinate_exterior_intertwining (t s : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map s (coordinateEquiv K t).toLinearMap ∘ₗ
        exteriorPower.map s (coordinateRepresentation K t g) =
      exteriorPower.map s (modelRepresentation K t g) ∘ₗ
        exteriorPower.map s (coordinateEquiv K t).toLinearMap := by
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact coordinateRepresentation_equiv K t g x

theorem pencil_decompose (t : ℕ) (u : Standard K) :
    pencil K t u = u 0 • (-oddPathFirstQuadratic (modelBasis K t)) +
      u 1 • oddPathSecondQuadratic (modelBasis K t) := by
  have hu : u = u 0 • Pi.basisFun K (Fin 2) 0 + u 1 • Pi.basisFun K (Fin 2) 1 := by
    simpa only [Fin.sum_univ_two, Pi.basisFun_repr] using
      ((Pi.basisFun K (Fin 2)).sum_repr u).symm
  conv_lhs => rw [hu]
  rw [map_add, map_smul, map_smul, pencil_zero_eq_path, pencil_one_eq_path]

theorem model_first_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (modelRepresentation K t g)
      (oddPathFirstQuadratic (modelBasis K t)) =
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 • oddPathFirstQuadratic (modelBasis K t) -
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 • oddPathSecondQuadratic (modelBasis K t) := by
  have h := pencil_equivariant K t g (Pi.basisFun K (Fin 2) 0)
  rw [pencil_zero_eq_path, Representation.exteriorPower_apply, map_neg,
    pencil_decompose] at h
  simp only [TauCeti.stdRep_apply_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] at h
  have hh := congrArg (fun x : ⋀[K]^2 (Model K t) => -x) h
  simpa only [neg_neg,neg_add,smul_neg,sub_eq_add_neg] using hh

theorem model_second_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (modelRepresentation K t g)
      (oddPathSecondQuadratic (modelBasis K t)) =
    -(g : Matrix (Fin 2) (Fin 2) K) 0 1 • oddPathFirstQuadratic (modelBasis K t) +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 • oddPathSecondQuadratic (modelBasis K t) := by
  have h := pencil_equivariant K t g (Pi.basisFun K (Fin 2) 1)
  rw [pencil_one_eq_path, Representation.exteriorPower_apply, pencil_decompose] at h
  simp only [TauCeti.stdRep_apply_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply,smul_neg] at h
  exact h.trans (congrArg
    (fun x : ⋀[K]^2 (Model K t) =>
      x+(g : Matrix (Fin 2) (Fin 2) K) 1 1 • oddPathSecondQuadratic (modelBasis K t))
    (neg_smul ((g : Matrix (Fin 2) (Fin 2) K) 0 1)
      (oddPathFirstQuadratic (modelBasis K t))).symm)

theorem coordinate_first_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (coordinateRepresentation K t g)
      (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) =
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 •
        oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) -
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 •
        oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) := by
  apply (exteriorPowerLinearEquiv (coordinateEquiv K t) 2).injective
  change exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _ =
    exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _
  rw [← LinearMap.comp_apply, coordinate_exterior_intertwining,
    LinearMap.comp_apply, map_sub, map_smul, map_smul]
  simpa only [coordinateEquiv, oddPathFirstQuadratic_standardBasisEquiv,
    oddPathSecondQuadratic_standardBasisEquiv] using model_first_covariance K t g

theorem coordinate_second_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (coordinateRepresentation K t g)
      (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) =
    -(g : Matrix (Fin 2) (Fin 2) K) 0 1 •
        oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 •
        oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) := by
  apply (exteriorPowerLinearEquiv (coordinateEquiv K t) 2).injective
  change exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _ =
    exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _
  rw [← LinearMap.comp_apply, coordinate_exterior_intertwining,
    LinearMap.comp_apply, map_add, map_smul, map_smul]
  simpa only [coordinateEquiv, oddPathFirstQuadratic_standardBasisEquiv,
    oddPathSecondQuadratic_standardBasisEquiv] using model_second_covariance K t g

theorem original_relations_invariant (t s : ℕ) (g : GL (Fin 2) K) :
    exteriorDegreeRelations
        (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))))
        (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) s ≤
      (exteriorDegreeRelations
        (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))))
        (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) s).comap
        (exteriorPower.map s (coordinateRepresentation K t g)) := by
  apply degreeRelations_map_le_of_span
  · rw [coordinate_first_covariance]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [coordinate_second_covariance]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The representation on the genuine quotient by both original quadrics. -/
def quotientRepresentation (t s : ℕ) :
    Representation K (GL (Fin 2) K) (OddExteriorQuotientDegree (K := K) (t+1) s) :=
  ((coordinateRepresentation K t).exteriorPower s).quotient _
    (by
      intro g
      simpa only [Representation.exteriorPower_apply] using original_relations_invariant K t s g)

@[simp] theorem quotientRepresentation_mk (t s : ℕ) (g : GL (Fin 2) K)
    (x : ⋀[K]^s (Coordinates K t)) :
    quotientRepresentation K t s g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (exteriorPower.map s (coordinateRepresentation K t g) x) := by
  simp only [quotientRepresentation,Representation.quotient_apply,Submodule.mapQ_apply,
    Representation.exteriorPower_apply]

def modelScaling (t : ℕ) (c : K) : Module.End K (Model K t) :=
  (c • LinearMap.id).prodMap LinearMap.id

theorem coordinateEquiv_scaling (t : ℕ) (c : K) :
    (coordinateEquiv K t).toLinearMap ∘ₗ Bidegree.oddScaling (t+1) c =
      modelScaling K t c ∘ₗ (coordinateEquiv K t).toLinearMap := by
  apply (Pi.basisFun K (Fin (2*(t+1)+1))).ext
  intro j
  obtain ⟨j, rfl⟩ := (TopInterlacing.abIndex (t+1)).surjective j
  cases j with
  | inl i =>
      have ha : Bidegree.aIndexDegree ((TopInterlacing.abIndex (t+1)) (Sum.inl i)) = 1 := by
        simp only [Bidegree.aIndexDegree, TopInterlacing.abIndex]
        have h : (2*i.val+1)%2=1 := by omega
        simp [h]
      simp only [LinearMap.comp_apply, Bidegree.oddScaling, Bidegree.basisScaling_basis,
        ha, pow_one, LinearEquiv.coe_coe, map_smul, coordinateEquiv,
        standardBasisEquiv_basisFun]
      have hi : (TopInterlacing.abIndex (t+1)) (Sum.inl i)=oddPathMiddle i := by
        apply Fin.ext
        rfl
      rw [hi]
      simp [modelBasis_middle,modelScaling]
  | inr i =>
      have ha : Bidegree.aIndexDegree ((TopInterlacing.abIndex (t+1)) (Sum.inr i)) = 0 := by
        simp only [Bidegree.aIndexDegree, TopInterlacing.abIndex]
        have h : (2*i.val)%2≠1 := by omega
        simp [h]
      simp only [LinearMap.comp_apply, Bidegree.oddScaling, Bidegree.basisScaling_basis,
        ha, pow_zero, one_smul, LinearEquiv.coe_coe, coordinateEquiv,
        standardBasisEquiv_basisFun]
      simp [modelBasis, modelScaling, Module.Basis.prod_apply]

theorem coordinate_scaling_commute (t : ℕ) (c : K) (g : GL (Fin 2) K) :
    Bidegree.oddScaling (t+1) c ∘ₗ coordinateRepresentation K t g =
      coordinateRepresentation K t g ∘ₗ Bidegree.oddScaling (t+1) c := by
  apply LinearMap.ext
  intro x
  apply (coordinateEquiv K t).injective
  have hs := LinearMap.congr_fun (coordinateEquiv_scaling K t c)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hs
  simp only [LinearMap.comp_apply]
  rw [hs, coordinateRepresentation_equiv, coordinateRepresentation_equiv, hs]
  change modelScaling K t c (modelRepresentation K t g _) =
    modelRepresentation K t g (modelScaling K t c _)
  simp [modelScaling, modelRepresentation, Representation.prod, map_smul]

theorem quotient_scaling_commute (t s : ℕ) (c : K) (g : GL (Fin 2) K) :
    Bidegree.quotientScaling (t+1) s c ∘ₗ quotientRepresentation K t s g =
      quotientRepresentation K t s g ∘ₗ Bidegree.quotientScaling (t+1) s c := by
  apply Submodule.quot_hom_ext
  intro x
  simp only [LinearMap.comp_apply, quotientRepresentation_mk,
    Bidegree.quotientScaling, Submodule.mapQ_apply]
  congr 1
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    coordinate_scaling_commute, exteriorPower.map_comp, LinearMap.comp_apply]

end OriginalAction

section BigradedAction

variable (K : Type) [Field K] [CharZero K]

theorem quotientScaling_piece (k s p : ℕ)
    (x : OddExteriorQuotientDegree (K := K) k s)
    (hx : x ∈ Bidegree.quotientASubdegree k s p) (c : K) :
    Bidegree.quotientScaling k s c x = c^p • x := by
  rw [Bidegree.quotientASubdegree_eq_basisPiece, BasisDegree.piece_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨I, hI, rfl⟩ := hx
      rw [Bidegree.quotientScaling_goodBasis, hI]
  | zero => rw [map_zero,smul_zero]
  | add x y hx hy hx' hy' => rw [map_add,hx',hy',smul_add]
  | smul a x hx hx' => rw [map_smul,hx',smul_comm]

theorem bigradedPiece_invariant (t p q : ℕ) (g : GL (Fin 2) K) :
    Bidegree.actualBigradedPiece (K := K) (t+1) p q ≤
      (Bidegree.actualBigradedPiece (K := K) (t+1) p q).comap
        (quotientRepresentation K t (p+q) g) := by
  intro x hx
  change quotientRepresentation K t (p+q) g x ∈ Bidegree.quotientASubdegree _ _ _
  rw [Bidegree.quotientASubdegree_eq_basisPiece, BasisDegree.mem_piece]
  intro I hI
  apply Bidegree.eigenvector_coordinate_zero (oddExteriorBasis (t+1) (p+q))
    (Bidegree.quotientScaling (t+1) (p+q) (2 : K))
    (fun J => (2 : K)^Bidegree.goodADegree J)
    (Bidegree.quotientScaling_goodBasis (t+1) (p+q) 2) ((2 : K)^p)
    (quotientRepresentation K t (p+q) g x) ?_ I
    (fun h => hI (Bidegree.two_pow_injective h))
  rw [← LinearMap.comp_apply, quotient_scaling_commute, LinearMap.comp_apply,
    quotientScaling_piece K (t+1) (p+q) p x hx 2, map_smul]

/-- The compatible action on the paper's original `(p,q)` quotient piece.
Its carrier remains the independently defined image of the original words. -/
def bigradedRepresentation (t p q : ℕ) :
    Representation K (GL (Fin 2) K)
      (Bidegree.actualBigradedPiece (K := K) (t+1) p q) :=
  (quotientRepresentation K t (p+q)).subrepresentation _
    (bigradedPiece_invariant K t p q)

end BigradedAction
end PaperVerification.AlternatingForms.SymmetricPencil
end
end
end TAF_LiteralSource_0358

section TAF_LiteralSource_0359
/- Original module: TauCeti.Analysis.Matrix.EuclideanLin -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The map of a matrix on Euclidean space

Two ingredients of a linear change of variables on `EuclideanSpace 𝕜 ι`.

Pulling the quadratic form `x ↦ ⟪x, B x⟫` of a square matrix `B` back along the linear map of a
rectangular matrix `A` gives the quadratic form of the congruent matrix `Aᴴ * B * A`. This is
the change-of-variables identity behind every computation of a quadratic statistic after a linear
transformation of the underlying vector.

The rank of a matrix is the rank of the linear map it induces, in both the `ℕ`-valued and the
`Cardinal`-valued sense; this is what lets a matrix-rank statement be read off an operator-rank
one.

Normal square matrices induce normal operators on Euclidean space.
The instance `Matrix.isStarNormal_toEuclideanLin` supplies this normality automatically
from `IsStarNormal A`.

An invertible square matrix induces not just a map but a continuous linear equivalence, whose
inverse is the map of the inverse matrix. That is the form a substitution needs: it supplies the
inverse substitution and, through `LinearMap.det_toLpLin`, the Jacobian.

A square matrix is unitary exactly when its continuous linear map preserves the inner product.

## Main results

* `Matrix.inner_toEuclideanLin_toEuclideanLin` — the quadratic form of `B` at `A x` is the
  quadratic form of `Aᴴ * B * A` at `x`;
* `Matrix.rank_eq_finrank_range_toEuclideanLin`, `Matrix.rank_coe_toEuclideanCLM` — the matrix
  rank is the dimension of the range of the induced map, and the `LinearMap.rank` of the induced
  continuous linear map;
* `Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM` — a matrix is unitary exactly when its
  Euclidean operator preserves the inner product;
* `Matrix.toEuclideanCLE` — the continuous linear equivalence of an invertible matrix, with its
  `apply`, `symm_apply`, coercion and determinant lemmas.
-/

public section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Pulling the quadratic form of `B` back along the linear map of `A` gives the quadratic form
of the congruent matrix `Aᴴ * B * A`. -/
theorem inner_toEuclideanLin_toEuclideanLin (A : Matrix κ ι 𝕜) (B : Matrix κ κ 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin x, B.toEuclideanLin (A.toEuclideanLin x)⟫_𝕜 =
      ⟪x, (Aᴴ * B * A).toEuclideanLin x⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]

omit [Fintype κ] [DecidableEq κ] in
/-- The rank of a matrix is the dimension of the range of the linear map it induces on Euclidean
space. -/
theorem rank_eq_finrank_range_toEuclideanLin [Finite κ] (A : Matrix κ ι 𝕜) :
    A.rank = Module.finrank 𝕜 (LinearMap.range (toEuclideanLin A)) := by
  have : Fintype κ := Fintype.ofFinite κ
  rw [toEuclideanLin_eq_toLin_orthonormal]
  exact A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun κ 𝕜).toBasis
    (EuclideanSpace.basisFun ι 𝕜).toBasis

/-- The `Cardinal`-valued rank of the continuous linear map of a square matrix is its matrix rank.
This is the bridge that turns an operator-rank statement into a matrix-rank one. -/
theorem rank_coe_toEuclideanCLM (A : Matrix ι ι 𝕜) :
    LinearMap.rank
        (toEuclideanCLM (n := ι) (𝕜 := 𝕜) A : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) =
      A.rank := by
  rw [LinearMap.rank, coe_toEuclideanCLM_eq_toEuclideanLin, ← Module.finrank_eq_rank,
    rank_eq_finrank_range_toEuclideanLin]

/-- The continuous linear map of a matrix acts as its Euclidean linear map. -/
@[simp]
theorem toEuclideanCLM_apply (A : Matrix ι ι 𝕜) (x : EuclideanSpace 𝕜 ι) :
    toEuclideanCLM (𝕜 := 𝕜) A x = toEuclideanLin A x := by
  rw [← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe]

/-- A square matrix is unitary exactly when its Euclidean operator preserves the inner product. -/
theorem mem_unitaryGroup_iff_inner_toEuclideanCLM {M : Matrix ι ι 𝕜} :
    M ∈ unitaryGroup ι 𝕜 ↔ ∀ x y : EuclideanSpace 𝕜 ι,
      ⟪toEuclideanCLM (n := ι) (𝕜 := 𝕜) M x, toEuclideanCLM (n := ι) (𝕜 := 𝕜) M y⟫_𝕜 =
        ⟪x, y⟫_𝕜 := by
  refine ⟨fun hM ↦ ContinuousLinearMap.inner_map_map_of_mem_unitary
    (Unitary.map_mem (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) hM), fun h ↦ ?_⟩
  rw [mem_unitaryGroup_iff']
  refine EquivLike.injective (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) ?_
  rw [map_mul, map_star, map_one, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp h

/-- The determinant of a diagonal continuous linear map is the product of its diagonal entries. -/
@[simp]
theorem det_toEuclideanCLM_diagonal (d : ι → 𝕜) :
    (toEuclideanCLM (𝕜 := 𝕜) (diagonal d)).det = ∏ i, d i := by
  rw [ContinuousLinearMap.det, coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearMap.det_toLpLin, det_diagonal]

section Invertible

/-- **The continuous linear equivalence of an invertible matrix** on Euclidean space, defined
when `A.det` is a unit. It acts as `A` does, and its inverse is the map of `A⁻¹`, so a change of
variables along it substitutes `A⁻¹`. -/
noncomputable def toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι :=
  (toEuclideanCLM (𝕜 := 𝕜) A).toContinuousLinearEquivOfDetNeZero <| by
    rw [ContinuousLinearMap.det, coe_toEuclideanCLM_eq_toEuclideanLin, LinearMap.det_toLpLin]
    exact hA

/-- The equivalence acts as the matrix does. -/
@[simp]
theorem toEuclideanCLE_apply (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) (x : EuclideanSpace 𝕜 ι) :
    A.toEuclideanCLE hA x = A.toEuclideanLin x := by
  rw [toEuclideanCLE, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply,
    toEuclideanCLM_apply]

/-- The inverse of the equivalence is the map of the inverse matrix. -/
@[simp]
theorem toEuclideanCLE_symm_apply (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0)
    (y : EuclideanSpace 𝕜 ι) : (A.toEuclideanCLE hA).symm y = A⁻¹.toEuclideanLin y := by
  rw [ContinuousLinearEquiv.symm_apply_eq, toEuclideanCLE_apply]
  simp only [← toEuclideanCLM_apply]
  rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), map_one,
    one_apply_eq_self]

/-- The determinant of the equivalence is the determinant of the matrix. -/
@[simp]
theorem det_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    LinearMap.det (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) = A.det := by
  have hcoe : (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι)
      = A.toEuclideanLin := LinearMap.ext fun x => A.toEuclideanCLE_apply hA x
  rw [hcoe, LinearMap.det_toLpLin]

end Invertible

end Matrix

namespace Matrix

open scoped InnerProductSpace

/-- The coordinate vector formed from the projections of the columns of `A` onto `ν`
satisfies `⟪m, ν⟫ ‖ν‖² = ν ⬝ᵥ A ν`. -/
theorem inner_sum_smul_basisFun_mul_norm_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) :
    ⟪∑ j, (⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2) • EuclideanSpace.basisFun ι ℝ j, ν⟫_ℝ *
      ‖ν‖ ^ 2 = ν.ofLp ⬝ᵥ A *ᵥ ν.ofLp := by
  classical
  have hN : ‖ν‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hν)
  have hcol : ∀ j, ⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ = ∑ i, A i j * ν.ofLp i := fun j => by
    simp [PiLp.inner_apply, mul_comm]
  have hs : ∀ j, ⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2 * ν.ofLp j * ‖ν‖ ^ 2 =
      (∑ i, A i j * ν.ofLp i) * ν.ofLp j := fun j => by
    rw [hcol]
    field_simp
  simp only [sum_inner, real_inner_smul_left, EuclideanSpace.basisFun_inner, Finset.sum_mul, hs]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The operator of a normal matrix on `EuclideanSpace 𝕜 n` is normal. -/
instance isStarNormal_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) [IsStarNormal A] :
    IsStarNormal (toEuclideanLin A) where
  star_comm_self := by
    have h : Aᴴ * A = A * Aᴴ := star_comm_self' A
    rw [commute_iff_eq, LinearMap.star_eq_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← toLpLin_mul_same, ← toLpLin_mul_same, h]

end Matrix
end
end TAF_LiteralSource_0359

section TAF_LiteralSource_0360
/- Original module: TauCeti.Analysis.Normed.Operator.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic facts about bounded operators

For continuous semilinear maps from a seminormed space to a normed space, zero operator norm
forces the map to vanish. The corresponding normed group structure is available as an explicit
construction, including for strong duals of seminormed spaces.

This file also records a shared uniform-bound lemma for continuous linear maps between seminormed
spaces. It lets an evaluation `T i (g i)` pass to the limit when the operators `T i` are eventually
uniformly bounded, their values at the limiting argument converge, and the arguments `g i` converge.
In particular, it supplies the common continuity step for
`StronglyContinuousSemigroup.tendsto_realOperator_apply` and
`StronglyContinuousGroup.tendsto_apply`.

Finally, an operator bounded below is injective
(`ContinuousLinearMap.injective_of_forall_norm_le`), an invertible operator `A` on a normed space
cancels against its inverse (`ContinuousLinearMap.ringInverse_apply_apply`,
`ContinuousLinearMap.apply_ringInverse_apply`) and is bounded below by `‖A⁻¹‖⁻¹`
(`ContinuousLinearMap.norm_le_norm_ringInverse_mul_norm_apply`), and conversely a lower bound
`‖x‖ ≤ M ‖A x‖` bounds the norm of the inverse by `M`
(`ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le`).

The diagonal sum `∑ i ∈ s, A (v i) (v i)` of a continuous bilinear map along vectors of norm at
most one, such as the trace of `A` along an orthonormal basis, is bounded by `#s * ‖A‖`
(`ContinuousLinearMap.norm_sum_apply_apply_le`).

Over `ℝ` or `ℂ`, two-sided norm bounds `1 - δ < ‖T v‖ < 1 + δ` on a `δ`-net of the unit sphere
extend to bounds `(1 - 3 δ) ‖v‖ ≤ ‖T v‖ ≤ (1 + 3 δ) ‖v‖` on the whole space
(`ContinuousLinearMap.norm_apply_bounds_of_net`).
-/

public section

open scoped Topology
open Filter

namespace ContinuousLinearMap

section Semilinear

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- An operator from a seminormed space to a normed space has zero norm exactly when it is zero.
This generalizes `opNorm_zero_iff` to seminormed sources. -/
@[simp]
theorem opNorm_zero_iff' (f : E →SL[σ] F) : ‖f‖ = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext x
    exact norm_le_zero_iff.mp (by simpa only [hf, zero_mul] using f.le_opNorm x)
  · rintro rfl
    exact norm_zero

/-- The nonnegative operator norm vanishes exactly at zero, even for a seminormed source. -/
@[simp]
theorem opNNNorm_eq_zero_iff (f : E →SL[σ] F) : ‖f‖₊ = 0 ↔ f = 0 := by
  simpa only [← NNReal.coe_eq_zero, coe_nnnorm] using f.opNorm_zero_iff'

/-- The extended operator norm vanishes exactly at zero, even for a seminormed source. -/
@[simp]
theorem opENorm_eq_zero_iff (f : E →SL[σ] F) : ‖f‖ₑ = 0 ↔ f = 0 := by
  simpa only [enorm_eq_nnnorm, ENNReal.coe_eq_zero] using f.opNNNorm_eq_zero_iff

/-- Continuous semilinear maps from a seminormed space to a normed space form a normed group
for the operator norm. Use this construction locally when the source is only seminormed. -/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup (E →SL[σ] F) :=
  .ofSeparation fun f ↦ f.opNorm_zero_iff'.mp

end Semilinear

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- If `T i` is eventually uniformly bounded, `T i z` tends to `w`, and `g i` tends to `z`, then
the moving evaluations `T i (g i)` tend to `w`. -/
theorem tendsto_apply_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {T : ι → X →L[𝕜] Y} {C : ℝ} {g : ι → X} {z : X} {w : Y}
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) (hz : Tendsto (fun i => T i z) l (𝓝 w))
    (hg : Tendsto g l (𝓝 z)) : Tendsto (fun i => T i (g i)) l (𝓝 w) := by
  have hmove : Tendsto (fun i => T i (g i - z)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => C * ‖g i - z‖) ?_ ?_
    · filter_upwards [hT] with i hi
      exact (T i).le_of_opNorm_le hi _
    · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul C
  simpa only [map_sub, sub_add_cancel, zero_add] using hmove.add hz

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An operator bounded below, `‖x‖ ≤ M ‖f x‖`, is injective. -/
theorem injective_of_forall_norm_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} {M : ℝ} (h : ∀ x, ‖x‖ ≤ M * ‖f x‖) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
  simpa [hx] using h x

/-- The inverse of an invertible operator undoes the operator. -/
@[simp]
theorem ringInverse_apply_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    Ring.inverse A (A x) = x := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel A hA, one_apply_eq_self]

/-- An invertible operator undoes its inverse. -/
@[simp]
theorem apply_ringInverse_apply {A : E →L[𝕜] E} (hA : IsUnit A) (y : E) :
    A (Ring.inverse A y) = y := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel A hA, one_apply_eq_self]

/-- An invertible operator is bounded below by the reciprocal of the norm of its inverse. -/
theorem norm_le_norm_ringInverse_mul_norm_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    ‖x‖ ≤ ‖Ring.inverse A‖ * ‖A x‖ := by
  calc
    ‖x‖ = ‖Ring.inverse A (A x)‖ := by rw [ringInverse_apply_apply hA]
    _ ≤ ‖Ring.inverse A‖ * ‖A x‖ := le_opNorm _ _

/-- An invertible operator bounded below by `M⁻¹` has an inverse of norm at most `M`. -/
theorem norm_ringInverse_le_of_forall_norm_le {A : E →L[𝕜] E} (hA : IsUnit A) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x, ‖x‖ ≤ M * ‖A x‖) : ‖Ring.inverse A‖ ≤ M := by
  refine opNorm_le_bound _ hM fun y ↦ ?_
  simpa only [apply_ringInverse_apply hA] using h (Ring.inverse A y)

end Inverse

/-- The diagonal sum `∑ i ∈ s, A (v i) (v i)` of a continuous bilinear map along vectors of norm
at most one is bounded by `#s * ‖A‖`. Along an orthonormal basis this bounds the trace of `A` by
the dimension times its norm. -/
theorem norm_sum_apply_apply_le {ι : Type*} (s : Finset ι) (A : X →L[𝕜] X →L[𝕜] Y)
    {v : ι → X} (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) : ‖∑ i ∈ s, A (v i) (v i)‖ ≤ s.card * ‖A‖ := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ ↦ ‖A‖) fun i hi ↦ ?_).trans_eq
    (by simp))
  calc ‖A (v i) (v i)‖ ≤ ‖A‖ * ‖v i‖ * ‖v i‖ := ((A (v i)).le_opNorm _).trans <|
        mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖A‖ * 1 * 1 := by gcongr <;> exact hv i hi
    _ = ‖A‖ := by ring

section Net

variable {𝕜 V F : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Two-sided bounds `1 - δ < ‖T v‖ < 1 + δ` on a `δ`-net of the unit sphere, for `δ ≤ 1 / 6`,
give `(1 - 3 δ) ‖v‖ ≤ ‖T v‖ ≤ (1 + 3 δ) ‖v‖` everywhere. -/
theorem norm_apply_bounds_of_net (T : V →L[𝕜] F) {t : Set V} {δ : ℝ}
    (hnear : ∀ w : V, ‖w‖ = 1 → ∃ v ∈ t, ‖w - v‖ < δ)
    (hlow : ∀ v ∈ t, 1 - δ < ‖T v‖) (hup : ∀ v ∈ t, ‖T v‖ < 1 + δ) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 6) :
    (∀ v, (1 - 3 * δ) * ‖v‖ ≤ ‖T v‖) ∧ ∀ v, ‖T v‖ ≤ (1 + 3 * δ) * ‖v‖ := by
  -- Propagate the upper bound to the unit sphere, and then bound `‖T‖`.
  have hTnorm : ‖T‖ ≤ 1 + 3 * δ := by
    have hbound : ‖T‖ ≤ 1 + δ + ‖T‖ * δ := by
      refine T.opNorm_le_of_unit_norm (by positivity) fun w hw ↦ ?_
      obtain ⟨v, hv, hwv⟩ := hnear w hw
      calc ‖T w‖ = ‖T v + T (w - v)‖ := by rw [map_sub, add_sub_cancel]
        _ ≤ ‖T v‖ + ‖T (w - v)‖ := norm_add_le _ _
        _ ≤ (1 + δ) + ‖T‖ * δ := by
          gcongr
          · exact (hup v hv).le
          · exact (T.le_opNorm _).trans (by gcongr)
    nlinarith [norm_nonneg T]
  -- The lower bound on the unit sphere.
  have hsphere : ∀ w : V, ‖w‖ = 1 → 1 - 3 * δ ≤ ‖T w‖ := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := hnear w hw
    have hTwv : ‖T (w - v)‖ ≤ (1 + 3 * δ) * δ :=
      (T.le_opNorm _).trans (mul_le_mul hTnorm hwv.le (norm_nonneg _) (by positivity))
    have : ‖T v‖ ≤ ‖T w‖ + ‖T (w - v)‖ := by
      calc ‖T v‖ = ‖T w - T (w - v)‖ := by rw [map_sub, sub_sub_cancel]
        _ ≤ ‖T w‖ + ‖T (w - v)‖ := norm_sub_le _ _
    nlinarith [hlow v hv]
  refine ⟨fun v ↦ ?_, fun v ↦ (T.le_opNorm v).trans (by gcongr)⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hTv : ‖T v‖ = ‖v‖ * ‖T ((‖v‖⁻¹ : 𝕜) • v)‖ := by
    simp [norm_smul, hv]
  rw [hTv, mul_comm]
  exact mul_le_mul_of_nonneg_left (hsphere _ (norm_smul_inv_norm hv)) (norm_nonneg v)

end Net

end ContinuousLinearMap

end
end TAF_LiteralSource_0360

section TAF_LiteralSource_0361
/- Original module: TauCeti.Analysis.InnerProductSpace.Adjoint -/
/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, Claude Opus 5
-/


/-!
# Adjoints of linear maps

For bounded operators between complete inner product spaces, the adjoint takes values in the
orthogonal complement of the kernel (`ContinuousLinearMap.adjoint_apply_mem_orthogonal_ker`).
An operator on a Hilbert space is invertible exactly when its adjoint is
(`ContinuousLinearMap.isUnit_adjoint_iff`), and inversion commutes with the adjoint
(`ContinuousLinearMap.ringInverse_adjoint`). An operator on a Hilbert space that is bounded below
by `M⁻¹` and has injective adjoint is invertible with `‖T⁻¹‖ ≤ M`
(`ContinuousLinearMap.isUnit_and_norm_ringInverse_le_of_forall_norm_le`).
For a continuous linear equivalence between complete inner product spaces, the adjoint is
bijective (`ContinuousLinearEquiv.adjoint_bijective`).
Its adjoint gives an equivalence in the reverse direction (`ContinuousLinearEquiv.adjointEquiv`),
with the adjoint of the inverse as inverse.
For a finite-dimensional linear isometry, the adjoint returns its image vectors to their
preimages (`LinearIsometry.adjoint_apply_apply`).

Two families of adjoints of linear maps between finite-dimensional inner product spaces:

* the adjoint of an isometric isomorphism `e : E ≃ₗᵢ[𝕜] F`, viewed as a linear map, is its
  inverse (`LinearIsometryEquiv.adjoint_coe_eq_symm`). This is Mathlib's
  `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm`, stated for the coercion
  `(e : E →ₗ[𝕜] F)` in which compositions with isometric isomorphisms are usually written;
* on the `L²` product `WithLp 2 (E × F)`, the coordinate projections `WithLp.fstₗ` and
  `WithLp.sndₗ` are adjoint to the inclusions `x ↦ (x, 0)` and `y ↦ (0, y)` of the two factors.

Finally, a pointwise bound `‖C x‖ ≤ c * ‖x‖` passes to the adjoint
(`LinearMap.norm_adjoint_apply_le`). This is the operator-norm bound `‖C†‖ ≤ ‖C‖` in pointwise
form for algebraic linear maps, deduced from Mathlib's isometry `ContinuousLinearMap.adjoint`.
If a linear map vanishes on `Tᗮ`, its adjoint takes values in `T`
(`LinearMap.adjoint_apply_mem_of_forall_mem_orthogonal`). The determinant of the adjoint of an
endomorphism is the conjugate of its determinant (`LinearMap.det_adjoint`). For a surjective
linear map, the orthogonal complement of its kernel has the dimension of the codomain
(`LinearMap.finrank_orthogonal_ker_of_surjective`).

Passing a finite-dimensional operator to continuous linear maps preserves its adjoint
(`LinearMap.toContinuousLinearMap_star`) and its normality
(the instance `LinearMap.isStarNormal_toContinuousLinearMap`).

-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

open scoped InnerProduct

/-- The adjoint of a bounded operator takes values in the orthogonal complement of its kernel. -/
theorem adjoint_apply_mem_orthogonal_ker [CompleteSpace E] [CompleteSpace F]
    (u : E →L[𝕜] F) (y : F) : (u†) y ∈ u.kerᗮ := by
  rw [orthogonal_ker]
  exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ y)

section Inverse

variable [CompleteSpace E]

/-- An operator on a Hilbert space that is bounded below by `M⁻¹` and whose adjoint is injective
is invertible, and its inverse has norm at most `M`. -/
theorem isUnit_and_norm_ringInverse_le_of_forall_norm_le {T : E →L[𝕜] E} {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ x, ‖x‖ ≤ M * ‖T x‖) (hT' : Function.Injective (adjoint T)) :
    IsUnit T ∧ ‖Ring.inverse T‖ ≤ M := by
  have hanti : AntilipschitzWith (Real.toNNReal M) T :=
    AddMonoidHomClass.antilipschitz_of_bound T fun x ↦ by
      simpa [Real.coe_toNNReal _ hM] using hT x
  have hdense : T.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, orthogonal_range, LinearMap.ker_eq_bot]
    exact hT'
  have hunit : IsUnit T := isUnit_iff_bijective.mpr
    ((bijective_iff_dense_range_and_antilipschitz T).mpr ⟨hdense, _, hanti⟩)
  exact ⟨hunit, norm_ringInverse_le_of_forall_norm_le hunit hM hT⟩

/-- The adjoint of an operator on a Hilbert space is invertible exactly when the operator is. -/
@[simp]
theorem isUnit_adjoint_iff {A : E →L[𝕜] E} : IsUnit (adjoint A) ↔ IsUnit A := by
  simpa only [star_eq_adjoint] using isUnit_star (a := A)

/-- Inversion commutes with the adjoint. -/
theorem ringInverse_adjoint (A : E →L[𝕜] E) :
    Ring.inverse (adjoint A) = adjoint (Ring.inverse A) := by
  simpa only [star_eq_adjoint] using Ring.inverse_star A

end Inverse

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open scoped InnerProduct

/-- The adjoint of a continuous linear equivalence between Hilbert spaces is bijective. -/
@[simp]
theorem adjoint_bijective [CompleteSpace E] [CompleteSpace F] (e : E ≃L[𝕜] F) :
    Function.Bijective ((e : E →L[𝕜] F)†) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨((e.symm : F →L[𝕜] E)†), ?_, ?_⟩
  · intro x
    simp only [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
      e.coe_comp_coe_symm, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  · intro x
    simp only [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
      e.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]

/-- The adjoint of `A⁻¹` is a left inverse of the adjoint of `A`. -/
@[simp]
theorem adjoint_symm_adjoint_apply [CompleteSpace E] [CompleteSpace F]
    (A : E ≃L[𝕜] F) (x : F) :
    ContinuousLinearMap.adjoint (A.symm : F →L[𝕜] E)
      (ContinuousLinearMap.adjoint (A : E →L[𝕜] F) x) = x := by
  simp [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_id]

/-- The adjoint of a continuous linear equivalence `A`, as an equivalence whose inverse is the
adjoint of `A⁻¹`. -/
noncomputable def adjointEquiv [CompleteSpace E] [CompleteSpace F]
    (A : E ≃L[𝕜] F) : F ≃L[𝕜] E :=
  equivOfInverse (ContinuousLinearMap.adjoint (A : E →L[𝕜] F))
    (ContinuousLinearMap.adjoint (A.symm : F →L[𝕜] E)) (adjoint_symm_adjoint_apply A)
    (adjoint_symm_adjoint_apply A.symm)

/-- Applying the adjoint equivalence is applying the adjoint map. -/
@[simp]
theorem adjointEquiv_apply [CompleteSpace E] [CompleteSpace F]
    (A : E ≃L[𝕜] F) (x : F) :
    A.adjointEquiv x = ContinuousLinearMap.adjoint (A : E →L[𝕜] F) x := by
  exact equivOfInverse_apply _ _ _ _ _

/-- The inverse of the adjoint equivalence is the adjoint equivalence of the inverse. -/
@[simp]
theorem adjointEquiv_symm [CompleteSpace E] [CompleteSpace F] (A : E ≃L[𝕜] F) :
    A.adjointEquiv.symm = A.symm.adjointEquiv := by
  ext x
  apply (A.adjointEquiv.symm_apply_eq).2
  simpa only [adjointEquiv_apply, A.symm_symm] using
    (adjoint_symm_adjoint_apply A.symm x).symm

/-- The inverse adjoint equivalence applies the adjoint of the inverse. -/
theorem adjointEquiv_symm_apply [CompleteSpace E] [CompleteSpace F]
    (A : E ≃L[𝕜] F) (x : E) :
    A.adjointEquiv.symm x = ContinuousLinearMap.adjoint (A.symm : F →L[𝕜] E) x := by
  rw [adjointEquiv_symm, adjointEquiv_apply]

end ContinuousLinearEquiv

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

namespace LinearIsometry

/-- The adjoint of a linear isometry sends each image vector back to its preimage. -/
@[simp]
theorem adjoint_apply_apply (f : E →ₗᵢ[𝕜] F) (x : E) :
    LinearMap.adjoint f.toLinearMap (f x) = x :=
  LinearMap.congr_fun (adjoint_comp_self' f) x

end LinearIsometry

namespace LinearIsometryEquiv

/-- The adjoint of an isometric isomorphism, viewed as a linear map, is its inverse.

Mathlib's `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm` states this for `e.toLinearMap`. The
coercion `(e : E →ₗ[𝕜] F)` instead factors through `e.toContinuousLinearEquiv`, so neither `rw`
nor `simp` can apply that lemma to it. -/
@[simp]
theorem adjoint_coe_eq_symm (e : E ≃ₗᵢ[𝕜] F) :
    LinearMap.adjoint (e : E →ₗ[𝕜] F) = (e.symm : F →ₗ[𝕜] E) :=
  ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ by simpa using e.symm.inner_map_map x (e y)).symm

end LinearIsometryEquiv

namespace WithLp

/-- The adjoint of the first coordinate projection of an `L²` product is the inclusion
`x ↦ (x, 0)` of the first factor. -/
theorem adjoint_fstₗ :
    LinearMap.adjoint (WithLp.fstₗ 2 𝕜 E F) =
      (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ LinearMap.inl 𝕜 E F := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply]

/-- The adjoint of the second coordinate projection of an `L²` product is the inclusion
`y ↦ (0, y)` of the second factor. -/
theorem adjoint_sndₗ :
    LinearMap.adjoint (WithLp.sndₗ 2 𝕜 E F) =
      (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E F := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply]

end WithLp

namespace LinearMap

/-- The orthogonal complement of the kernel of a surjective linear map has the dimension of the
codomain. -/
theorem finrank_orthogonal_ker_of_surjective (f : E →ₗ[𝕜] F) (hf : Function.Surjective f) :
    Module.finrank 𝕜 (ker f)ᗮ = Module.finrank 𝕜 F := by
  rw [orthogonal_ker, finrank_range_adjoint, range_eq_top.mpr hf, finrank_top]

/-- The determinant of the adjoint of an endomorphism is the conjugate of its determinant. -/
@[simp]
theorem det_adjoint (f : E →ₗ[𝕜] E) : (adjoint f).det = star f.det := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [← det_toMatrix b.toBasis, ← det_toMatrix b.toBasis, toMatrix_adjoint b b,
    Matrix.det_conjTranspose]

/-- If `‖C x‖ ≤ c * ‖x‖` for every `x` and `0 ≤ c`, then also `‖C† y‖ ≤ c * ‖y‖` for every `y`. -/
theorem norm_adjoint_apply_le {C : E →ₗ[𝕜] F} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ x, ‖C x‖ ≤ c * ‖x‖) (y : F) : ‖adjoint C y‖ ≤ c * ‖y‖ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  -- The continuous adjoint is an isometry for the operator norm.
  calc ‖adjoint C y‖ = ‖ContinuousLinearMap.adjoint C.toContinuousLinearMap y‖ := by
        rw [← adjoint_toContinuousLinearMap, coe_toContinuousLinearMap']
    _ ≤ c * ‖y‖ := ContinuousLinearMap.le_of_opNorm_le _ (by
        rw [LinearIsometryEquiv.norm_map]
        exact C.toContinuousLinearMap.opNorm_le_bound hc hC) y

/-- If a linear map `A` vanishes on `Tᗮ`, then the adjoint of `A` takes values in `T`. -/
theorem adjoint_apply_mem_of_forall_mem_orthogonal {A : E →ₗ[𝕜] F} {T : Submodule 𝕜 E}
    (hA : ∀ x ∈ Tᗮ, A x = 0) (y : F) : adjoint A y ∈ T :=
  T.orthogonal_orthogonal ▸ Submodule.orthogonal_le (fun x hx ↦ hA x hx)
    (A.orthogonal_ker ▸ mem_range_self _ y)

/-- Passing a finite-dimensional operator to continuous linear maps preserves its adjoint. -/
theorem toContinuousLinearMap_star {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    (T : E →ₗ[𝕜] E) :
    (star T).toContinuousLinearMap = star T.toContinuousLinearMap := by
  rw [LinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]

/-- A finite-dimensional linear operator remains normal when regarded as continuous. -/
instance isStarNormal_toContinuousLinearMap {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    (T : E →ₗ[𝕜] E) [IsStarNormal T] :
    IsStarNormal T.toContinuousLinearMap where
  star_comm_self := by
    rw [← toContinuousLinearMap_star]
    -- The endomorphism algebra equivalence is the multiplicative version of this conversion.
    exact (star_comm_self (x := T)).map (Module.End.toContinuousLinearMap (𝕜 := 𝕜) E)

end LinearMap
end
end TAF_LiteralSource_0361

section TAF_LiteralSource_0362
/- Original module: TauCeti.Analysis.InnerProductSpace.NormalOperator -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Spectral theorems for commuting normal operators

A linear operator `T` on a finite-dimensional complex inner product space is **normal** when it
commutes with its adjoint, `IsStarNormal T`. The spectral theorem says that `T` is then
diagonalized by an orthonormal basis: there is an orthonormal basis of eigenvectors of `T`.
Mathlib proves this for symmetric (self-adjoint) operators,
`LinearMap.IsSymmetric.eigenvectorBasis`; this file extends it to normal ones.

The family theorem `TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute`
constructs a common orthonormal eigenbasis for any commuting family of normal operators,
including infinite families. It applies Mathlib's joint-eigenspace decomposition to all real
and imaginary parts; Fuglede's theorem ensures that these parts commute. The single-operator
spectral theorem follows by taking a singleton family.

Unlike the self-adjoint case, the eigenvalues are complex, and the statement is specific to
complex scalars: a rotation of the real plane is normal but has no real eigenvector.

## Main results

* `TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute`: a common orthonormal
  eigenbasis for any commuting family of normal operators.

* `LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`: **the spectral theorem for
  normal operators**, a normal operator on a finite-dimensional complex inner product space has
  an orthonormal basis of eigenvectors, indexed by any finite type of the right cardinality.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

open Module Module.End ComplexStarModule LinearMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

namespace LinearMap

/-- On a joint eigenspace of the real and imaginary parts of `T`, where `ℜ T` acts by `a` and
`ℑ T` by `b`, the operator `T` acts by `a + i b`. Normality is not needed here; finite
dimensionality only enters because the adjoint, hence `ℜ T` and `ℑ T`, is defined on
finite-dimensional spaces. -/
theorem apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart (T : E →ₗ[ℂ] E)
    {a b : ℂ} {v : E} (ha : v ∈ eigenspace (ℜ T : E →ₗ[ℂ] E) a)
    (hb : v ∈ eigenspace (ℑ T : E →ₗ[ℂ] E) b) :
    T v = (a + Complex.I * b) • v := by
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [LinearMap.add_apply, LinearMap.smul_apply, mem_eigenspace_iff.mp ha,
    mem_eigenspace_iff.mp hb, add_smul,
    mul_smul]

end LinearMap

namespace Commute

/-- Finite-dimensional Fuglede: an operator commuting with a normal operator also commutes
with its adjoint. -/
theorem star_right_of_isStarNormal {T S : E →ₗ[ℂ] E} [IsStarNormal S]
    (h : Commute T S) : Commute T (star S) := by
  have := FiniteDimensional.complete ℂ E
  -- Transfer commutation along the endomorphism algebra equivalence in both directions.
  have hc := h.map (Module.End.toContinuousLinearMap (𝕜 := ℂ) E)
  have hs := IsStarNormal.commute_star_right (a := S.toContinuousLinearMap) inferInstance hc
  rw [← toContinuousLinearMap_star] at hs
  exact hs.of_map (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).injective

/-- The real and imaginary parts of two commuting normal operators commute in all four
combinations. -/
theorem realPart_imaginaryPart_of_isStarNormal {T S : E →ₗ[ℂ] E}
    [IsStarNormal T] [IsStarNormal S] (h : Commute T S) :
    Commute (ℜ T : E →ₗ[ℂ] E) (ℜ S : E →ₗ[ℂ] E) ∧
      Commute (ℜ T : E →ₗ[ℂ] E) (ℑ S : E →ₗ[ℂ] E) ∧
      Commute (ℑ T : E →ₗ[ℂ] E) (ℜ S : E →ₗ[ℂ] E) ∧
      Commute (ℑ T : E →ₗ[ℂ] E) (ℑ S : E →ₗ[ℂ] E) := by
  have h₂ := h.star_right_of_isStarNormal
  have h₃ := h.symm.star_right_of_isStarNormal.symm
  have h₄ := h.star_star
  simp only [realPart_apply_coe, imaginaryPart_apply_coe]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((h.add_right h₂).add_left (h₃.add_right h₄)).smul_left
      ((2 : ℝ)⁻¹) |>.smul_right ((2 : ℝ)⁻¹)
  · exact ((h.sub_right h₂).add_left (h₃.sub_right h₄)).smul_left
      ((2 : ℝ)⁻¹) |>.smul_right ((2 : ℝ)⁻¹) |>.smul_right (-Complex.I)
  · exact ((h.add_right h₂).sub_left (h₃.add_right h₄)).smul_left
      ((2 : ℝ)⁻¹) |>.smul_left (-Complex.I) |>.smul_right ((2 : ℝ)⁻¹)
  · exact ((h.sub_right h₂).sub_left (h₃.sub_right h₄)).smul_left
      ((2 : ℝ)⁻¹) |>.smul_left (-Complex.I) |>.smul_right ((2 : ℝ)⁻¹)
      |>.smul_right (-Complex.I)

end Commute

namespace TauCeti

/-- A commuting family of normal operators has a common orthonormal eigenbasis, indexed by
any finite type of cardinality equal to the dimension. No finiteness of the family is needed. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i, IsStarNormal (T i))
    (hC : Pairwise (fun i j => Commute (T i) (T j)))
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ = finrank ℂ E) :
    ∃ (b : OrthonormalBasis κ ℂ E) (μ : ι → κ → ℂ),
      ∀ i j, T i (b j) = μ i j • b j := by
  classical
  have := FiniteDimensional.complete ℂ E
  have hcomm (i j : ι) : Commute (T i) (T j) :=
    if h : i = j then h ▸ Commute.refl _ else hC h
  -- All real and imaginary parts are symmetric and commute with one another.
  let S : ι × Bool → E →ₗ[ℂ] E := fun p => if p.2 then ℑ (T p.1) else ℜ (T p.1)
  have hS (p : ι × Bool) : (S p).IsSymmetric := by
    dsimp [S]
    split
    · exact (isSymmetric_iff_isSelfAdjoint _).mpr (ℑ _).2
    · exact (isSymmetric_iff_isSelfAdjoint _).mpr (ℜ _).2
  have hSC : Pairwise (fun p q => Commute (S p) (S q)) := by
    intro p q _
    have := hT p.1
    have := hT q.1
    have h := (hcomm p.1 q.1).realPart_imaginaryPart_of_isStarNormal
    rcases p with ⟨i, a⟩
    rcases q with ⟨j, b⟩
    cases a <;> cases b
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  -- Only finitely many joint eigenspaces are nonzero. Choose a basis subordinate to them.
  let V : ((ι × Bool) → ℂ) → Submodule ℂ E := fun χ =>
    ⨅ p, eigenspace (S p) (χ p)
  have hV : DirectSum.IsInternal V :=
    IsSymmetric.directSum_isInternal_of_pairwise_commute hS hSC
  have hO := IsSymmetric.orthogonalFamily_iInf_eigenspaces hS
  let J := {χ : (ι × Bool) → ℂ // V χ ≠ ⊥}
  let _ : Fintype J := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVJ : DirectSum.IsInternal fun χ : J => V χ := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hOJ := hO.comp (Subtype.val_injective (p := fun χ => V χ ≠ ⊥))
  let b := hVJ.subordinateOrthonormalBasis rfl hOJ
  let χ : Fin (finrank ℂ E) → J := fun j =>
    hVJ.subordinateOrthonormalBasisIndex rfl j hOJ
  let e : κ ≃ Fin (finrank ℂ E) := Fintype.equivFinOfCardEq hκ
  refine ⟨b.reindex e.symm, fun i j => (χ (e j)).1 (i, false) +
    Complex.I * (χ (e j)).1 (i, true), fun i j => ?_⟩
  have hmem := hVJ.subordinateOrthonormalBasis_subordinate rfl (e j) hOJ
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  exact (T i).apply_eq_smul_of_mem_eigenspace_realPart_imaginaryPart
    (by simpa [S] using ((Submodule.mem_iInf _).mp hmem (i, false)))
    (by simpa [S] using ((Submodule.mem_iInf _).mp hmem (i, true)))

end TauCeti

open Module

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The spectral theorem for normal operators.** A normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. The basis may be indexed by
any finite type whose cardinality is the dimension of the space. -/
theorem exists_orthonormalBasis_apply_eq_smul_of_isStarNormal (T : E →ₗ[ℂ] E) [IsStarNormal T]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℂ E) :
    ∃ (b : OrthonormalBasis ι ℂ E) (μ : ι → ℂ), ∀ i, T (b i) = μ i • b i := by
  obtain ⟨b, μ, hb⟩ := TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (fun _ : Unit => T) (fun _ => inferInstance) (fun _ _ _ => Commute.refl _) hι
  exact ⟨b, μ (), hb ()⟩

end LinearMap
end
end TAF_LiteralSource_0362

section TAF_LiteralSource_0363
/- Original module: TauCeti.Analysis.Matrix.Normal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Unitary diagonalization of commuting normal matrices

A complex square matrix `A` is **normal** when it commutes with its conjugate transpose,
`IsStarNormal A`. The spectral theorem for normal matrices says that such a matrix is unitarily
diagonalizable: `star U * A * U` is diagonal for some unitary `U`. Mathlib proves this for Hermitian
matrices (`Matrix.IsHermitian.spectral_theorem`); this file extends it to normal ones as the
singleton case of `TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal`.
The columns of `U` are an orthonormal basis of eigenvectors of `A`.
The family theorem gives a single unitary diagonalizer for any commuting family of complex
normal matrices; the family need not be finite.

Unitary matrices are normal, so in particular every unitary matrix is conjugate within the unitary
group to a diagonal one. This is the statement that every element of `U(n)` lies in a conjugate of
the diagonal torus.

## Main results

* `TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal`: a common unitary
  diagonalizer for any commuting family of complex normal matrices.

* `Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`: **the spectral theorem for normal
  matrices**, a normal complex matrix is diagonalized by a unitary matrix.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

namespace TauCeti

open Matrix Module

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A commuting family of complex normal matrices has a common unitary diagonalizer.
The index type of the family need not be finite. -/
theorem exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal
    (A : ι → Matrix n n ℂ) (hA : ∀ i, IsStarNormal (A i))
    (hC : Pairwise (fun i j => Commute (A i) (A j))) :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : ι → n → ℂ,
      ∀ i, star U * A i * U = diagonal (d i) := by
  have hT (i : ι) : IsStarNormal (toEuclideanLin (A i)) := by
    have := hA i
    infer_instance
  have hcomm : Pairwise (fun i j => Commute (toEuclideanLin (A i))
      (toEuclideanLin (A j))) := by
    intro i j hij
    simpa only [commute_iff_eq, Module.End.mul_eq_comp, ← toLpLin_mul_same] using
      congrArg toEuclideanLin (hC hij).eq
  obtain ⟨b, d, hb⟩ := TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (fun i => toEuclideanLin (A i)) hT hcomm (κ := n) finrank_euclideanSpace.symm
  let s := (EuclideanSpace.basisFun n ℂ).toBasis
  have hU : s.toMatrix b.toBasis ∈ unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨_, hU, d, fun k => ?_⟩
  -- The inverse change of orthonormal basis is the conjugate transpose.
  have hstar : star (s.toMatrix b.toBasis) = b.toBasis.toMatrix s := by
    rw [← Matrix.mul_one (star _), ← s.toMatrix_mul_toMatrix_flip b.toBasis,
      ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]
  have hAk : A k = LinearMap.toMatrix s s (toEuclideanLin (A k)) := by
    rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [hstar, hAk, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  by_cases h : i = j <;> simp [LinearMap.toMatrix_apply, hb, h]

end TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral theorem for normal matrices.** A normal complex matrix is unitarily
diagonalizable: there is a unitary matrix `U` with `star U * A * U` diagonal. -/
theorem exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix n n ℂ) [IsStarNormal A] :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, star U * A * U = diagonal d := by
  obtain ⟨U, hU, d, hd⟩ := TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal
    (fun _ : Unit => A) (fun _ => inferInstance) (fun _ _ _ => Commute.refl _)
  exact ⟨U, hU, d (), hd ()⟩

end Matrix
end
end TAF_LiteralSource_0363

section TAF_LiteralSource_0364
/- Original module: TauCeti.Analysis.Matrix.UnitaryGroup.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# `U(n) = Circle · SU(n)`

The determinant of a complex unitary matrix has modulus one, and every point of the circle has a
`card n`-th root there, so a unitary matrix can be rescaled by a scalar of modulus one until its
determinant is one: the unitary group is the product of the scalars of modulus one with the special
unitary group. Rescaling by a scalar of modulus one keeps a matrix unitary, so nothing is lost.

## Main results

* `Circle.coe_mem_unitary`: a point of the circle is a unitary complex number.
* `Matrix.diagonal_mem_unitaryGroup_iff`: a diagonal matrix is unitary exactly when its diagonal
  entries are.
* `Matrix.exists_circle_smul_mem_specialUnitaryGroup`: every complex unitary matrix becomes
  special unitary after multiplication by a suitable scalar of modulus one.
-/

public section

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

/-- A diagonal matrix is unitary exactly when each of its diagonal entries is unitary. -/
@[simp]
theorem diagonal_mem_unitaryGroup_iff {d : n → α} :
    diagonal d ∈ unitaryGroup n α ↔ ∀ i, d i ∈ unitary α := by
  simp only [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff, Pi.star_apply,
    Unitary.mem_iff_self_mul_star]

end Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A point of the circle is a unitary complex number. -/
theorem _root_.Circle.coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ :=
  Unitary.mem_iff_star_mul_self.mpr <| by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]

/-- `U(n) = Circle · SU(n)`: every complex unitary matrix becomes special unitary after
multiplication by a suitable scalar of modulus one. The scalar is a `card n`-th root of the inverse
of the determinant, which has modulus one; the root is taken through `Circle.exp`. -/
theorem _root_.Matrix.exists_circle_smul_mem_specialUnitaryGroup (U : Matrix.unitaryGroup n ℂ) :
    ∃ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.specialUnitaryGroup n ℂ := by
  -- Rescaling by a scalar of modulus one keeps the matrix unitary, whatever the scalar.
  have hunit : ∀ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.unitaryGroup n ℂ := fun c =>
    Unitary.smul_mem_of_mem c.coe_mem_unitary U.2
  rcases isEmpty_or_nonempty n with hn | hn
  · -- With no indices at all every determinant is one and there is nothing to rescale.
    exact ⟨1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hunit 1, Matrix.det_isEmpty⟩⟩
  · have hcard : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnorm : ‖(U : Matrix n n ℂ).det‖ = 1 :=
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective
      (⟨(U : Matrix n n ℂ).det, mem_sphere_zero_iff_norm.mpr hnorm⟩ : Circle)
    have hdetU : (U : Matrix n n ℂ).det = Complex.exp ((θ : ℂ) * Complex.I) := by
      have := congrArg (fun z : Circle => (z : ℂ)) hθ
      rw [Circle.coe_exp] at this
      exact this.symm
    refine ⟨Circle.exp (-(θ / Fintype.card n)), Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨hunit _, ?_⟩⟩
    rw [Matrix.det_smul, Circle.coe_exp, hdetU, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    field_simp
    ring

end TauCeti
end
end TAF_LiteralSource_0364

section TAF_LiteralSource_0365
/- Original module: TauCeti.Analysis.Matrix.UnitaryGroup.Torus -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The diagonal torus of the unitary group

The diagonal unitary matrices form a subgroup `TauCeti.unitaryTorus n` of the unitary group
`U(n) = Matrix.unitaryGroup n ℂ`. A diagonal matrix is unitary exactly when its diagonal entries
have modulus one (`Matrix.diagonal_mem_unitaryGroup_iff`), so this subgroup is the image of the
injective homomorphism `TauCeti.unitaryTorusHom n : (n → Circle) →* U(n)`,
`z ↦ diag (z₁, …, zₙ)`: a product of `card n` circles.

The main result is that **every element of `U(n)` is conjugate into this torus**
(`TauCeti.exists_conj_mem_unitaryTorus`). A unitary matrix is normal, so by the spectral theorem
for normal matrices (`Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`) it is diagonalized
by a unitary change of basis, and the resulting diagonal matrix is again unitary. Read through the
parametrization, every unitary matrix is conjugate in `U(n)` to `diag (z₁, …, zₙ)` for some points
`zᵢ` of the circle, namely its eigenvalues (`TauCeti.exists_isConj_unitaryTorusHom`).

The diagonal torus is commutative and is its own centralizer in `U(n)`
(`TauCeti.centralizer_unitaryTorus`): a unitary matrix commuting with every diagonal unitary
matrix is diagonal. Hence it is a maximal commutative subgroup of `U(n)`
(`TauCeti.eq_unitaryTorus_of_isMulCommutative`), and in particular a maximal torus. Together with
the conjugacy result this is the `U(n)` case of the theorem that a compact connected Lie group is
the union of the conjugates of a maximal torus; for `SU(2)` the same statement is
`TauCeti.SU2.exists_conj_mem_torus`. The Weyl group of this torus is computed in
`TauCeti.Analysis.Matrix.UnitaryGroup.Weyl`.

## Main definitions

* `TauCeti.unitaryTorusHom`: the homomorphism `(n → Circle) →* U(n)` onto the diagonal matrices.
* `TauCeti.unitaryTorus`: the diagonal torus of `U(n)`, its range.

## Main results

* `TauCeti.mem_unitaryTorus_iff`: the diagonal torus consists of the diagonal unitary matrices.
* `TauCeti.centralizer_unitaryTorus`: the diagonal torus is its own centralizer.
* `TauCeti.eq_unitaryTorus_of_isMulCommutative`: the diagonal torus is a maximal commutative
  subgroup of `U(n)`.
* `TauCeti.exists_conj_mem_unitaryTorus`: every element of `U(n)` is conjugate into the diagonal
  torus.
* `TauCeti.exists_isConj_unitaryTorusHom`: every element of `U(n)` is conjugate to
  `diag (z₁, …, zₙ)` for some points `zᵢ` of the circle.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §1.
-/

public section

namespace TauCeti

open Matrix

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The homomorphism `(n → Circle) →* U(n)` sending `z` to the diagonal matrix with diagonal
entries `z i`. Its range is the diagonal torus `TauCeti.unitaryTorus n`. -/
noncomputable def unitaryTorusHom : (n → Circle) →* unitaryGroup n ℂ where
  toFun z := ⟨diagonal fun i => (z i : ℂ),
    diagonal_mem_unitaryGroup_iff.mpr fun i => (z i).coe_mem_unitary⟩
  map_one' := Subtype.ext <| by simp
  map_mul' z w := Subtype.ext <| by simp [diagonal_mul_diagonal]

variable {n}

/-- As a matrix, `TauCeti.unitaryTorusHom n z` is the diagonal matrix with diagonal entries
`z i`. -/
@[simp]
theorem coe_unitaryTorusHom (z : n → Circle) :
    (unitaryTorusHom n z : Matrix n n ℂ) = diagonal fun i => (z i : ℂ) :=
  (rfl)

/-- As an invertible matrix, the diagonal unitary matrix with entries `z i` is the diagonal element
of the general linear group with the entries `z i` viewed as units of `ℂ`. -/
@[simp]
theorem toUnits_unitaryTorusHom (z : n → Circle) :
    Unitary.toUnits (unitaryTorusHom n z) = diagGL fun i => Circle.toUnits (z i) :=
  Units.ext <| by simp

/-- The parametrization `TauCeti.unitaryTorusHom n` of the diagonal torus by `card n` circles is
injective: distinct tuples of circle points give distinct diagonal matrices. -/
theorem unitaryTorusHom_injective : Function.Injective (unitaryTorusHom n) := fun z w h => by
  funext i
  have := congr_fun₂ (congrArg Subtype.val h) i i
  simpa only [coe_unitaryTorusHom, diagonal_apply_eq, Circle.coe_inj] using this

/-- The diagonal parametrization of the unitary torus is continuous. -/
@[fun_prop]
theorem continuous_unitaryTorusHom : Continuous (unitaryTorusHom n) := by
  apply continuous_induced_rng.2
  simp only [Function.comp_def, coe_unitaryTorusHom]
  fun_prop

variable (n) in
/-- The **diagonal torus** of the unitary group `U(n)`: the subgroup of diagonal unitary matrices,
the image of `(n → Circle)` under `TauCeti.unitaryTorusHom n`. -/
noncomputable def unitaryTorus : Subgroup (unitaryGroup n ℂ) :=
  (unitaryTorusHom n).range

/-- An element of `U(n)` lies in the diagonal torus exactly when it is `TauCeti.unitaryTorusHom n z`
for some tuple `z` of circle points. -/
theorem mem_unitaryTorus_iff_exists_unitaryTorusHom {g : unitaryGroup n ℂ} :
    g ∈ unitaryTorus n ↔ ∃ z : n → Circle, unitaryTorusHom n z = g :=
  MonoidHom.mem_range

/-- The diagonal matrix `TauCeti.unitaryTorusHom n z` lies in the diagonal torus. -/
theorem unitaryTorusHom_mem_unitaryTorus (z : n → Circle) :
    unitaryTorusHom n z ∈ unitaryTorus n :=
  ⟨z, rfl⟩

/-- The diagonal torus of `U(n)` consists of exactly the unitary matrices that are diagonal. -/
theorem mem_unitaryTorus_iff {g : unitaryGroup n ℂ} :
    g ∈ unitaryTorus n ↔ (g : Matrix n n ℂ).IsDiag := by
  refine ⟨fun ⟨z, hz⟩ => hz ▸ isDiag_diagonal _, fun hg => ?_⟩
  -- The diagonal entries of a diagonal unitary matrix are unitary, so lie on the circle.
  have hunit := diagonal_mem_unitaryGroup_iff.mp (hg.diagonal_diag.symm ▸ g.2)
  refine ⟨fun i => ⟨(g : Matrix n n ℂ) i i,
    mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary (hunit i))⟩, Subtype.ext ?_⟩
  exact hg.diagonal_diag

/-- The diagonal torus of `U(n)` is commutative: diagonal matrices commute. -/
instance : IsMulCommutative (unitaryTorus n) :=
  Subgroup.range_isMulCommutative _

/-- **The diagonal torus of `U(n)` is its own centralizer**: a unitary matrix commuting with every
diagonal unitary matrix is diagonal. -/
theorem centralizer_unitaryTorus :
    Subgroup.centralizer (unitaryTorus n : Set (unitaryGroup n ℂ)) = unitaryTorus n := by
  refine le_antisymm (fun g hg => mem_unitaryTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  let z : n → Circle := Pi.mulSingle i (Circle.exp Real.pi)
  have hcomm : Commute (diagonal fun k => (z k : ℂ)) (g : Matrix n n ℂ) := by
    have h := congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hg _ (unitaryTorusHom_mem_unitaryTorus z))
    rwa [Submonoid.coe_mul, Submonoid.coe_mul, coe_unitaryTorusHom] at h
  exact apply_eq_zero_of_commute_diagonal hcomm fun h => Circle.exp_pi_ne_one <| by
    simpa [z, Pi.mulSingle_eq_of_ne hij.symm] using Circle.coe_inj.mp h

/-- **The diagonal torus is a maximal commutative subgroup of `U(n)`**: a commutative subgroup
containing it is equal to it. In particular the diagonal torus is a maximal torus of `U(n)`. -/
theorem eq_unitaryTorus_of_isMulCommutative {H : Subgroup (unitaryGroup n ℂ)} [IsMulCommutative H]
    (hH : unitaryTorus n ≤ H) : H = unitaryTorus n :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative centralizer_unitaryTorus hH

/-- **Every element of `U(n)` is conjugate into the diagonal torus.** A unitary matrix is normal,
so a unitary change of basis diagonalizes it. -/
theorem exists_conj_mem_unitaryTorus (g : unitaryGroup n ℂ) :
    ∃ u : unitaryGroup n ℂ, u * g * u⁻¹ ∈ unitaryTorus n := by
  obtain ⟨U, hU, d, hd⟩ := exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (g : Matrix n n ℂ)
  refine ⟨(⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹, mem_unitaryTorus_iff.mpr ?_⟩
  -- Inversion in `U(n)` is `star`, which commutes with the coercion to matrices.
  have hcoe : (((⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹ * g * ((⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹)⁻¹ :
      unitaryGroup n ℂ) : Matrix n n ℂ) = star U * g * U := by
    rw [inv_inv, Submonoid.coe_mul, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
  rw [hcoe, hd]
  exact isDiag_diagonal d

/-- Every element of `U(n)` is conjugate to `diag (z₁, …, zₙ)` for some points `zᵢ` of the circle:
`TauCeti.exists_conj_mem_unitaryTorus` read through the parametrization
`TauCeti.unitaryTorusHom` of the diagonal torus. -/
theorem exists_isConj_unitaryTorusHom (g : unitaryGroup n ℂ) :
    ∃ z : n → Circle, IsConj g (unitaryTorusHom n z) := by
  obtain ⟨u, hu⟩ := exists_conj_mem_unitaryTorus g
  obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hu
  exact ⟨z, isConj_iff.mpr ⟨u, hz.symm⟩⟩

end TauCeti
end
end TAF_LiteralSource_0365

section TAF_LiteralSource_0366
/- Original module: TauCeti.Analysis.InnerProductSpace.BasisSpan -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/


/-!
# Spans of orthonormal subfamilies

For a finite-index orthonormal basis and a set of indices, `spanIndices` is the
subspace spanned by the corresponding basis vectors.

## Main results

* `OrthonormalBasis.spanIndices_eq_span`: the explicit span characterization.
* `OrthonormalBasis.span_range_comp_subtypeVal_eq_spanIndices`: the restriction
  `b ∘ (↑) : s → E` of the basis to the coordinate block `s`, an orthonormal family by
  `Orthonormal.comp`, spans the selected subspace.
* `OrthonormalBasis.spanIndices_mono`: monotonicity under index-set inclusion.
* `OrthonormalBasis.mem_spanIndices_of_mem`: selected basis vectors belong to the span.
* `OrthonormalBasis.mem_spanIndices_iff`: membership means coordinates vanish
  outside the selected indices.
* `OrthonormalBasis.finrank_spanIndices`: the dimension of a selected finite span.
* `OrthonormalBasis.finrank_spanIndices_set`: dimension as set cardinality.
* `OrthonormalBasis.orthogonal_spanIndices`: orthogonal complement by index complement.

## Source

Adapted from `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). The selected-span construction originates in the
Courant--Fischer development.
-/

public section

namespace OrthonormalBasis

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices
`i ∈ s`. -/
noncomputable def spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (b '' s)

/-- The selected subspace is the span of its basis vectors.
Use this identity to apply `Submodule.span`'s induction or universal property. -/
theorem spanIndices_eq_span (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    b.spanIndices s = Submodule.span 𝕜 (b '' s) := (rfl)

/-- The basis vectors indexed by the coordinate block `s`, as a family indexed by `s`, span the
selected subspace. -/
theorem span_range_comp_subtypeVal_eq_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    Submodule.span 𝕜 (Set.range (b ∘ ((↑) : s → ι))) = b.spanIndices s := by
  rw [spanIndices_eq_span, Set.range_comp, Subtype.range_coe]

/-- Selecting more indices spans more. -/
theorem spanIndices_mono (b : OrthonormalBasis ι 𝕜 E) {s t : Set ι} (h : s ⊆ t) :
    b.spanIndices s ≤ b.spanIndices t := by
  rw [b.spanIndices_eq_span s, b.spanIndices_eq_span t]
  exact Submodule.span_mono (Set.image_mono h)

/-- A selected basis vector lies in the span of its index set. -/
theorem mem_spanIndices_of_mem (b : OrthonormalBasis ι 𝕜 E) {s : Set ι} {i : ι}
    (hi : i ∈ s) : b i ∈ b.spanIndices s := by
  rw [b.spanIndices_eq_span]
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- A vector in the span of a selected subfamily has zero coordinate at any
index outside the selection. -/
theorem repr_eq_zero_of_mem_spanIndices (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} (hx : x ∈ b.spanIndices s) {i : ι} (hi : i ∉ s) :
    b.repr x i = 0 := by
  rw [b.spanIndices_eq_span] at hx
  rw [b.repr_apply_apply]
  -- `⟪b i, ·⟫` vanishes on the spanning set, hence on the whole span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, hj, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi hj
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Membership in the span of a selected subfamily is exactly the vanishing of
the coordinates outside the selection. -/
@[simp]
theorem mem_spanIndices_iff (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} :
    x ∈ b.spanIndices s ↔ ∀ i ∉ s, b.repr x i = 0 := by
  classical
  refine ⟨fun hx i hi => b.repr_eq_zero_of_mem_spanIndices hx hi, fun h => ?_⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i ∈ s
  · exact Submodule.smul_mem _ _ (b.mem_spanIndices_of_mem hi)
  · rw [h i hi, zero_smul]
    exact Submodule.zero_mem _

/-- The span of a selected subfamily has dimension the number of selected
indices. -/
theorem finrank_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) :
    finrank 𝕜 (b.spanIndices ↑s) = s.card := by
  have h : finrank 𝕜 (Submodule.span 𝕜
      (Set.range fun i : ↥(↑s : Set ι) => b ↑i)) = Fintype.card ↥(↑s : Set ι) :=
    finrank_span_eq_card
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)
  rw [b.spanIndices_eq_span, Set.image_eq_range, h]
  simp

/-- The span of the basis vectors with index below `n` has rank at most `n`. -/
theorem rank_spanIndices_val_lt_le {m : ℕ} (b : OrthonormalBasis (Fin m) 𝕜 E) (n : ℕ) :
    Module.rank 𝕜 (b.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m))) ≤ n := by
  let := Module.Finite.of_basis b.toBasis
  rw [← Module.finrank_eq_rank, b.finrank_spanIndices, Fin.card_filter_val_lt]
  exact_mod_cast min_le_right m n

/-- The span of a selected set of basis vectors has dimension equal to the
number of selected indices. -/
theorem finrank_spanIndices_set (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    finrank 𝕜 (b.spanIndices s) = s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  rw [← b.finrank_spanIndices s.toFinset, Set.coe_toFinset]

/-- The orthogonal complement of the span of a selected subfamily is the span
of the complementary subfamily. -/
theorem orthogonal_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    (b.spanIndices s)ᗮ = b.spanIndices sᶜ := by
  classical
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have hEcard : finrank 𝕜 E = Fintype.card ι := by
    rw [Module.finrank_eq_card_basis b.toBasis]
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · -- the complementary span is orthogonal to the selected span.
    rw [b.spanIndices_eq_span (sᶜ)]
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    rw [← inner_conj_symm, ← b.repr_apply_apply,
      b.repr_eq_zero_of_mem_spanIndices hu hj, map_zero]
  · -- dimensions match: `card ι − #s` on both sides.
    have h1 : finrank 𝕜 (b.spanIndices s)
        + finrank 𝕜 ((b.spanIndices s)ᗮ : Submodule 𝕜 E) = Fintype.card ι := by
      rw [Submodule.finrank_add_finrank_orthogonal, hEcard]
    have h2 := b.finrank_spanIndices_set s
    have h3 := b.finrank_spanIndices_set sᶜ
    have h4 : s.toFinset.card + (sᶜ).toFinset.card = Fintype.card ι := by
      rw [Set.toFinset_compl, Finset.card_compl]
      have := Finset.card_le_univ s.toFinset
      omega
    simp only [Set.ncard_eq_toFinset_card'] at h2 h3
    omega

/-- A vector orthogonal to the first `n` basis vectors lies in the remaining span. -/
theorem mem_spanIndices_le_of_mem_orthogonal {m : ℕ} (b : OrthonormalBasis (Fin m) 𝕜 E)
    {n : ℕ} {x : E}
    (hx : x ∈ (b.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m)))ᗮ) :
    x ∈ b.spanIndices {i | n ≤ (i : ℕ)} := by
  refine b.spanIndices_mono (fun i hi ↦ ?_) ((b.orthogonal_spanIndices _).le hx)
  simpa using hi

end OrthonormalBasis

end
end TAF_LiteralSource_0366

section TAF_LiteralSource_0367
/- Original module: TauCeti.Algebra.Module.Equiv.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Linear equivalences and their underlying maps

Mathlib's `LinearEquiv.smulOfUnit` packages multiplication by a unit `u` of the base ring as a
linear equivalence, but records no lemma evaluating it at a vector. This file supplies that
evaluation lemma, in the `simp`-normal form that rewrites an application of
`LinearEquiv.smulOfUnit` to a scalar multiplication. It also records how a linear automorphism,
viewed as a permutation of the module through `MulAction.toPermHom`, moves the set underlying a
submodule.
Postcomposition with an isomorphism of targets also transports hom spaces over auxiliary
scalars, even when the ring defining the linear maps is noncommutative.
For coordinate transport, forgetting linearity gives the corresponding additive word
equivalence, with the same direction on coordinates. A commutative square of linear maps with
isomorphisms on its vertical sides transports the ranges of precomposition on hom spaces.
Conjugating an endomorphism by a semilinear equivalence commutes with powers and moves its kernel
by the equivalence.

## Main results

* `LinearEquiv.map_range_lcomp`: transport of precomposition ranges along an isomorphism
  of arrows, over a semiring and with any compatible hom-space scalars and target.
* `LinearEquiv.homCongrRight`: an isomorphism of targets induces an equivalence of hom spaces
  over the auxiliary scalar semiring.

* `LinearEquiv.map_ker_of_intertwine` and `LinearEquiv.map_range_of_intertwine`: transport of
  kernels and ranges across an intertwining semilinear equivalence.
* `LinearEquiv.conj_pow` and `LinearEquiv.ker_conj`: conjugation by a semilinear equivalence
  commutes with powers and transports kernels.
* `LinearEquiv.toPermHom_smul_coe`: the permutation of the module underlying a linear
  automorphism moves the set underlying a submodule to the set underlying its image.
* `LinearEquiv.smulOfUnit_apply`: `LinearEquiv.smulOfUnit u` acts as multiplication by `u`.
* `LinearEquiv.funCongrLeft_toAddMonoidHom`: forgetting linearity in coordinate transport
  gives additive coordinate transport.
-/

public section

namespace LinearEquiv

section Coordinates

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {ι κ : Type*}

/-- The additive homomorphism underlying linear coordinate transport is the one underlying
`AddEquiv.arrowCongr`, with the coordinate equivalence reversed. -/
@[simp]
theorem funCongrLeft_toAddMonoidHom (e : κ ≃ ι) :
    ((funCongrLeft R M e : (ι → M) →ₗ[R] κ → M) : (ι → M) →+ κ → M) =
      (AddEquiv.arrowCongr e.symm (AddEquiv.refl M)) := by
  ext x i
  simp

end Coordinates

section HomCongrRight

variable (k : Type*) {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
variable {S : Type*} [AddCommMonoid S] [Module A S]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
variable {P : Type*} [AddCommMonoid P] [Module A P] [Module k P] [IsScalarTower k A P]

/-- **Isomorphic targets give isomorphic hom spaces.**  An `A`-linear isomorphism `e : N ≃ₗ[A] P`
carries `S →ₗ[A] N` to `S →ₗ[A] P` by postcomposition, `k`-linearly.

This is `LinearEquiv.congrRight` with the auxiliary scalars `k` in place of a commutativity
assumption on `A`: since `A` is not assumed commutative the hom spaces are not `A`-modules, and
`k`, acting on the targets compatibly with `A`, supplies the linear structure instead.  The two
directions are `LinearMap.compRight`. -/
def homCongrRight (e : N ≃ₗ[A] P) : (S →ₗ[A] N) ≃ₗ[k] (S →ₗ[A] P) :=
  LinearEquiv.ofLinearMap (LinearMap.compRight (M := S) k (e : N →ₗ[A] P))
    (LinearMap.compRight (M := S) k (e.symm : P →ₗ[A] N))
    (by ext f s; simp) (by ext f s; simp)

@[simp]
theorem homCongrRight_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] N) (s : S) :
    homCongrRight k (S := S) e f s = e (f s) :=
  (rfl)

@[simp]
theorem homCongrRight_symm_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] P) (s : S) :
    (homCongrRight k (S := S) e).symm f s = e.symm (f s) :=
  (rfl)

end HomCongrRight

section Precomposition

variable {R P₀ P₁ Q₀ Q₁ : Type*} [Semiring R]
  [AddCommMonoid P₀] [Module R P₀] [AddCommMonoid P₁] [Module R P₁]
  [AddCommMonoid Q₀] [Module R Q₀] [AddCommMonoid Q₁] [Module R Q₁]

/-- An isomorphism of arrows transports the range of precomposition on hom spaces.
The common target and its commuting scalar action are arbitrary; in particular, the target
may be `R` with scalars `Rᵐᵒᵖ`, as for opposite module duals. -/
theorem map_range_lcomp (e₀ : P₀ ≃ₗ[R] Q₀) (e₁ : P₁ ≃ₗ[R] Q₁)
    (S N : Type*) [Semiring S] [AddCommMonoid N] [Module R N] [Module S N]
    [SMulCommClass R S N] {p : P₁ →ₗ[R] P₀} {q : Q₁ →ₗ[R] Q₀}
    (hsquare : e₀.toLinearMap ∘ₗ p = q ∘ₗ e₁.toLinearMap) :
    (LinearMap.range (p.lcomp S N)).map (e₁.congrLeft N S).toLinearMap =
      LinearMap.range (q.lcomp S N) := by
  rw [← LinearMap.range_comp]
  have hcomp :
      (e₁.congrLeft N S).toLinearMap.comp (p.lcomp S N) =
        (q.lcomp S N).comp (e₀.congrLeft N S).toLinearMap := by
    ext φ x
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply]
    apply congrArg φ
    simpa using congrArg e₀.symm (LinearMap.congr_fun hsquare (e₁.symm x))
  rw [hcomp, LinearEquiv.range_comp]

end Precomposition

section Intertwining

variable {R S M N : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module S N] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/-- If a semilinear equivalence `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the kernel of `f` onto the kernel of `g`. -/
theorem map_ker_of_intertwine
    (e : M ≃ₛₗ[σ] N) (f : M →ₗ[R] M) (g : N →ₗ[S] N)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₛₗ[σ] N) (LinearMap.ker f) = LinearMap.ker g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [h d, hd, map_zero]
  · intro hc
    refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
    have : e (f (e.symm c)) = 0 := by rw [← h, e.apply_symm_apply, hc]
    exact e.map_eq_zero_iff.mp this

/-- If a semilinear equivalence `e` intertwines two endomorphisms `f` and `g` pointwise
(`g (e d) = e (f d)`), it carries the range of `f` onto the range of `g`. -/
theorem map_range_of_intertwine
    (e : M ≃ₛₗ[σ] N) (f : M →ₗ[R] M) (g : N →ₗ[S] N)
    (h : ∀ d, g (e d) = e (f d)) :
    Submodule.map (e : M →ₛₗ[σ] N) (LinearMap.range f) = LinearMap.range g := by
  ext c
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨d, ⟨b, rfl⟩, rfl⟩
    exact ⟨e b, h b⟩
  · rintro ⟨b, rfl⟩
    exact ⟨f (e.symm b), ⟨e.symm b, rfl⟩, by rw [← h, e.apply_symm_apply]⟩

end Intertwining

section Conj

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module S N] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/-- Conjugation by a semilinear equivalence commutes with powers. -/
@[simp]
theorem conj_pow (e : M ≃ₛₗ[σ] N) (f : Module.End R M) (k : ℕ) :
    e.conj (f ^ k) = e.conj f ^ k :=
  map_pow e.conjRingEquiv f k

/-- Conjugation by a semilinear equivalence `e` carries the kernel of `f` to its image under `e`. -/
@[simp]
theorem ker_conj (e : M ≃ₛₗ[σ] N) (f : Module.End R M) :
    LinearMap.ker (e.conj f) = (LinearMap.ker f).map (e : M →ₛₗ[σ] N) :=
  (map_ker_of_intertwine e f (e.conj f) fun d => by simp).symm

end Conj

section PermHom

open Pointwise

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The permutation of the module underlying a linear automorphism moves the set underlying a
submodule to the set underlying its image. -/
theorem toPermHom_smul_coe (g : M ≃ₗ[R] M) (p : Submodule R M) :
    MulAction.toPermHom (M ≃ₗ[R] M) M g • (p : Set M) = (p.map (g : M →ₗ[R] M) : Set M) := by
  ext x
  simp only [Set.mem_smul_set, SetLike.mem_coe, Submodule.mem_map, MulAction.toPermHom_apply,
    Equiv.Perm.smul_def, MulAction.toPerm_apply, LinearEquiv.smul_def, LinearEquiv.coe_coe]

end PermHom

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit of the base ring, evaluated: `LinearEquiv.smulOfUnit u` sends `x` to
`u • x`. -/
@[simp]
theorem smulOfUnit_apply (u : Rˣ) (x : M) : (smulOfUnit u : M ≃ₗ[R] M) x = (u : R) • x :=
  (rfl)

end LinearEquiv
end
end TAF_LiteralSource_0367

section TAF_LiteralSource_0368
/- Original module: TauCeti.LinearAlgebra.Dimension.Submodule -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/


/-!
# Dimensions of submodules

Dimension-counting criteria for nontrivial submodule intersection: two subspaces of a
finite-dimensional space whose dimensions sum to more than the ambient dimension meet
nontrivially, as do three subspaces whose dimensions sum to more than twice the ambient dimension,
and a subspace of rank greater than the rank of a linear map `f` meets `ker f`
nontrivially. Dually, the preimage of a subspace `W` under a linear map out of an
`m`-dimensional space has codimension at most the codimension of `W`. A set spans a subspace of
dimension at least `n` exactly when it contains `n` linearly independent vectors. Two disjoint
subspaces of a finite-dimensional subspace `U` have dimensions adding to at most that of `U`.

The rank of a product `V.prod W` of free submodules is the sum of their ranks over any
semiring satisfying the strong rank condition. Consequently, the rank of a product map
`f.prodMap g` with free ranges is the sum of the ranks of `f` and `g`. Conjugating an
endomorphism by a linear equivalence preserves the dimension of its kernel.
-/

public section

open Module (finrank)

universe u v

namespace Submodule

variable {𝕜 : Type*}

section DivisionRing

variable [DivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- Two subspaces whose dimensions sum to more than the dimension of the ambient
space have nontrivial intersection. -/
theorem inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {V W : Submodule 𝕜 E}
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : V ⊓ W ≠ ⊥ := fun hbot =>
  absurd (Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot))
    (by omega)

/-
Call sites supply `E` explicitly. Leaving it to unification makes the elaborator look for an
`AddCommGroup` structure on a space -- of linear maps, of tensors -- whose `AddCommMonoid`
structure is already fixed, which it does not find quickly.
-/

/-- Two disjoint subspaces of a finite-dimensional subspace `U` have dimensions adding to at most
that of `U`. This is the relative form of `Submodule.finrank_add_finrank_le_of_disjoint`, which
bounds them by the dimension of the ambient space. -/
theorem finrank_add_finrank_le_of_disjoint_of_le {S T U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
    (h : Disjoint S T) (hS : S ≤ U) (hT : T ≤ U) :
    finrank 𝕜 S + finrank 𝕜 T ≤ finrank 𝕜 U := by
  have := finiteDimensional_of_le hS
  have := finiteDimensional_of_le hT
  rw [← finrank_sup_add_finrank_inf_eq, h.eq_bot, finrank_bot, add_zero]
  exact finrank_mono (sup_le hS hT)

/-- Three subspaces whose dimensions sum to more than twice the dimension of the ambient
space have nontrivial common intersection. -/
theorem inf_inf_ne_bot_of_finrank_lt [FiniteDimensional 𝕜 E] {U V W : Submodule 𝕜 E}
    (h : 2 * finrank 𝕜 E < finrank 𝕜 U + finrank 𝕜 V + finrank 𝕜 W) : U ⊓ V ⊓ W ≠ ⊥ := by
  have hUV := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hle := (U ⊔ V).finrank_le
  exact inf_ne_bot_of_finrank_lt (by omega)

/-- The preimage of a subspace `W` under a linear map `f : M → N` of finite-dimensional spaces
has codimension at most the codimension of `W`: `dim M + dim W ≤ dim (f⁻¹ W) + dim N`. -/
theorem finrank_add_finrank_le_finrank_comap_add_finrank {M N : Type*} [AddCommGroup M]
    [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N] [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
    (f : M →ₗ[𝕜] N) (W : Submodule 𝕜 N) :
    finrank 𝕜 M + finrank 𝕜 W ≤ finrank 𝕜 (W.comap f) + finrank 𝕜 N := by
  -- The preimage is the kernel of `M → N ⧸ W`; apply rank–nullity to that map.
  have hker : LinearMap.ker (W.mkQ ∘ₗ f) = W.comap f := by
    rw [LinearMap.ker_comp, ker_mkQ]
  have h₁ := LinearMap.finrank_range_add_finrank_ker (W.mkQ ∘ₗ f)
  have h₂ := (W.mkQ ∘ₗ f).range.finrank_le
  have h₃ := W.finrank_quotient_add_finrank
  rw [hker] at h₁
  omega

/-- A set spans a subspace of dimension at least `n` exactly when it contains `n` linearly
independent vectors. -/
theorem le_finrank_span_iff_exists_linearIndependent {s : Set E} [Module.Finite 𝕜 (span 𝕜 s)]
    {n : ℕ} :
    n ≤ finrank 𝕜 (span 𝕜 s) ↔ ∃ v : Fin n → E, LinearIndependent 𝕜 v ∧ ∀ i, v i ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv, hvs⟩ ↦ ?_⟩
  · obtain ⟨f, hfs, -, hf⟩ := exists_fun_fin_finrank_span_eq 𝕜 s
    exact ⟨f ∘ Fin.castLE h, hf.comp _ (Fin.castLE_injective h), fun i ↦ hfs _⟩
  · have := finrank_mono (span_mono (R := 𝕜) (Set.range_subset_iff.2 hvs))
    rwa [finrank_span_eq_card hv, Fintype.card_fin] at this

end DivisionRing

/-- A submodule meeting the kernel of `f` trivially has rank at most the rank of `f`, since `f`
maps it injectively into its range. -/
theorem lift_rank_le_of_disjoint_ker [Ring 𝕜] {M : Type u} {N : Type v}
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
    {V : Submodule 𝕜 M} {f : M →ₗ[𝕜] N} (h : Disjoint V (LinearMap.ker f)) :
    Cardinal.lift.{v} (Module.rank 𝕜 V) ≤ Cardinal.lift.{u} f.rank := by
  apply (f.rangeRestrict.domRestrict V).lift_rank_le_of_injective
  simpa only [LinearMap.injective_domRestrict_iff, LinearMap.ker_rangeRestrict] using h

/-- The rank of a product of free submodules is the sum of their ranks. -/
theorem rank_prod [Semiring 𝕜] [StrongRankCondition 𝕜] {M : Type u} {N : Type v}
    [AddCommMonoid M] [Module 𝕜 M] [AddCommMonoid N] [Module 𝕜 N]
    (V : Submodule 𝕜 M) (W : Submodule 𝕜 N) [Module.Free 𝕜 V] [Module.Free 𝕜 W] :
    Module.rank 𝕜 (V.prod W) =
      Cardinal.lift.{v} (Module.rank 𝕜 V) + Cardinal.lift.{u} (Module.rank 𝕜 W) := by
  rw [(V.prodEquiv W).rank_eq, _root_.rank_prod]

end Submodule

namespace LinearMap

variable {𝕜 M N : Type*} {M' : Type u} {N' : Type v} [Semiring 𝕜] [StrongRankCondition 𝕜]
  [AddCommMonoid M] [Module 𝕜 M] [AddCommMonoid N] [Module 𝕜 N]
  [AddCommMonoid M'] [Module 𝕜 M'] [AddCommMonoid N'] [Module 𝕜 N']

/-- The rank of a product map with free ranges is the sum of the ranks of its components. -/
theorem rank_prodMap (f : M →ₗ[𝕜] M') (g : N →ₗ[𝕜] N')
    [Module.Free 𝕜 f.range] [Module.Free 𝕜 g.range] :
    (f.prodMap g).rank = Cardinal.lift.{v} f.rank + Cardinal.lift.{u} g.rank := by
  rw [LinearMap.rank, range_prodMap, Submodule.rank_prod]

end LinearMap

namespace LinearEquiv

/-- Conjugate endomorphisms have kernels of the same dimension. -/
@[simp]
theorem finrank_ker_conj {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) (f : Module.End R M) :
    finrank R (LinearMap.ker (e.conj f)) = finrank R (LinearMap.ker f) := by
  rw [ker_conj, finrank_map_eq]

end LinearEquiv

end
end TAF_LiteralSource_0368

section TAF_LiteralSource_0369
/- Original module: TauCeti.Analysis.InnerProductSpace.CourantFischer -/
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/


/-!
# Courant–Fischer min–max theorem and Weyl's inequality

For a finite-dimensional inner-product space over `ℝ` or `ℂ`, the min–max theorem
characterizes the decreasingly sorted eigenvalues of a symmetric endomorphism
through its Rayleigh form.  The same argument gives monotonicity under quadratic-
form domination and Weyl's perturbation bound.

## Main results

* `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq`:
  diagonal expansion of the Rayleigh form in an eigenbasis.
* `LinearMap.sq_norm_apply_eq_sum_of_eigenbasis`:
  diagonal expansion of `‖T x‖²` in an eigenbasis.
* `LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue` and
  `LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner`:
  the two min–max directions.
* `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner`:
  the Courant–Fischer equality.
* `LinearMap.IsSymmetric.eigenvalue_mono`:
  monotonicity of sorted eigenvalues under quadratic-form order.
* `LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le` and
  `LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm`:
  Weyl's perturbation inequality.
* `LinearMap.IsSymmetric.eigenvalues_add_le` and `LinearMap.IsSymmetric.le_eigenvalues_add`:
  Weyl's additive inequalities comparing the sorted eigenvalues of `T + S` with those of `T`
  and `S`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed.,
  Theorems 4.2.6 and 4.3.1.
* R. Bhatia, *Matrix Analysis*, Corollary III.2.6.

## Provenance

Ported and adapted from
[`ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/main/ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean)
in Kitware's DKPS formalization (Apache-2.0).  The original proof development
was by Claude Fable 5, with polishing by Claude Opus 4.8 and oversight by
Jon Crall.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- Parseval: in an orthonormal basis the squared norms of the coordinates sum
to the squared norm.  Thin wrapper around
`OrthonormalBasis.sum_sq_norm_inner_right`. -/
private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x


/-- The squared norm in any orthonormal eigenbasis: if `S (w i) = μ i • w i` for all `i`, then
`‖S x‖ ^ 2 = ∑ i, ‖μ i‖ ^ 2 * ‖w.repr x i‖ ^ 2`. -/
theorem LinearMap.sq_norm_apply_eq_sum_of_eigenbasis
    (S : E →ₗ[𝕜] E) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → 𝕜}
    (hw : ∀ i, S (w i) = μ i • w i) (x : E) :
    ‖S x‖ ^ 2 = ∑ i : Fin n, ‖μ i‖ ^ 2 * ‖w.repr x i‖ ^ 2 := by
  have hrepr : ∀ i, w.repr (S x) i = μ i * w.repr x i := by
    intro i
    conv_lhs => rw [← w.sum_repr x]
    simp [map_sum, hw, smul_smul, mul_comm, Pi.single_apply]
  rw [← sum_sq_norm_repr_eq_sq_norm w (S x)]
  simp_rw [hrepr, norm_mul, mul_pow]

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

omit [FiniteDimensional 𝕜 E] in
/-- Diagonalization of the quadratic form in any orthonormal eigenbasis: if
`S (w i) = μ i • w i` for all `i`, then
`re ⟪S x, x⟫ = ∑ i, μ i * ‖w.repr x i‖ ^ 2`. -/
theorem re_inner_apply_self_eq_sum_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) (x : E) :
    RCLike.re ⟪S x, x⟫_𝕜 = ∑ i : Fin n, μ i * ‖w.repr x i‖ ^ 2 := by
  have hrepr : ∀ i, w.repr (S x) i = (μ i : 𝕜) * w.repr x i := by
    intro i
    rw [w.repr_apply_apply, w.repr_apply_apply, ← hS (w i) x, hw i, inner_smul_left,
      RCLike.conj_ofReal]
  have key : ⟪S x, x⟫_𝕜 = ((∑ i : Fin n, μ i * ‖w.repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← w.repr.inner_map_map (S x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hrepr i, map_mul, RCLike.conj_ofReal, mul_left_comm,
      RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

omit [FiniteDimensional 𝕜 E] in
/-- On the span of the eigenvectors selected by `s`, the quadratic form is
bounded below by any lower bound on the selected values (general-eigenbasis
version of `le_re_inner_apply_self_of_mem_spanIndices`). -/
theorem le_re_inner_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ μ i) {x : E} (hx : x ∈ w.spanIndices s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜 := by
  rw [hS.re_inner_apply_self_eq_sum_of_eigenbasis w hw x,
    -- names the application so the norm bound applies to it directly.
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖w.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [w.repr_eq_zero_of_mem_spanIndices hx hp]; simp

omit [FiniteDimensional 𝕜 E] in
/-- Dual of `le_re_inner_of_eigenbasis`. -/
theorem re_inner_le_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, μ i ≤ c) {x : E} (hx : x ∈ w.spanIndices s) :
    RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  rw [hS.re_inner_apply_self_eq_sum_of_eigenbasis w hw x,
    -- names the application so the norm bound applies to it directly.
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖w.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [w.repr_eq_zero_of_mem_spanIndices hx hp]; simp


/-! ### The quadratic form in the eigenbasis -/

/-- The quadratic form `re ⟪T x, x⟫` of a symmetric operator `T` expressed in
its eigenbasis: it is the eigenvalue-weighted sum of the squared norms of the
coordinates of `x`.  This is the diagonalization of the quadratic form.  (For
symmetric `T` the inner product `⟪T x, x⟫` is real, so no information is lost
by taking the real part.) -/
theorem re_inner_apply_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  exact hT.re_inner_apply_self_eq_sum_of_eigenbasis
    (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) x

/-- On the span of a selected subfamily of the eigenbasis, the quadratic form
is bounded by any bound on the selected eigenvalues: if
`x ∈ b.spanIndices s` (so its coordinates vanish off `s`) and every selected
eigenvalue satisfies `λᵢ ≤ c`, then `re ⟪T x, x⟫ ≤ c ‖x‖²`. -/
theorem re_inner_apply_self_le_of_mem_spanIndices
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ (hT.eigenvectorBasis hn).spanIndices s) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  exact hT.re_inner_le_of_eigenbasis
    (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) hc hx

/-- Dual of `re_inner_apply_self_le_of_mem_spanIndices`: if
`x ∈ b.spanIndices s` and every selected eigenvalue satisfies `c ≤ λᵢ`, then
`c ‖x‖² ≤ re ⟪T x, x⟫`. -/
theorem le_re_inner_apply_self_of_mem_spanIndices
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ (hT.eigenvectorBasis hn).spanIndices s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  exact hT.le_re_inner_of_eigenbasis
    (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) hc hx

/-! ### Discrete Courant–Fischer directional bounds -/

/-- **Courant–Fischer, upper direction.** On any subspace `V` of dimension
`k + 1` there is a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`, where `λ` is the
decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the eigenvalues
of the symmetric operator `T`. -/
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := b.spanIndices ↑(Finset.Ici k) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, b.finrank_spanIndices, Fin.card_Ici]
  -- Dimension counting: `finrank V + finrank W > finrank E`, so `V ⊓ W ≠ ⊥`.
  have hsum : finrank 𝕜 V + finrank 𝕜 W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ :=
    Submodule.inf_ne_bot_of_finrank_lt (by omega)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  -- The unit vector still lies in `W`; on `W` the selected eigenvalues are all `≤ λₖ`
  -- (antitone), so the spectral-subspace bound gives `re ⟪T x, x⟫ ≤ λₖ · ‖x‖² = λₖ`.
  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        hT.re_inner_apply_self_le_of_mem_spanIndices hn
          (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-- **Courant–Fischer, lower direction.** There is a subspace `V` of dimension
`k + 1` on which every unit vector `x` satisfies `λₖ(T) ≤ re ⟪T x, x⟫`, where
`λ` is the decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the
eigenvalues of the symmetric operator `T`.

Witness: `V = span {bᵢ : i ≤ k}`; on it the quadratic form is bounded below by
`λₖ` since all involved eigenvalues are `≥ λₖ`. -/
theorem exists_submodule_forall_unit_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨b.spanIndices ↑(Finset.Iic k), ?_, ?_⟩
  · rw [b.finrank_spanIndices, Fin.card_Iic]
  · intro x hxV hnx
    -- On this subspace the selected eigenvalues are all `≥ λₖ` (antitone), so the dual
    -- spectral-subspace bound gives `λₖ = λₖ · ‖x‖² ≤ re ⟪T x, x⟫`.
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
          hT.le_re_inner_apply_self_of_mem_spanIndices hn
            (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxV

/-! ### The Courant–Fischer min-max equality -/

/-- **Courant–Fischer min-max equality.** The `k`-th (decreasingly sorted)
eigenvalue of a symmetric operator on a finite-dimensional inner product space
over `𝕜 = ℝ, ℂ` is the supremum, over the subspaces `V` of dimension `k + 1`,
of the infimum of the Rayleigh quotient `re ⟪T x, x⟫` over the unit vectors of
`V`.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.2.6. -/
theorem eigenvalues_eq_iSup_iInf_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    hT.eigenvalues hn k =
      ⨆ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
        ⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
          RCLike.re ⟪T (x : E), (x : E)⟫_𝕜 := by
  have hn0 : 0 < n := k.pos
  -- Uniform Rayleigh lower bound: every unit vector has quadratic form at least
  -- the smallest eigenvalue; this bounds every inner infimum below.
  set m : Fin n := ⟨n - 1, by omega⟩ with hm
  have hray : ∀ x : E, ‖x‖ = 1 →
      hT.eigenvalues hn m ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
    intro x hx
    rw [hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hn x,
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      show hT.eigenvalues hn m = ∑ i : Fin n,
          hT.eigenvalues hn m * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 by
        rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm, hx]; ring]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hn ?_) (sq_nonneg _)
    rw [Fin.le_def]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change (i : ℕ) ≤ n - 1
    have := i.2
    omega
  have hbddB : ∀ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
      BddBelow (Set.range fun x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1} =>
        RCLike.re ⟪T (x : E), (x : E)⟫_𝕜) := by
    intro V
    exact ⟨hT.eigenvalues hn m, by rintro _ ⟨x, rfl⟩; exact hray _ x.2.2⟩
  -- Every inner infimum is at most `λₖ` (upper direction).
  have hupper : ∀ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
      (⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_𝕜) ≤ hT.eigenvalues hn k := by
    intro V
    obtain ⟨x, hxV, hx1, hxle⟩ :=
      hT.exists_unit_vector_re_inner_le_eigenvalue hn k V.1 V.2
    exact (ciInf_le (hbddB V) ⟨x, hxV, hx1⟩).trans hxle
  -- The lower-direction witness subspace attains `λₖ` from below.
  obtain ⟨V₀, hV₀dim, hV₀low⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
  have : Nonempty {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1} :=
    ⟨⟨V₀, hV₀dim⟩⟩
  obtain ⟨x₀, hx₀V, hx₀1, -⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue hn k V₀ hV₀dim
  refine le_antisymm ?_ (ciSup_le hupper)
  have hlow : hT.eigenvalues hn k ≤
      ⨅ x : {x : E // x ∈ ((⟨V₀, hV₀dim⟩ :
          {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1}) :
            Submodule 𝕜 E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_𝕜 := by
    have : Nonempty {x : E // x ∈ V₀ ∧ ‖x‖ = 1} := ⟨⟨x₀, hx₀V, hx₀1⟩⟩
    exact le_ciInf fun x => hV₀low _ x.2.1 x.2.2
  have hbddA : BddAbove (Set.range
      fun V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1} =>
        ⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
          RCLike.re ⟪T (x : E), (x : E)⟫_𝕜) :=
    ⟨hT.eigenvalues hn k, by rintro _ ⟨V, rfl⟩; exact hupper V⟩
  exact hlow.trans (le_ciSup hbddA ⟨V₀, hV₀dim⟩)

/-! ### Sorted-eigenvalue uniqueness and Loewner monotonicity

Courant–Fischer consequences needed by the Ky Fan / unitarily-invariant-norm
development: an antitone list diagonalizing a symmetric operator in *some*
orthonormal basis is *the* sorted eigenvalue list, and the sorted eigenvalues
are monotone in the quadratic form (Loewner order). -/

/-- **Sorted-eigenvalue uniqueness.**  If an orthonormal basis `w`
diagonalizes the symmetric operator `S` with an *antitone* value list `μ`,
then `μ` is the sorted eigenvalue list: `hS.eigenvalues hn = μ`.
(Courant–Fischer: both lists satisfy the same minimax characterization.) -/
theorem eigenvalues_eq_of_eigenbasis
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (w : OrthonormalBasis (Fin n) 𝕜 E)
    {μ : Fin n → ℝ} (hμ : Antitone μ) (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) :
    hS.eigenvalues hn = μ := by
  funext k
  refine le_antisymm ?_ ?_
  · -- `λₖ ≤ μₖ`: intersect the CF-lower witness with the `w`-tail span.
    obtain ⟨V, hVdim, hVlow⟩ :=
      hS.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
    set W := w.spanIndices ↑(Finset.Ici k) with hW
    have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
      rw [hW, w.finrank_spanIndices, Fin.card_Ici]
    have hinf : V ⊓ W ≠ ⊥ :=
      Submodule.inf_ne_bot_of_finrank_lt (by have hk : (k : ℕ) < n := k.2; omega)
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
    obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
    have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
    have hnx : ‖x‖ = 1 := by
      rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
    have hxW : x ∈ W := W.smul_mem _ hzW
    calc hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x (V.smul_mem _ hzV) hnx
      _ ≤ μ k * ‖x‖ ^ 2 :=
          re_inner_le_of_eigenbasis hS w hw (fun _ hik => hμ (by simpa using hik)) hxW
      _ = μ k := by rw [hnx]; ring
  · -- `μₖ ≤ λₖ`: test the CF-upper bound on the `w`-head span.
    set V := w.spanIndices ↑(Finset.Iic k) with hV
    have hVdim : finrank 𝕜 V = (k : ℕ) + 1 := by
      rw [hV, w.finrank_spanIndices, Fin.card_Iic]
    obtain ⟨x, hxV, hnx, hup⟩ :=
      hS.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
    calc μ k = μ k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪S x, x⟫_𝕜 :=
          le_re_inner_of_eigenbasis hS w hw (fun _ hik => hμ (by simpa using hik)) hxV
      _ ≤ hS.eigenvalues hn k := hup

/-- **Loewner monotonicity of the sorted eigenvalues.**  If the quadratic form
of `T` is dominated by that of `S`, then so is every sorted eigenvalue. -/
theorem eigenvalue_mono
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (h : ∀ x, RCLike.re ⟪T x, x⟫_𝕜 ≤ RCLike.re ⟪S x, x⟫_𝕜) (k : Fin n) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
  obtain ⟨x, hxV, hnx, hup⟩ :=
    hS.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
  calc hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := hVlow x hxV hnx
    _ ≤ RCLike.re ⟪S x, x⟫_𝕜 := h x
    _ ≤ hS.eigenvalues hn k := hup

/-- The span of a selected subfamily of the eigenbasis of a symmetric operator
is invariant under the operator. -/
theorem map_mem_spanIndices (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Set (Fin n)) {x : E}
    (hx : x ∈ (hT.eigenvectorBasis hn).spanIndices s) :
    T x ∈ (hT.eigenvectorBasis hn).spanIndices s := by
  rw [OrthonormalBasis.spanIndices_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    rw [hT.apply_eigenvectorBasis hn j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

end LinearMap.IsSymmetric

/-! ### Weyl's inequality -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- One-sided Weyl bound: `λₖ(S) − λₖ(T) ≤ ‖S − T‖op`.  This is the core
estimate; Weyl's inequality follows by symmetry.

We take a witness subspace `V` of dimension `k + 1` on which
`λₖ(S) ≤ re ⟪S x, x⟫` (lower direction for `S`), then a unit vector `x ∈ V`
with `re ⟪T x, x⟫ ≤ λₖ(T)` (upper direction for `T`).  The difference is
controlled by Cauchy–Schwarz. -/
private theorem eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    hS.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
  obtain ⟨x, hxV, hnx, hTup⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
  -- `λₖ(S) − λₖ(T) ≤ re ⟪Sx,x⟫ − re ⟪Tx,x⟫ = re ⟪(S−T)x,x⟫ ≤ ‖(S−T)x‖ ≤ ε`.
  have hdiff : RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜
      = RCLike.re ⟪(S - T) x, x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_𝕜 ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    simpa [hnx] using hε x
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜 := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_𝕜 := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

/-- **Weyl's inequality** for symmetric operators on a finite-dimensional inner
product space over `𝕜 = ℝ, ℂ`: the `k`-th (decreasingly sorted) eigenvalues of
`T` and `S` differ by at most the operator norm of `T − S`.

At `LinearMap` level there is no operator norm, so the bound is supplied as the
pointwise hypothesis `∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`; see
`LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm` for the continuous-linear-map
operator-norm form.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia,
*Matrix Analysis*, Corollary III.2.6. -/
theorem abs_eigenvalue_sub_eigenvalue_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  -- The two directions of `eigenvalues_sub_le`, with the roles of `T` and `S`
  -- swapped, using `‖(T − S) x‖ = ‖(S − T) x‖`.
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

/-- **Weyl's inequality**, operator-norm form, for symmetric (equivalently,
self-adjoint) continuous linear maps on a finite-dimensional inner product
space: the `k`-th sorted eigenvalues of `T` and `S` differ by at most
`‖T − S‖`.  The symmetry hypotheses are stated on the underlying linear maps
so that the signature does not require the adjoint star structure (whose
instance needs `CompleteSpace E`, which `FiniteDimensional` deliberately does
not register as an instance).

The bound is expressed directly in the norm of a continuous linear map. -/
theorem abs_eigenvalue_sub_eigenvalue_le_norm
    {T S : E →L[𝕜] E}
    (hT : LinearMap.IsSymmetric (T : E →ₗ[𝕜] E))
    (hS : LinearMap.IsSymmetric (S : E →ₗ[𝕜] E))
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ‖T - S‖ := by
  refine abs_eigenvalue_sub_eigenvalue_le hT hS hn (fun x => ?_) k
  simpa using (T - S).le_opNorm x

/-- Weyl's inequality for linear maps, using the operator norm of the
corresponding continuous linear map.  Unlike the preceding theorem, the symmetry
hypotheses and eigenvalue enumeration are directly attached to `LinearMap`s. -/
theorem abs_eigenvalues_sub_le_opNorm
    {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  refine abs_eigenvalue_sub_eigenvalue_le hT hS hn (fun x => ?_) k
  have hx := (LinearMap.toContinuousLinearMap (T - S)).le_opNorm x
  rwa [LinearMap.coe_toContinuousLinearMap'] at hx

/-- Sorted eigenvalues are congruent along an operator equality (the eigenvalue
enumeration depends only on the operator, not on the symmetry proof). -/
theorem eigenvalues_congr {S₁ S₂ : E →ₗ[𝕜] E} (h : S₁ = S₂)
    (hS₁ : S₁.IsSymmetric) (hS₂ : S₂.IsSymmetric) (hn : finrank 𝕜 E = n) :
    hS₁.eigenvalues hn = hS₂.eigenvalues hn := by
  subst h; rfl

/-- The eigenvalue enumeration does not depend on which witness of the dimension indexes
it: two witnesses `finrank 𝕜 E = m` and `finrank 𝕜 E = n` enumerate the same eigenvalues,
read across the induced `Fin m ≃ Fin n`.

Both spellings occur in practice.  A matrix over `Fin n` has
`Matrix.IsHermitian.eigenvalues₀` indexed by `Fin (Fintype.card (Fin n))`, while the
operator theory it is transported to indexes by `Fin n`; `Fintype.card (Fin n) = n` is a
theorem and not definitional, so the two index types are genuinely different. -/
theorem eigenvalues_cast {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {m : ℕ}
    (hm : finrank 𝕜 E = m) (hn : finrank 𝕜 E = n) (hmn : m = n) (i : Fin m) :
    hT.eigenvalues hm i = hT.eigenvalues hn (Fin.cast hmn i) := by
  subst hmn; rfl

/-! ### Weyl's additive inequalities -/

/-- **Weyl's additive inequality**, upper form: for symmetric operators `T` and `S` and indices
with `i + j ≤ k`, the decreasingly sorted eigenvalues satisfy `λₖ(T + S) ≤ λᵢ(T) + λⱼ(S)`.
Indices start at `0`, so for `k = i + j` this is the classical
`λ_{i+j-1}(T + S) ≤ λᵢ(T) + λⱼ(S)` in one-based indexing.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia, *Matrix Analysis*,
Theorem III.2.1. -/
theorem eigenvalues_add_le (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {i j k : Fin n} (hk : (i : ℕ) + j ≤ k) :
    (hT.add hS).eigenvalues hn k ≤ hT.eigenvalues hn i + hS.eigenvalues hn j := by
  -- A nonzero vector in the head span of `T + S` up to `k` and the tail spans of `T` from `i`
  -- and of `S` from `j` exists by counting dimensions: `(k + 1) + (n - i) + (n - j) > 2 n`.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.inf_inf_ne_bot_of_finrank_lt
      (U := ((hT.add hS).eigenvectorBasis hn).spanIndices ↑(Finset.Iic k))
      (V := (hT.eigenvectorBasis hn).spanIndices ↑(Finset.Ici i))
      (W := (hS.eigenvectorBasis hn).spanIndices ↑(Finset.Ici j))
      (by simp only [OrthonormalBasis.finrank_spanIndices, Fin.card_Iic, Fin.card_Ici]; omega))
  obtain ⟨⟨hxTS, hxT⟩, hxS⟩ := hx
  have hlow := (hT.add hS).le_re_inner_apply_self_of_mem_spanIndices hn
    (fun _ h ↦ (hT.add hS).eigenvalues_antitone hn (by simpa using h)) hxTS
  have hTup := hT.re_inner_apply_self_le_of_mem_spanIndices hn
    (fun _ h ↦ hT.eigenvalues_antitone hn (by simpa using h)) hxT
  have hSup := hS.re_inner_apply_self_le_of_mem_spanIndices hn
    (fun _ h ↦ hS.eigenvalues_antitone hn (by simpa using h)) hxS
  rw [LinearMap.add_apply, inner_add_left, map_add] at hlow
  exact (mul_le_mul_iff_left₀ (pow_pos (norm_pos_iff.mpr hx0) 2)).mp (by linarith)

/-- **Weyl's additive inequality**, lower form: for symmetric operators `T` and `S` on an
`n`-dimensional space and indices with `k + n ≤ i + j + 1`, the decreasingly sorted eigenvalues
satisfy `λᵢ(T) + λⱼ(S) ≤ λₖ(T + S)`. For `k + n = i + j + 1` this is the classical
`λᵢ(T) + λⱼ(S) ≤ λ_{i+j-n}(T + S)` in one-based indexing.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia, *Matrix Analysis*,
Theorem III.2.1. -/
theorem le_eigenvalues_add (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {i j k : Fin n} (hk : (k : ℕ) + n ≤ i + j + 1) :
    hT.eigenvalues hn i + hS.eigenvalues hn j ≤ (hT.add hS).eigenvalues hn k := by
  -- A nonzero vector in the tail span of `T + S` from `k` and the head spans of `T` up to `i`
  -- and of `S` up to `j` exists by counting dimensions: `(n - k) + (i + 1) + (j + 1) > 2 n`.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.inf_inf_ne_bot_of_finrank_lt
      (U := ((hT.add hS).eigenvectorBasis hn).spanIndices ↑(Finset.Ici k))
      (V := (hT.eigenvectorBasis hn).spanIndices ↑(Finset.Iic i))
      (W := (hS.eigenvectorBasis hn).spanIndices ↑(Finset.Iic j))
      (by simp only [OrthonormalBasis.finrank_spanIndices, Fin.card_Iic, Fin.card_Ici]; omega))
  obtain ⟨⟨hxTS, hxT⟩, hxS⟩ := hx
  have hup := (hT.add hS).re_inner_apply_self_le_of_mem_spanIndices hn
    (fun _ h ↦ (hT.add hS).eigenvalues_antitone hn (by simpa using h)) hxTS
  have hTlow := hT.le_re_inner_apply_self_of_mem_spanIndices hn
    (fun _ h ↦ hT.eigenvalues_antitone hn (by simpa using h)) hxT
  have hSlow := hS.le_re_inner_apply_self_of_mem_spanIndices hn
    (fun _ h ↦ hS.eigenvalues_antitone hn (by simpa using h)) hxS
  rw [LinearMap.add_apply, inner_add_left, map_add] at hup
  exact (mul_le_mul_iff_left₀ (pow_pos (norm_pos_iff.mpr hx0) 2)).mp (by linarith)

end LinearMap.IsSymmetric

end
end TAF_LiteralSource_0369

section TAF_LiteralSource_0370
/- Original module: TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The functional calculus of a symmetric operator in finite dimension

Let `T` be a symmetric endomorphism of a finite-dimensional inner product space `E` over `ℝ` or
`ℂ` (any `RCLike` field `𝕜`). For a real function `f : ℝ → ℝ`, the operator `f(T)` is the
spectral sum `∑ᵢ f(λᵢ) eᵢ ⊗ eᵢ` over an orthonormal eigenbasis `(eᵢ)` of `T` with eigenvalues
`(λᵢ)`. This file defines it as `LinearMap.IsSymmetric.cfc` and proves the identities that make
it a functional calculus: `f(T)` acts as multiplication by `f(λ)` on every eigenvector of `T` with
eigenvalue `λ`, and it is the unique endomorphism doing so. Everything else follows from this
characterization: `f(T)` is symmetric, depends only on the values of `f` at the eigenvalues of
`T`, is additive and multiplicative in `f`, recovers `T` from the identity function, is compatible
with composition of functions, and is preserved by every linear map intertwining two symmetric
operators. In particular `f(T)` commutes with every endomorphism commuting with `T`. A bound on
`|f|` at the eigenvalues of `T` bounds the norm of `f(T)`.

No continuity of `f` is required, and the construction works uniformly over `RCLike` scalars by
finite sums, without any `C⋆`-algebra structure. It agrees with Mathlib's continuous functional
calculus of the corresponding bounded operator: see
`LinearMap.IsSymmetric.toContinuousLinearMap_cfc`. A function that is nonnegative at the
eigenvalues of `T` gives a positive operator; applied to `Real.sqrt` on a positive operator, this
yields the positive square root `LinearMap.IsPositive.sqrt`.

The name follows `Matrix.IsHermitian.cfc`, Mathlib's eigenbasis construction of the functional
calculus of a Hermitian matrix.

## Main declarations

* `LinearMap.IsSymmetric.cfc`: the functional calculus `f(T)` of a symmetric operator `T`.
* `LinearMap.IsSymmetric.cfc_apply_of_apply_eq_smul`: `f(T)x = f(λ)x` whenever `Tx = λx`.
* `LinearMap.IsSymmetric.eq_cfc_iff`: `f(T)` is the unique endomorphism acting by `f(λ)` on
  the eigenvectors of `T` with eigenvalue `λ`.
* `LinearMap.IsSymmetric.cfc_eq_sum`: the spectral sum formula over any ordered eigenbasis.
* `LinearMap.IsSymmetric.isSymmetric_cfc`, `LinearMap.IsSymmetric.cfc_congr`,
  `LinearMap.IsSymmetric.cfc_id`, `LinearMap.IsSymmetric.cfc_mul`,
  `LinearMap.IsSymmetric.cfc_comp`: the algebraic laws of the calculus.
* `LinearMap.IsSymmetric.isPositive_cfc`: `f(T)` is positive when `f` is nonnegative at the
  eigenvalues of `T`.
* `LinearMap.IsSymmetric.comp_cfc_eq_cfc_comp` and `LinearMap.IsSymmetric.commute_cfc`:
  intertwiners of symmetric operators intertwine their functional calculi; in particular the
  commutant of `T` commutes with `f(T)`.
* `LinearMap.IsSymmetric.norm_cfc_apply_le`: `‖f(T)x‖ ≤ c‖x‖` when `|f| ≤ c` on the eigenvalues
  of `T`.
* `LinearMap.IsSymmetric.norm_cfc_apply_sq_add_norm_cfc_apply_sq`: `‖f(T)x‖² + ‖g(T)x‖² = ‖x‖²`
  when `f² + g² = 1` on the eigenvalues of `T`.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  §§2.5 and 7.2 (the spectral theorem and functions of Hermitian matrices).
-/

public section

open Module.End InnerProductSpace
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {T : E →ₗ[𝕜] E} {n : ℕ}

/-- The functional calculus `f(T)` of a symmetric operator `T` on a finite-dimensional inner
product space: the spectral sum `∑ᵢ f(λᵢ) eᵢ ⊗ eᵢ` of the rank-one projections
`eᵢ ⊗ eᵢ = rankOne 𝕜 eᵢ eᵢ` over Mathlib's ordered orthonormal eigenbasis `(eᵢ)` of `T`, whose
eigenvalues are `(λᵢ)`.

The result does not depend on the choice of eigenbasis: see `cfc_eq_sum` and `eq_cfc_iff`. -/
noncomputable def cfc (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i, (f (hT.eigenvalues rfl i) : 𝕜) •
    (rankOne 𝕜 (hT.eigenvectorBasis rfl i) (hT.eigenvectorBasis rfl i) : E →ₗ[𝕜] E)

/-- For an eigenvector `x` of `T` with eigenvalue `μ`, the spectral coefficient
`f(λᵢ)⟪eᵢ, x⟫` equals `f(μ)⟪eᵢ, x⟫`: either `λᵢ = μ`, or `eᵢ` is orthogonal to `x`. -/
private theorem coe_mul_inner_eigenvectorBasis_eq (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) {x : E} {μ : ℝ} (hx : T x = (μ : 𝕜) • x)
    (i : Fin n) :
    (f (hT.eigenvalues hn i) : 𝕜) * ⟪hT.eigenvectorBasis hn i, x⟫_𝕜 =
      (f μ : 𝕜) * ⟪hT.eigenvectorBasis hn i, x⟫_𝕜 := by
  by_cases hμ : hT.eigenvalues hn i = μ
  · rw [hμ]
  have h0 := hT.orthogonalFamily_eigenspaces (by exact_mod_cast hμ)
    ⟨_, mem_eigenspace_iff.mpr (hT.apply_eigenvectorBasis hn i)⟩ ⟨x, mem_eigenspace_iff.mpr hx⟩
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply] at h0
  rw [h0, mul_zero, mul_zero]

/-- The spectral sum over any ordered eigenbasis acts by `f(μ)` on an eigenvector with
eigenvalue `μ`. -/
private theorem sum_rankOne_apply_of_apply_eq_smul (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) {x : E} {μ : ℝ} (hx : T x = (μ : 𝕜) • x) :
    (∑ i, (f (hT.eigenvalues hn i) : 𝕜) •
      (rankOne 𝕜 (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) : E →ₗ[𝕜] E)) x =
      (f μ : 𝕜) • x := by
  conv_rhs => rw [← (hT.eigenvectorBasis hn).sum_repr' x, Finset.smul_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, smul_smul, coe_mul_inner_eigenvectorBasis_eq hT hn f hx]

/-- **Eigenvector action.** If `Tx = μx`, then `f(T)x = f(μ)x`. -/
theorem cfc_apply_of_apply_eq_smul (hT : T.IsSymmetric) (f : ℝ → ℝ) {x : E} {μ : ℝ}
    (hx : T x = (μ : 𝕜) • x) : hT.cfc f x = (f μ : 𝕜) • x :=
  sum_rankOne_apply_of_apply_eq_smul hT rfl f hx

/-- The functional calculus acts diagonally on every ordered eigenbasis of `T`. -/
@[simp]
theorem cfc_apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (f : ℝ → ℝ) (i : Fin n) :
    hT.cfc f (hT.eigenvectorBasis hn i) =
      (f (hT.eigenvalues hn i) : 𝕜) • hT.eigenvectorBasis hn i :=
  hT.cfc_apply_of_apply_eq_smul f (hT.apply_eigenvectorBasis hn i)

/-- **Uniqueness.** An endomorphism equals `f(T)` exactly when it acts as multiplication by `f(μ)`
on every eigenvector of `T` with eigenvalue `μ`. -/
theorem eq_cfc_iff (hT : T.IsSymmetric) (f : ℝ → ℝ) {S : E →ₗ[𝕜] E} :
    S = hT.cfc f ↔ ∀ (μ : ℝ) (x : E), T x = (μ : 𝕜) • x → S x = (f μ : 𝕜) • x := by
  refine ⟨fun h μ x hx ↦ h ▸ hT.cfc_apply_of_apply_eq_smul f hx, fun h ↦ ?_⟩
  refine (hT.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, cfc_apply_eigenvectorBasis,
    h _ _ (hT.apply_eigenvectorBasis rfl i)]

/-- The functional calculus is the spectral sum over any ordered eigenbasis of `T`. -/
theorem cfc_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) :
    hT.cfc f = ∑ i, (f (hT.eigenvalues hn i) : 𝕜) •
      (rankOne 𝕜 (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) : E →ₗ[𝕜] E) :=
  ((hT.eq_cfc_iff f).mpr fun _ _ hx ↦ sum_rankOne_apply_of_apply_eq_smul hT hn f hx).symm

/-- The spectral expansion of `f(T)x` in any ordered eigenbasis of `T`. -/
theorem cfc_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (f : ℝ → ℝ) (x : E) :
    hT.cfc f x = ∑ i, ((f (hT.eigenvalues hn i) : 𝕜) * ⟪hT.eigenvectorBasis hn i, x⟫_𝕜) •
      hT.eigenvectorBasis hn i := by
  simp [hT.cfc_eq_sum hn, smul_smul]

/-- The functional calculus of a symmetric operator is symmetric. -/
theorem isSymmetric_cfc (hT : T.IsSymmetric) (f : ℝ → ℝ) : (hT.cfc f).IsSymmetric :=
  isSymmetric_sum _ fun _ _ ↦ (isSymmetric_rankOne_self _).smul (RCLike.conj_ofReal _)

/-- The functional calculus only depends on the values of `f` at the eigenvalues of `T`. -/
theorem cfc_congr (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (hfg : ∀ μ : ℝ, HasEigenvalue T (μ : 𝕜) → f μ = g μ) : hT.cfc f = hT.cfc g := by
  refine (hT.eq_cfc_iff g).mpr fun μ x hx ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rw [hT.cfc_apply_of_apply_eq_smul f hx,
    hfg μ (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hx, hx0⟩)]

/-- The identity function recovers the operator. -/
@[simp]
theorem cfc_id (hT : T.IsSymmetric) : hT.cfc _root_.id = T :=
  ((hT.eq_cfc_iff _root_.id).mpr fun _ _ hx ↦ hx).symm

/-- The identity function, written as a lambda, recovers the operator. -/
@[simp]
theorem cfc_id' (hT : T.IsSymmetric) : hT.cfc (fun μ ↦ μ) = T :=
  hT.cfc_id

/-- A constant function gives the corresponding multiple of the identity. -/
@[simp]
theorem cfc_const (hT : T.IsSymmetric) (c : ℝ) : hT.cfc (fun _ ↦ c) = (c : 𝕜) • 1 :=
  ((hT.eq_cfc_iff _).mpr fun _ _ _ ↦ rfl).symm

/-- The zero function gives the zero operator. -/
@[simp]
theorem cfc_zero (hT : T.IsSymmetric) : hT.cfc 0 = 0 :=
  ((hT.eq_cfc_iff 0).mpr fun _ _ _ ↦ by simp).symm

/-- The constant function `1` gives the identity operator. -/
@[simp]
theorem cfc_one (hT : T.IsSymmetric) : hT.cfc 1 = 1 :=
  ((hT.eq_cfc_iff 1).mpr fun _ _ _ ↦ by simp).symm

/-- The functional calculus is additive in the function. -/
theorem cfc_add (hT : T.IsSymmetric) (f g : ℝ → ℝ) : hT.cfc (f + g) = hT.cfc f + hT.cfc g :=
  ((hT.eq_cfc_iff _).mpr fun _ _ hx ↦ by
    rw [LinearMap.add_apply, hT.cfc_apply_of_apply_eq_smul f hx,
      hT.cfc_apply_of_apply_eq_smul g hx, Pi.add_apply, RCLike.ofReal_add, add_smul]).symm

/-- **Product law.** The functional calculus is multiplicative in the function:
`(fg)(T) = f(T)g(T)`. -/
theorem cfc_mul (hT : T.IsSymmetric) (f g : ℝ → ℝ) : hT.cfc (f * g) = hT.cfc f * hT.cfc g :=
  ((hT.eq_cfc_iff _).mpr fun _ _ hx ↦ by
    rw [Module.End.mul_apply, hT.cfc_apply_of_apply_eq_smul g hx, map_smul,
      hT.cfc_apply_of_apply_eq_smul f hx, smul_smul, Pi.mul_apply, RCLike.ofReal_mul,
      mul_comm]).symm

/-- Composition of functions corresponds to iterating the functional calculus:
`(g ∘ f)(T) = g(f(T))`. -/
theorem cfc_comp (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    hT.cfc (g ∘ f) = (hT.isSymmetric_cfc f).cfc g :=
  ((hT.eq_cfc_iff _).mpr fun _ _ hx ↦
    (hT.isSymmetric_cfc f).cfc_apply_of_apply_eq_smul g
      (hT.cfc_apply_of_apply_eq_smul f hx)).symm

/-- A linear map intertwining two symmetric operators intertwines their functional calculi:
if `S T = T' S`, then `S f(T) = f(T') S`. -/
theorem comp_cfc_eq_cfc_comp (hT : T.IsSymmetric) {T' : F →ₗ[𝕜] F} (hT' : T'.IsSymmetric)
    {S : E →ₗ[𝕜] F} (hS : S ∘ₗ T = T' ∘ₗ S) (f : ℝ → ℝ) :
    S ∘ₗ hT.cfc f = hT'.cfc f ∘ₗ S := by
  refine (hT.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  have hSe : T' (S (hT.eigenvectorBasis rfl i)) =
      (hT.eigenvalues rfl i : 𝕜) • S (hT.eigenvectorBasis rfl i) := by
    rw [← LinearMap.comp_apply, ← hS, LinearMap.comp_apply, apply_eigenvectorBasis, map_smul]
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearMap.comp_apply,
    cfc_apply_eigenvectorBasis, map_smul, hT'.cfc_apply_of_apply_eq_smul f hSe]

/-- **Commutant preservation.** Every endomorphism commuting with `T` commutes with `f(T)`. -/
theorem commute_cfc (hT : T.IsSymmetric) {S : E →ₗ[𝕜] E} (hS : Commute S T) (f : ℝ → ℝ) :
    Commute S (hT.cfc f) :=
  hT.comp_cfc_eq_cfc_comp hT hS.eq f

/-- **Norm bound.** If `|f(λ)| ≤ c` at every eigenvalue `λ` of `T`, then `‖f(T)x‖ ≤ c‖x‖`. -/
theorem norm_cfc_apply_le (hT : T.IsSymmetric) (f : ℝ → ℝ) {c : ℝ}
    (hf : ∀ μ : ℝ, HasEigenvalue T (μ : 𝕜) → |f μ| ≤ c) (x : E) :
    ‖hT.cfc f x‖ ≤ c * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nontrivial E := nontrivial_of_ne x 0 hx
  let b := hT.eigenvectorBasis rfl
  have hc : 0 ≤ c :=
    (abs_nonneg _).trans (hf _ (hT.hasEigenvalue_eigenvalues rfl ⟨0, Module.finrank_pos⟩))
  have hcoord (i) : ‖⟪b i, hT.cfc f x⟫_𝕜‖ = |f (hT.eigenvalues rfl i)| * ‖⟪b i, x⟫_𝕜‖ := by
    rw [← hT.isSymmetric_cfc f, cfc_apply_eigenvectorBasis, inner_smul_left, norm_mul,
      RCLike.norm_conj, RCLike.norm_ofReal]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, ← b.sum_sq_norm_inner_right, ← b.sum_sq_norm_inner_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [hcoord, mul_pow]
  gcongr
  exact hf _ (hT.hasEigenvalue_eigenvalues rfl i)

/-- **Pythagorean splitting.** If `f(λ)² + g(λ)² = 1` at every eigenvalue `λ` of `T`, then
`‖f(T)x‖² + ‖g(T)x‖² = ‖x‖²`. For instance `f = sin` and `g = cos`. -/
theorem norm_cfc_apply_sq_add_norm_cfc_apply_sq (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (hfg : ∀ μ : ℝ, HasEigenvalue T (μ : 𝕜) → f μ ^ 2 + g μ ^ 2 = 1) (x : E) :
    ‖hT.cfc f x‖ ^ 2 + ‖hT.cfc g x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h1 : hT.cfc f * hT.cfc f + hT.cfc g * hT.cfc g = 1 := by
    rw [← hT.cfc_mul, ← hT.cfc_mul, ← hT.cfc_add, ← hT.cfc_one]
    exact hT.cfc_congr fun μ hμ ↦ by simpa [sq] using hfg μ hμ
  have hsq (h : ℝ → ℝ) : ‖hT.cfc h x‖ ^ 2 = RCLike.re ⟪x, (hT.cfc h * hT.cfc h) x⟫_𝕜 := by
    rw [@norm_sq_eq_re_inner 𝕜, Module.End.mul_apply, hT.isSymmetric_cfc h]
  simp only [hsq, ← map_add, ← inner_add_right, ← LinearMap.add_apply, h1, Module.End.one_apply,
    @norm_sq_eq_re_inner 𝕜 _ _ _ _ x]

/-- **Positivity.** If `f` is nonnegative at every eigenvalue of `T`, then `f(T)` is positive. -/
theorem isPositive_cfc (hT : T.IsSymmetric) {f : ℝ → ℝ}
    (hf : ∀ μ : ℝ, HasEigenvalue T (μ : 𝕜) → 0 ≤ f μ) : (hT.cfc f).IsPositive := by
  -- `f(T) = R * R` for the symmetric operator `R = (√f)(T)`.
  have hR : hT.cfc f = hT.cfc (fun μ ↦ √(f μ)) * hT.cfc (fun μ ↦ √(f μ)) := by
    rw [← cfc_mul]
    exact hT.cfc_congr fun μ hμ ↦ (Real.mul_self_sqrt (hf μ hμ)).symm
  refine ⟨hT.isSymmetric_cfc f, fun x ↦ ?_⟩
  rw [hR, Module.End.mul_apply, hT.isSymmetric_cfc _ _ x]
  exact inner_self_nonneg

end LinearMap.IsSymmetric
end
end TAF_LiteralSource_0370

section TAF_LiteralSource_0371
/- Original module: TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Positive square roots and the finite-dimensional operator modulus

A positive endomorphism of a finite-dimensional real or complex inner product space has a unique
positive square root.  It is obtained by applying the finite symmetric functional calculus to
`Real.sqrt`.  This file develops its kernel, range, norm, and uniqueness properties, then applies
the construction to the source Gram operator `A† A` of a rectangular map.

The resulting `LinearMap.operatorAbs A` is the finite-dimensional operator modulus.  Its square is
`A† A`, it has the same pointwise norms and kernel as `A`, and its range is `(ker A)ᗮ`.  A normal
endomorphism commutes with its modulus.  These facts are the spectral input to finite-dimensional
polar decomposition.

## Main declarations

* `LinearMap.IsPositive.sqrt`: the positive square root of a positive endomorphism.
* `LinearMap.IsPositive.sqrt_sq`: its square is the original endomorphism.
* `LinearMap.IsPositive.sqrt_unique`: uniqueness among positive square roots.
* `LinearMap.IsPositive.sqrt_eq_iff`: the positive square root is the positive endomorphism whose
  square is the original endomorphism.
* `LinearMap.IsPositive.commute_sqrt`: an endomorphism commuting with `T` commutes with `sqrt T`.
* `LinearMap.operatorAbs`: the modulus `sqrt (A† A)` of a rectangular linear map.
* `LinearMap.IsPositive.eq_operatorAbs`: uniqueness among positive square roots of `A† A`.
* `LinearMap.norm_operatorAbs_apply`: `‖|A|x‖ = ‖Ax‖`.
* `LinearMap.ker_operatorAbs`, `LinearMap.range_operatorAbs`: the kernel and range of the modulus.
* `LinearMap.operatorAbs_injective_iff`: the modulus is injective exactly when the map is.
* `LinearMap.commute_operatorAbs_of_commute`: an endomorphism commuting with `A† A` commutes
  with `|A|`.
* `LinearMap.commute_operatorAbs`: a normal endomorphism commutes with its modulus.
* `LinearMap.operatorAbs_comp_of_commute`: `|A P| = |A| P` for an orthogonal projection `P`
  commuting with `A† A`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorems 7.2.6 and 7.3.1.
-/

public section

open Module.End InnerProductSpace
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {T S : E →ₗ[𝕜] E}

namespace IsPositive

/-- The positive square root of a positive endomorphism, defined by the finite symmetric
functional calculus at `Real.sqrt`. -/
noncomputable def sqrt (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  hT.isSymmetric.cfc Real.sqrt

/-- The positive square root acts on an eigenvector by the square root of its eigenvalue. -/
theorem sqrt_apply_of_apply_eq_smul (hT : T.IsPositive) {x : E} {μ : ℝ}
    (hx : T x = (μ : 𝕜) • x) : hT.sqrt x = (√μ : 𝕜) • x :=
  hT.isSymmetric.cfc_apply_of_apply_eq_smul Real.sqrt hx

/-- The positive square root acts diagonally on the ordered eigenbasis. -/
@[simp]
theorem sqrt_apply_eigenvectorBasis (hT : T.IsPositive) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.sqrt (hT.isSymmetric.eigenvectorBasis hn i) =
      (√(hT.isSymmetric.eigenvalues hn i) : 𝕜) • hT.isSymmetric.eigenvectorBasis hn i :=
  hT.sqrt_apply_of_apply_eq_smul (hT.isSymmetric.apply_eigenvectorBasis hn i)

/-- The square root of a positive endomorphism is positive. -/
theorem sqrt_isPositive (hT : T.IsPositive) : hT.sqrt.IsPositive :=
  hT.isSymmetric.isPositive_cfc fun _ _ ↦ Real.sqrt_nonneg _

/-- The positive square root is symmetric. -/
theorem sqrt_isSymmetric (hT : T.IsPositive) : hT.sqrt.IsSymmetric :=
  hT.sqrt_isPositive.isSymmetric

/-- The square of the positive square root is the original endomorphism. -/
@[simp]
theorem sqrt_sq (hT : T.IsPositive) : hT.sqrt ∘ₗ hT.sqrt = T := by
  refine (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  simp [smul_smul, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i),
    hT.isSymmetric.apply_eigenvectorBasis]

/-- The squared norm of `sqrt T x` is the quadratic form of `T` at `x`. -/
theorem norm_sqrt_apply_sq (hT : T.IsPositive) (x : E) :
    ‖hT.sqrt x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, ← hT.sqrt_isSymmetric (hT.sqrt x) x,
    ← comp_apply, hT.sqrt_sq]

/-- The positive square root has the same kernel as the original endomorphism. -/
@[simp]
theorem ker_sqrt (hT : T.IsPositive) : hT.sqrt.ker = T.ker := by
  ext x
  simp only [mem_ker]
  constructor
  · intro hx
    rw [← hT.sqrt_sq, comp_apply, hx, map_zero]
  · intro hx
    have hsquare : ‖hT.sqrt x‖ ^ 2 = 0 := by
      rw [hT.norm_sqrt_apply_sq, hx, inner_zero_left, map_zero]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- The positive square root has the same range as the original endomorphism. -/
@[simp]
theorem range_sqrt (hT : T.IsPositive) : hT.sqrt.range = T.range := by
  calc
    hT.sqrt.range = hT.sqrt.adjoint.range := by rw [hT.sqrt_isPositive.adjoint_eq]
    _ = hT.sqrt.kerᗮ := hT.sqrt.orthogonal_ker.symm
    _ = T.kerᗮ := by rw [hT.ker_sqrt]
    _ = T.adjoint.range := T.orthogonal_ker
    _ = T.range := by rw [hT.adjoint_eq]

/-- The positive square root is a unit exactly when the original endomorphism is a unit. -/
@[simp]
theorem sqrt_isUnit_iff (hT : T.IsPositive) : IsUnit hT.sqrt ↔ IsUnit T := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.isUnit_iff_ker_eq_bot, hT.ker_sqrt]

/-- The positive square root is unique among positive endomorphisms whose square is `T`. -/
theorem sqrt_unique (hT : T.IsPositive) (hS : S.IsPositive) (hST : S ∘ₗ S = T) :
    S = hT.sqrt := by
  refine (hS.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  have hSe := hS.isSymmetric.apply_eigenvectorBasis rfl i
  have hTe : T (hS.isSymmetric.eigenvectorBasis rfl i) =
      ((hS.isSymmetric.eigenvalues rfl i ^ 2 : ℝ) : 𝕜) • hS.isSymmetric.eigenvectorBasis rfl i := by
    simp [← hST, hSe, smul_smul, sq]
  simp [hSe, hT.sqrt_apply_of_apply_eq_smul hTe, Real.sqrt_sq (hS.nonneg_eigenvalues rfl i)]

/-- The positive square root is characterized as the positive endomorphism whose square is `T`. -/
theorem sqrt_eq_iff (hT : T.IsPositive) : hT.sqrt = S ↔ S.IsPositive ∧ S ∘ₗ S = T :=
  ⟨fun h ↦ h ▸ ⟨hT.sqrt_isPositive, hT.sqrt_sq⟩, fun h ↦ (hT.sqrt_unique h.1 h.2).symm⟩

/-- The positive square root of the zero endomorphism is zero. -/
@[simp]
theorem sqrt_zero : (isPositive_zero : (0 : E →ₗ[𝕜] E).IsPositive).sqrt = 0 :=
  (isPositive_zero.sqrt_unique isPositive_zero (zero_comp 0)).symm

/-- The positive square root of the identity is the identity. -/
@[simp]
theorem sqrt_one : (isPositive_one : (1 : E →ₗ[𝕜] E).IsPositive).sqrt = 1 :=
  (isPositive_one.sqrt_unique isPositive_one (id_comp 1)).symm

/-- The positive square root vanishes exactly when the original endomorphism does. -/
@[simp]
theorem sqrt_eq_zero_iff (hT : T.IsPositive) : hT.sqrt = 0 ↔ T = 0 := by
  rw [sqrt_eq_iff, zero_comp, eq_comm]
  exact and_iff_right isPositive_zero

/-- Every endomorphism commuting with `T` commutes with its positive square root. -/
theorem commute_sqrt (hT : T.IsPositive) (hS : Commute S T) : Commute S hT.sqrt :=
  hT.isSymmetric.commute_cfc hS Real.sqrt

end IsPositive

/-- The finite-dimensional modulus of a rectangular linear map is the positive square root of
its source Gram operator `A† A`. -/
noncomputable def operatorAbs (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  (isPositive_adjoint_comp_self A).sqrt

/-- The finite-dimensional modulus is positive. -/
theorem isPositive_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.IsPositive :=
  (isPositive_adjoint_comp_self A).sqrt_isPositive

/-- The finite-dimensional modulus is symmetric. -/
theorem isSymmetric_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.IsSymmetric :=
  A.isPositive_operatorAbs.isSymmetric

/-- The square of the finite-dimensional modulus is the source Gram operator. -/
@[simp]
theorem operatorAbs_sq (A : E →ₗ[𝕜] F) :
    A.operatorAbs ∘ₗ A.operatorAbs = A.adjoint ∘ₗ A :=
  (isPositive_adjoint_comp_self A).sqrt_sq

/-- The modulus is the unique positive endomorphism whose square is the source Gram operator
`A† A`. -/
theorem IsPositive.eq_operatorAbs {A : E →ₗ[𝕜] F} {S : E →ₗ[𝕜] E} (hS : S.IsPositive)
    (h : S ∘ₗ S = A.adjoint ∘ₗ A) : S = A.operatorAbs :=
  (isPositive_adjoint_comp_self A).sqrt_unique hS h

/-- The modulus and the original map have the same pointwise norms. -/
@[simp]
theorem norm_operatorAbs_apply (A : E →ₗ[𝕜] F) (x : E) :
    ‖A.operatorAbs x‖ = ‖A x‖ := by
  rw [operatorAbs, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    (isPositive_adjoint_comp_self A).norm_sqrt_apply_sq]
  simp only [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The modulus and the original map have the same kernel. -/
@[simp]
theorem ker_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.ker = A.ker := by
  rw [operatorAbs, (isPositive_adjoint_comp_self A).ker_sqrt, ker_adjoint_comp_self]

/-- The modulus of a map is injective exactly when the map is. -/
@[simp]
theorem operatorAbs_injective_iff {A : E →ₗ[𝕜] F} :
    Function.Injective A.operatorAbs ↔ Function.Injective A := by
  rw [← ker_eq_bot, ← ker_eq_bot, ker_operatorAbs]

/-- The range of the modulus is the orthogonal complement of the original map's kernel. -/
@[simp]
theorem range_operatorAbs (A : E →ₗ[𝕜] F) : A.operatorAbs.range = A.kerᗮ := by
  rw [operatorAbs, (isPositive_adjoint_comp_self A).range_sqrt,
    range_adjoint_comp_self, ← orthogonal_ker]

/-- An endomorphism commuting with the source Gram operator `A† A` commutes with the modulus. -/
theorem commute_operatorAbs_of_commute {A : E →ₗ[𝕜] F} {S : E →ₗ[𝕜] E}
    (h : Commute S (A.adjoint ∘ₗ A)) : Commute S A.operatorAbs := by
  simpa only [operatorAbs, IsPositive.sqrt] using
    (isSymmetric_adjoint_comp_self A).commute_cfc h Real.sqrt

/-- A normal finite-dimensional endomorphism commutes with its modulus. -/
theorem commute_operatorAbs (A : E →ₗ[𝕜] E) [IsStarNormal A] :
    Commute A A.operatorAbs := by
  refine commute_operatorAbs_of_commute ?_
  simpa only [Module.End.mul_eq_comp, star_eq_adjoint] using
    star_comm_self.symm.mul_right (Commute.refl A)

/-- If an orthogonal projection `P` commutes with the source Gram operator `A† A`, then the
modulus of `A P` is `|A| P`. -/
theorem operatorAbs_comp_of_commute {A : E →ₗ[𝕜] F} {P : E →ₗ[𝕜] E}
    (hP : P.IsSymmetricProjection) (h : Commute P (A.adjoint ∘ₗ A)) :
    (A ∘ₗ P).operatorAbs = A.operatorAbs ∘ₗ P := by
  have hc : Commute P A.operatorAbs := commute_operatorAbs_of_commute h
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hconj : A.operatorAbs ∘ₗ P = P.adjoint ∘ₗ A.operatorAbs ∘ₗ P := by
    rw [hP.isSymmetric.adjoint_eq, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
      ← mul_assoc, hc.eq, mul_assoc, hPP, Module.End.mul_eq_comp]
  refine ((isPositive_adjoint_comp_self (A ∘ₗ P)).sqrt_unique ?_ ?_).symm
  · rw [hconj]
    exact A.isPositive_operatorAbs.adjoint_conj P
  · have hgram : (A ∘ₗ P).adjoint ∘ₗ A ∘ₗ P = P ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ P := by
      simp only [adjoint_comp, hP.isSymmetric.adjoint_eq, comp_assoc]
    rw [hgram, ← operatorAbs_sq]
    simp only [← Module.End.mul_eq_comp, mul_assoc]
    rw [hc.left_comm (A.operatorAbs * P), hc.left_comm P, hPP]

end LinearMap
end
end TAF_LiteralSource_0371

section TAF_LiteralSource_0372
/- Original module: TauCeti.Analysis.InnerProductSpace.RangeProjection -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The orthogonal projection onto the range of an operator

If `B : F →L[𝕜] V` is an operator between inner product spaces whose Gram operator `B† B` is
invertible, the orthogonal projection of `V` onto the range of `B` is `B (B† B)⁻¹ B†`. When `F` is
finite-dimensional, `B† B` is invertible exactly when `B` is injective.

Over `ℝ` this explicit formula shows that the projection depends smoothly on the operator: for a
`C^n` family of injective operators `A u : E →L[ℝ] V` out of a finite-dimensional real normed
space `E`, the orthogonal projections of `V` onto the ranges of `A u` form a `C^n` family. Applied
to the derivative of an immersion into a Euclidean space, this says that the tangent spaces, and
hence the normal spaces, of an immersed submanifold vary smoothly.

## Main results

* `ContinuousLinearMap.isUnit_adjoint_comp_self_iff`: the Gram operator of an operator out of a
  finite-dimensional space is invertible exactly when the operator is injective.
* `ContinuousLinearMap.starProjection_range_eq`: the formula `B (B† B)⁻¹ B†` for the orthogonal
  projection onto the range of `B`.
* `ContinuousLinearMap.comp_adjoint_eq_starProjection_range`: for an isometry `B` it reduces to
  `B B†`.
* `LinearMap.finrank_orthogonal_range_of_injective`: the dimension of the orthogonal
  complement of the range of an injective operator.
* `Submodule.starProjection_inverse_apply`: if the compression to `W` of the orthogonal projection
  onto `K` is invertible, it inverts the projection from `W` onto `K`.
* `ContDiffAt.starProjection_range`, `ContDiffAt.starProjection_orthogonal_range`: the orthogonal
  projections onto the range of a `C^n` family of injective operators, and onto its orthogonal
  complement, are `C^n`.
-/

public section

open Function Filter Topology

namespace ContinuousLinearMap

variable {𝕜 F V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

section Adjoint

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [CompleteSpace V]

/-- The Gram operator `B† B` of an operator out of a finite-dimensional space is invertible
exactly when `B` is injective. -/
theorem isUnit_adjoint_comp_self_iff [FiniteDimensional 𝕜 F] (B : F →L[𝕜] V) :
    IsUnit (adjoint B ∘L B) ↔ Injective B := by
  simp only [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    ker_adjoint_comp_self, LinearMap.ker_eq_bot, coe_coe]

/-- The orthogonal projection onto the range of `B` is `B (B† B)⁻¹ B†`, when the Gram operator
`B† B` is invertible. -/
theorem starProjection_range_eq {B : F →L[𝕜] V} [B.range.HasOrthogonalProjection]
    (hB : IsUnit (adjoint B ∘L B)) :
    B.range.starProjection = B ∘L Ring.inverse (adjoint B ∘L B) ∘L adjoint B := by
  have hG : (adjoint B ∘L B) ∘L Ring.inverse (adjoint B ∘L B) = 1 :=
    Ring.mul_inverse_cancel _ hB
  ext v
  rw [comp_apply, comp_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) _) ?_
  rintro _ ⟨x, rfl⟩
  have h := congrArg (fun T : F →L[𝕜] F => T (adjoint B v)) hG
  simp only [comp_apply, one_apply_eq_self] at h
  rw [coe_coe, inner_sub_left]
  simp only [← adjoint_inner_left, h, sub_self]

/-- For an isometry `B`, the operator `B B†` is the orthogonal projection onto the range of `B`. -/
theorem comp_adjoint_eq_starProjection_range {B : F →L[𝕜] V} (hB : Isometry B)
    [B.range.HasOrthogonalProjection] : B ∘L adjoint B = B.range.starProjection := by
  have h := (isometry_iff_adjoint_comp_self B).1 hB
  rw [starProjection_range_eq (h ▸ isUnit_one), h, Ring.inverse_one, one_def, id_comp]

end Adjoint

section Range

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- The orthogonal projection onto the range of `B` fixes every value of `B`. -/
@[simp]
theorem starProjection_range_apply (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection] (x : F) :
    B.range.starProjection (B x) = B x :=
  Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) x)

/-- The orthogonal projection onto the complement of the range of `B` kills every value of `B`. -/
theorem starProjection_orthogonal_range_apply (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection]
    (x : F) : B.rangeᗮ.starProjection (B x) = 0 :=
  Submodule.starProjection_orthogonal_apply_eq_zero (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) x)

/-- An operator followed by the orthogonal projection onto its range is unchanged. -/
@[simp]
theorem starProjection_range_comp (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection] :
    B.range.starProjection ∘L B = B := by
  ext x
  simp

/-- An operator followed by the orthogonal projection onto the complement of its range is zero. -/
@[simp]
theorem starProjection_orthogonal_range_comp (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection] :
    B.rangeᗮ.starProjection ∘L B = 0 := by
  ext x
  simp

end Range

end ContinuousLinearMap

section LinearMap

variable {𝕜 E V : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The orthogonal complement of the range of an injective operator into a finite-dimensional
inner product space has the expected dimension. -/
theorem LinearMap.finrank_orthogonal_range_of_injective {A : E →ₗ[𝕜] V}
    (hA : Injective A) :
    Module.finrank 𝕜 A.rangeᗮ = Module.finrank 𝕜 V - Module.finrank 𝕜 E := by
  have h := Submodule.finrank_add_finrank_orthogonal A.range
  rw [LinearMap.finrank_range_of_inj hA] at h
  omega

end LinearMap

section Submodule

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Let `K` be a finite-dimensional subspace and `W` a projected subspace of the same dimension.
If the compression `R = π_W ∘ P_K ∘ ι_W` of the orthogonal projection onto `K` is invertible, then
`P_K` maps `W` onto `K`, and the preimage of `v ∈ K` is `R⁻¹ (π_W v)`. -/
theorem Submodule.starProjection_inverse_apply {K W : Submodule 𝕜 V}
    [FiniteDimensional 𝕜 K] [W.HasOrthogonalProjection]
    (hrank : Module.finrank 𝕜 W = Module.finrank 𝕜 K)
    (hR : IsUnit (W.orthogonalProjectionOnto ∘L K.starProjection ∘L W.subtypeL)) {v : V}
    (hv : v ∈ K) :
    K.starProjection (Ring.inverse (W.orthogonalProjectionOnto ∘L K.starProjection ∘L W.subtypeL)
      (W.orthogonalProjectionOnto v)) = v := by
  set R := W.orthogonalProjectionOnto ∘L K.starProjection ∘L W.subtypeL
  have hRinj : Injective R :=
    (Module.End.isUnit_iff _).mp (hR.map ContinuousLinearMap.toLinearMapRingHom) |>.1
  -- `P_K` restricted to `W` is injective because its compression `R` is, hence onto `K`.
  let κ : W →L[𝕜] K := K.orthogonalProjectionOnto ∘L W.subtypeL
  have hκ : Injective κ := fun w w' h => hRinj <| by
    simp only [R, ContinuousLinearMap.comp_apply]
    exact congrArg (fun z : K => W.orthogonalProjectionOnto (z : V)) h
  have : FiniteDimensional 𝕜 W := FiniteDimensional.of_injective κ.toLinearMap hκ
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := κ.toLinearMap)).mp hκ ⟨v, hv⟩
  have hw' : K.starProjection w = v := by
    simpa only [κ, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      Submodule.coe_orthogonalProjectionOnto_apply, Submodule.subtypeL_apply]
      using congrArg Subtype.val hw
  have hRw : R w = W.orthogonalProjectionOnto v := by simp [R, hw']
  have hinv : Ring.inverse R (R w) = w := by
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hR, one_apply_eq_self]
  rw [← hRw, hinv, hw']

end Submodule

section ContDiffAt

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The orthogonal projection onto the range of a `C^n` family of operators out of a
finite-dimensional space is `C^n` at every point where the operator is injective. -/
theorem ContDiffAt.starProjection_range {A : X → E →L[ℝ] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).range.starProjection) u₀ := by
  -- Precompose with a linear isomorphism from a Euclidean space, so that adjoints exist.
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let j : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [F])
  let B : X → F →L[ℝ] V := fun u => (A u).comp (j : F →L[ℝ] E)
  have hrange : ∀ u, (B u).range = (A u).range := fun u =>
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr j.surjective)
  have hB : ContDiffAt ℝ n B u₀ := hA.clm_comp contDiffAt_const
  have hB' : ContDiffAt ℝ n (fun u => ContinuousLinearMap.adjoint (B u)) u₀ :=
    (ContinuousLinearMap.adjoint : (F →L[ℝ] V) ≃ₗᵢ[ℝ] (V →L[ℝ] F)).contDiff.contDiffAt.comp u₀ hB
  have hG : IsUnit (ContinuousLinearMap.adjoint (B u₀) ∘L B u₀) :=
    (ContinuousLinearMap.isUnit_adjoint_comp_self_iff _).mpr (hinj.comp j.injective)
  have hinv : ContDiffAt ℝ n
      (fun u => Ring.inverse (ContinuousLinearMap.adjoint (B u) ∘L B u)) u₀ := by
    have := contDiffAt_ringInverse ℝ (n := n) hG.unit
    rw [hG.unit_spec] at this
    exact this.comp u₀ (hB'.clm_comp hB)
  -- Near `u₀` the operators stay injective, so the projection is given by the Gram formula.
  have hev : ∀ᶠ u in 𝓝 u₀, Injective (B u) :=
    hB.continuousAt.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds (hinj.comp j.injective))
  refine (hB.clm_comp (hinv.clm_comp hB')).congr_of_eventuallyEq ?_
  filter_upwards [hev] with u hu
  simp only [← hrange u]
  exact ContinuousLinearMap.starProjection_range_eq
    ((ContinuousLinearMap.isUnit_adjoint_comp_self_iff _).mpr hu)

/-- The orthogonal projection onto the orthogonal complement of the range of a `C^n` family of
operators out of a finite-dimensional space is `C^n` at every point where the operator is
injective. -/
theorem ContDiffAt.starProjection_orthogonal_range {A : X → E →L[ℝ] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).rangeᗮ.starProjection) u₀ := by
  refine (contDiffAt_const (c := (1 : V →L[ℝ] V))).sub (hA.starProjection_range hinj)
    |>.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => Submodule.starProjection_orthogonal' _

end ContDiffAt
end
end TAF_LiteralSource_0372

section TAF_LiteralSource_0373
/- Original module: TauCeti.Data.Finsupp.Antitone -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Antitone finitely supported sequences

A finitely supported sequence `f : ℕ →₀ α` that is antitone takes only nonnegative values, and
it is determined by how many times it takes each nonzero value: it lists its nonzero values in
nonincreasing order, followed by zeros. Sorted, zero-padded sequences of this kind are how
Mathlib records singular values (`LinearMap.singularValues`), so this is the uniqueness
principle used to identify two such sequences from their multiplicities.
Nonnegativity holds in any preorder, and uniqueness requires only a partial order on the values.

## Main declarations

* `Finsupp.nonneg_of_antitone`: an antitone finitely supported sequence is nonnegative.
* `Finsupp.eq_of_antitone_of_ncard_eq`: two antitone finitely supported sequences that take
  every nonzero value equally often are equal.
-/

public section

namespace Finsupp

variable {α : Type*} [Zero α]

/-- An antitone finitely supported sequence takes only nonnegative values. -/
theorem nonneg_of_antitone [Preorder α] {f : ℕ →₀ α} (hf : Antitone f) (i : ℕ) :
    0 ≤ f i := by
  obtain ⟨n, hn⟩ := f.support.exists_nat_subset_range
  have hfn : f (max i n) = 0 :=
    notMem_support_iff.mp fun h ↦ (Finset.mem_range.mp (hn h)).not_ge (le_max_right i n)
  exact hfn ▸ hf (le_max_left i n)

/-- If two sequences agree below `i` and take each nonzero value equally often, the `i`-th
entry of the first lies below that of the second whenever the second is antitone. -/
private theorem le_of_antitone_of_ncard_eq [Preorder α] {f g : ℕ →₀ α} (hg : Antitone g)
    {i : ℕ} (hfg : ∀ j < i, f j = g j)
    (h : ∀ a ≠ 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : f i ≤ g i := by
  by_contra hi
  have hfi : f i ≠ 0 := fun hfi ↦ hi (hfi ▸ nonneg_of_antitone hg i)
  refine (Set.ncard_lt_ncard ⟨fun j hj ↦ ?_, fun h ↦ ?_⟩ <|
    f.support.finite_toSet.subset (t := {j | f j = f i}) fun j (hj : f j = f i) ↦
      mem_support_iff.mpr (hj ▸ hfi)).ne
      (h _ hfi).symm
  · have hji : j < i := lt_of_not_ge fun hij ↦ hi (hj ▸ hg hij)
    exact (hfg j hji).trans hj
  · exact hi (h (rfl : f i = f i)).ge

/-- An antitone finitely supported sequence is determined by how many times it takes each nonzero
value. -/
theorem eq_of_antitone_of_ncard_eq [PartialOrder α] {f g : ℕ →₀ α}
    (hf : Antitone f) (hg : Antitone g)
    (h : ∀ a ≠ 0, {i | f i = a}.ncard = {i | g i = a}.ncard) : f = g := by
  ext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    exact le_antisymm (le_of_antitone_of_ncard_eq hg ih h)
      (le_of_antitone_of_ncard_eq hf (fun j hj ↦ (ih j hj).symm) fun a ha ↦ (h a ha).symm)

end Finsupp
end
end TAF_LiteralSource_0373

section TAF_LiteralSource_0374
/- Original module: TauCeti.LinearAlgebra.Eigenspace.Comp -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Eigenspaces of `g ∘ f` and `f ∘ g`

For linear maps `f : M → N` and `g : N → M` and a unit `μ`, the map `f` carries the
`μ`-eigenspace of `g ∘ f` isomorphically onto the `μ`-eigenspace of `f ∘ g`, with inverse
`μ⁻¹ • g`. In particular the two composites have the same eigenvalue multiplicities at every
nonzero eigenvalue over a field. This is the multiplicity form of Mathlib's
`spectrum.nonzero_mul_comm`, and applied to `f = A` and `g = A†` it shows that the source and
target Gram operators `A† A` and `A A†` of a linear map between inner product spaces have the
same nonzero eigenvalues with multiplicity.

## Main declarations

* `Module.End.eigenspaceCompEquiv`: the linear equivalence induced by `f` between the
  `μ`-eigenspaces of `g ∘ₗ f` and `f ∘ₗ g`.
* `Module.End.finrank_eigenspace_comp_comm`: the two eigenspaces have the same dimension.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 1.3.22.
-/

public section

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `f` maps the `μ`-eigenspace of `g ∘ₗ f` into the `μ`-eigenspace of `f ∘ₗ g`. -/
theorem apply_mem_eigenspace_comp {f : M →ₗ[R] N} {g : N →ₗ[R] M} {μ : R} {x : M}
    (hx : x ∈ eigenspace (g ∘ₗ f) μ) : f x ∈ eigenspace (f ∘ₗ g) μ := by
  rw [mem_eigenspace_iff] at hx ⊢
  simpa using congrArg f hx

/-- For a unit `μ`, `f` restricts to a linear equivalence from the `μ`-eigenspace of `g ∘ₗ f`
onto the `μ`-eigenspace of `f ∘ₗ g`; the inverse is the restriction of `μ⁻¹ • g`. -/
noncomputable def eigenspaceCompEquiv (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) :
    eigenspace (g ∘ₗ f) μ ≃ₗ[R] eigenspace (f ∘ₗ g) μ :=
  LinearEquiv.ofLinearMap (f.restrict fun _ ↦ apply_mem_eigenspace_comp)
    (((↑hμ.unit⁻¹ : R) • g).restrict fun _ hy ↦ Submodule.smul_mem _ _ <|
      apply_mem_eigenspace_comp hy)
    (by
      ext ⟨y, hy⟩
      rw [mem_eigenspace_iff] at hy
      simpa [smul_smul] using congrArg ((↑hμ.unit⁻¹ : R) • ·) hy)
    (by
      ext ⟨x, hx⟩
      rw [mem_eigenspace_iff] at hx
      simpa [smul_smul] using congrArg ((↑hμ.unit⁻¹ : R) • ·) hx)

@[simp]
theorem coe_eigenspaceCompEquiv_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ)
    (x : eigenspace (g ∘ₗ f) μ) : (eigenspaceCompEquiv f g hμ x : N) = f x :=
  (rfl)

@[simp]
theorem coe_eigenspaceCompEquiv_symm_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R}
    (hμ : IsUnit μ) (y : eigenspace (f ∘ₗ g) μ) :
    ((eigenspaceCompEquiv f g hμ).symm y : M) = (↑hμ.unit⁻¹ : R) • g y :=
  (rfl)

/-- At a unit `μ`, the `μ`-eigenspaces of `g ∘ₗ f` and `f ∘ₗ g` have the same dimension. -/
theorem finrank_eigenspace_comp_comm (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) :
    finrank R (eigenspace (g ∘ₗ f) μ) = finrank R (eigenspace (f ∘ₗ g) μ) :=
  (eigenspaceCompEquiv f g hμ).finrank_eq

end Module.End
end
end TAF_LiteralSource_0374

section TAF_LiteralSource_0375
/- Original module: TauCeti.Analysis.InnerProductSpace.SingularValues -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Singular values, the two Gram spectra, and the singular system

Mathlib defines the singular values of a linear map `A : E →ₗ[𝕜] F` between finite-dimensional
inner product spaces from the source Gram operator `A† A` (`LinearMap.singularValues`). This file
shows that the target Gram operator `A A†` carries the same information: the nonzero eigenvalues
of `A† A` and `A A†` agree with multiplicity, so their sorted eigenvalue lists agree through the
common dimension and vanish beyond the rank of `A`. Equivalently, `A` and `A†` have the same
singular values.

The multiplicity statement is `Module.End.finrank_eigenspace_comp_comm` applied to `A` and `A†`.
A positive value `s` occurs among the singular values of `A` as often as `s²` occurs among the
eigenvalues of `A† A` (`LinearMap.ncard_ofPred_singularValues_eq`), and a sorted zero-padded
sequence is determined by these multiplicities (`Finsupp.eq_of_antitone_of_ncard_eq`).

## Main declarations

* `LinearMap.ncard_ofPred_singularValues_eq`: the multiplicity of a positive singular value `s`
  is the dimension of the `s²`-eigenspace of `A† A`.
* `LinearMap.singularValues_adjoint`: `A†` has the same singular values as `A`.
* `LinearMap.sq_singularValues_eq_eigenvalues_self_comp_adjoint`: the squared singular values
  are also the sorted eigenvalues of `A A†`.
* `LinearMap.eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint`: the sorted
  eigenvalues of `A† A` and `A A†` agree at every index below both dimensions.
* `LinearMap.eigenvalues_adjoint_comp_self_eq_zero_iff`,
  `LinearMap.eigenvalues_self_comp_adjoint_eq_zero_iff`: both sorted eigenvalue lists vanish
  exactly from the rank of `A` on.

## The singular system

The second half of the file builds the singular system of `A` from these spectra. The right
singular basis `(vᵢ) = A.rightSingularBasis` is the ordered orthonormal eigenbasis of `A† A`, in
whose order the singular values are listed (`LinearMap.sq_singularValues_fin`), and the left
singular vectors are `uᵢ = σᵢ⁻¹ A vᵢ = A.leftSingularVector i`, using total field inversion so
that `uᵢ = 0` when `σᵢ = 0`. The singular relations hold at every index, which lets the expansion
of `A` run over the whole basis without splitting off the kernel.

* `LinearMap.sq_singularValues_antitone`: the squared singular values are nonincreasing.
* `LinearMap.sq_singularValues_eq_of_adjoint_comp_self_eigenbasis`: any sorted orthonormal
  Gram eigenbasis recovers the squared singular values, with a zero tail.
* `LinearMap.norm_apply_le_of_mem_spanIndices_of_adjoint_comp_self_eigenbasis`: an upper bound
  for `‖A x‖` on a span of Gram eigenvectors with bounded eigenvalues.
* `LinearMap.adjoint_comp_self_rightSingularBasis`: `A† A vᵢ = σᵢ² vᵢ`.
* `LinearMap.singularValues_eq_single_of_finrank_eq_one`: on a one-dimensional source the only
  singular value is `‖A x‖` for a unit vector `x`.
* `LinearMap.singularValues_mul_norm_le_norm_apply`,
  `LinearMap.norm_apply_le_singularValues_mul_norm`: `σₙ ‖x‖ ≤ ‖A x‖` on the span of the `vᵢ`
  with `i ≤ n`, and `‖A x‖ ≤ σₙ ‖x‖` on the span of the `vᵢ` with `n ≤ i`.
* `LinearMap.apply_rightSingularBasis`: `A vᵢ = σᵢ uᵢ`.
* `LinearMap.adjoint_leftSingularVector`: `A† uᵢ = σᵢ vᵢ`.
* `LinearMap.self_comp_adjoint_leftSingularVector`: `A A† uᵢ = σᵢ² uᵢ`.
* `LinearMap.orthonormal_leftSingularVector`: the `uᵢ` with `σᵢ ≠ 0` are orthonormal.
* `LinearMap.sum_norm_inner_leftSingularVector_sq_le`: Bessel's inequality for the whole family
  `(uᵢ)`, zero vectors included.
* `LinearMap.apply_eq_sum_singularValues_smul`: `A x = ∑ᵢ σᵢ ⟪vᵢ, x⟫ uᵢ`.
* `LinearMap.eq_sum_singularValues_smul_rankOne`: `A = ∑ᵢ σᵢ uᵢ ⊗ vᵢ`, the singular value
  decomposition in rank-one form.
* `LinearMap.exists_orthonormalBasis_apply_eq_leftSingularVector`: the nonzero left singular
  vectors extend, index by index, to an orthonormal basis of the codomain.

## Comparison of singular values

The comparison section compares the singular values of two maps with the same source through the
Courant–Fischer min–max principle for their source Gram operators.

* `LinearMap.singularValues_le_mul_of_norm_apply_le`: if `‖B x‖ ≤ c ‖A x‖` for every `x`, then
  `σᵢ(B) ≤ c σᵢ(A)` for every `i`.
* `LinearMap.singularValues_comp_le`: if `‖C y‖ ≤ c ‖y‖` for every `y`, then
  `σᵢ(C A) ≤ c σᵢ(A)` for every `i`.
* `LinearMap.singularValues_le_of_norm_apply_le`: if `‖A x‖ ≤ c ‖x‖` for every `x`, with
  `c ≥ 0`, then `σᵢ(A) ≤ c` for every `i`.
* `LinearMap.singularValues_eq_of_norm_apply_eq`: if `‖B x‖ = ‖A x‖` for every `x`, then `A` and
  `B` have the same singular values.
* `LinearMap.singularValues_operatorAbs`: the modulus `|A| = √(A† A)` has the same singular values
  as `A`.
* `LinearMap.singularValues_linearIsometry_comp`,
  `LinearMap.singularValues_comp_adjoint_linearIsometry`: composing on the left with a linear
  isometry, or on the right with the adjoint of one, leaves the singular values unchanged.
* `LinearMap.singularValues_linearIsometryEquiv_comp`,
  `LinearMap.singularValues_comp_linearIsometryEquiv`: composing with isometric isomorphisms on
  either side leaves the singular values unchanged.
* `ContinuousLinearMap.singularValues_comp_starProjection_range`: an operator into any finite-
  dimensional inner product space has the same singular values after a range projection as
  after the corresponding isometric trial map.

## Diagonal models

For an orthonormal basis `(eᵢ)` of `E` and scalars `(dᵢ)`, the diagonal operator with `eᵢ` as
eigenvectors and diagonal entries `dᵢ` is Mathlib's
`Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)`. Its additivity in `d`
(`Matrix.diagonal_add`), its adjoint (`Matrix.toLin_conjTranspose` with
`Matrix.diagonal_conjTranspose`) and its symmetry for real entries (`Matrix.isSymmetric_toLin_iff`)
are in Mathlib. The diagonal section computes its singular values and shows that every map is a
diagonal map up to isometries on both sides.

* `Matrix.toLin_diagonal_apply_self`: the diagonal operator sends `eᵢ` to `dᵢ eᵢ`.
* `Matrix.adjoint_comp_self_toLin_diagonal_apply`: the Gram operator sends `eᵢ` to
  `‖dᵢ‖² eᵢ`.
* `OrthonormalBasis.adjoint_comp_self_toLin_diagonal_reindex_apply`: the same Gram relation
  in a reordered diagonal basis.
* `Matrix.singularValues_toLin_diagonal`: the singular values of the diagonal operator are the
  norms `‖dᵢ‖` listed in nonincreasing order.
* `Matrix.toLin_of_ite_val_eq_apply`: the rectangular diagonal map with entries `dₖ` sends `eᵢ` to
  `dᵢ fᵢ` when `i` is also an index of `(fⱼ)`, and to `0` otherwise.
* `LinearMap.exists_linearIsometryEquiv_eq_comp_toLin_comp`: every map `A : E →ₗ[𝕜] F` is `U D V`
  for linear isometric equivalences `U` of `F` and `V` of `E` and the rectangular diagonal map `D`
  with the singular values of `A` on its diagonal, in any prescribed orthonormal bases.
* `LinearMap.exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp`: every endomorphism `A` is
  `U D V` for linear isometric equivalences `U`, `V` and the diagonal operator `D` with the
  singular values of `A` as entries, in any prescribed orthonormal basis.
* `LinearMap.exists_orthonormal_eq_sum_singularValues_smul_rankOne`: the compact singular value
  decomposition `A = ∑_{i < p} σᵢ wᵢ ⊗ vᵢ`, with `p = min (dim E) (dim F)` and both families
  orthonormal.

## Orthogonal-tail bound for bounded maps

The final section transfers the Gram-eigenbasis estimate to bounded maps, supplying the tail
bound used in the Eckart–Young and attainment theorems.

* `ContinuousLinearMap.norm_comp_orthogonal_spanIndices_le_of_adjoint_comp_self_eigenbasis`:
  the norm on the orthogonal complement of the first `n` vectors of a sorted Gram eigenbasis
  is at most the `n`-th singular value, including indices beyond the source dimension.

## Source

The singular-system definitions `LinearMap.rightSingularBasis` and
`LinearMap.leftSingularVector` are adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 1.3.22, Theorem 2.6.3 and Section 7.3.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991,
  Section 3.3.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section I.2
  (the singular value decomposition).
-/

public section

open Module Module.End

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A positive value `s` occurs among the singular values of `T` as many times as the dimension
of the `s²`-eigenspace of `T† T`. -/
theorem ncard_ofPred_singularValues_eq (T : E →ₗ[𝕜] F) {s : ℝ} (hs : 0 < s) :
    {i | T.singularValues i = s}.ncard =
      finrank 𝕜 (eigenspace (adjoint T ∘ₗ T) ((s ^ 2 : ℝ) : 𝕜)) := by
  have hT := T.isSymmetric_adjoint_comp_self
  have hset : {i | T.singularValues i = s} =
      Fin.val '' {k | (hT.eigenvalues rfl k : 𝕜) = ((s ^ 2 : ℝ) : 𝕜)} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_image, RCLike.ofReal_inj]
    constructor
    · intro hi
      have hlt : i < finrank 𝕜 E :=
        lt_of_not_ge fun h ↦ hs.ne' (hi ▸ T.singularValues_of_finrank_le h)
      exact ⟨⟨i, hlt⟩, by rw [← T.sq_singularValues_of_lt rfl hlt, hi], rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rwa [← T.sq_singularValues_fin rfl k, sq_eq_sq₀ (T.singularValues_nonneg _) hs.le] at hk
  rw [hset, Set.ncard_image_of_injective _ Fin.val_injective, ← hT.card_filter_eigenvalues_eq rfl,
    ← Set.ncard_coe_finset, Finset.coe_filter_univ]

/-- A linear map and its adjoint have the same singular values. -/
@[simp]
theorem singularValues_adjoint (A : E →ₗ[𝕜] F) :
    (adjoint A).singularValues = A.singularValues := by
  refine Finsupp.eq_of_antitone_of_ncard_eq (singularValues_antitone _)
    (singularValues_antitone _) fun s hs ↦ ?_
  rcases hs.lt_or_gt with hs | hs
  · have hempty (σ : ℕ →₀ ℝ) (hσ : ∀ i, 0 ≤ σ i) : {i | σ i = s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ (hσ i).not_gt (hi ▸ hs)
    rw [hempty _ (singularValues_nonneg _), hempty _ (singularValues_nonneg _)]
  · rw [ncard_ofPred_singularValues_eq _ hs, ncard_ofPred_singularValues_eq _ hs, adjoint_adjoint,
      finrank_eigenspace_comp_comm A (adjoint A) (by simpa using hs.ne')]

/-- The singular values of `A : E →ₗ[𝕜] F` vanish from the dimension of the target on. -/
theorem singularValues_of_finrank_le_right (A : E →ₗ[𝕜] F) {i : ℕ} (hi : finrank 𝕜 F ≤ i) :
    A.singularValues i = 0 := by
  rw [← singularValues_adjoint]
  exact (adjoint A).singularValues_of_finrank_le hi

/-- A sum `∑ᵢ f(σᵢ(A))` over the first `dim E` singular values is the `Finsupp` sum of `f` over
all singular values, provided `f 0 = 0`. -/
theorem sum_fin_singularValues {M : Type*} [AddCommMonoid M] (A : E →ₗ[𝕜] F) (f : ℝ → M)
    (hf : f 0 = 0) :
    ∑ i : Fin (finrank 𝕜 E), f (A.singularValues i) = A.singularValues.sum fun _ s ↦ f s := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ f (A.singularValues i)),
    Finsupp.sum_of_support_subset _ (A.support_singularValues ▸
      Finset.range_subset_range.mpr A.finrank_range_le) _ fun _ _ ↦ hf]

/-- The squared singular values of `A` are the sorted eigenvalues of the target Gram operator
`A A†`, at every index below the dimension of the target. -/
theorem sq_singularValues_eq_eigenvalues_self_comp_adjoint (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 F = n) {i : ℕ} (hin : i < n) :
    A.singularValues i ^ 2 = A.isSymmetric_self_comp_adjoint.eigenvalues hn ⟨i, hin⟩ := by
  simpa only [adjoint_adjoint, singularValues_adjoint] using
    (adjoint A).sq_singularValues_of_lt hn hin

/-- The sorted eigenvalues of the source Gram operator `A† A` and the target Gram operator `A A†`
agree at every index below both dimensions. -/
theorem eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint (A : E →ₗ[𝕜] F)
    {m n : ℕ} (hm : finrank 𝕜 E = m) (hn : finrank 𝕜 F = n) {i : ℕ} (him : i < m) (hin : i < n) :
    A.isSymmetric_adjoint_comp_self.eigenvalues hm ⟨i, him⟩ =
      A.isSymmetric_self_comp_adjoint.eigenvalues hn ⟨i, hin⟩ := by
  rw [← A.sq_singularValues_of_lt hm him, A.sq_singularValues_eq_eigenvalues_self_comp_adjoint]

/-- The sorted eigenvalues of the source Gram operator `A† A` vanish exactly from the rank of `A`
on. -/
theorem eigenvalues_adjoint_comp_self_eq_zero_iff (A : E →ₗ[𝕜] F) {m : ℕ}
    (hm : finrank 𝕜 E = m) {i : ℕ} (him : i < m) :
    A.isSymmetric_adjoint_comp_self.eigenvalues hm ⟨i, him⟩ = 0 ↔ finrank 𝕜 (range A) ≤ i := by
  rw [← A.sq_singularValues_of_lt hm him, sq_eq_zero_iff,
    singularValues_eq_zero_iff_le_finrank_range]

/-- The sorted eigenvalues of the target Gram operator `A A†` vanish exactly from the rank of `A`
on. -/
theorem eigenvalues_self_comp_adjoint_eq_zero_iff (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 F = n) {i : ℕ} (hin : i < n) :
    A.isSymmetric_self_comp_adjoint.eigenvalues hn ⟨i, hin⟩ = 0 ↔ finrank 𝕜 (range A) ≤ i := by
  rw [← A.sq_singularValues_eq_eigenvalues_self_comp_adjoint hn hin, sq_eq_zero_iff,
    singularValues_eq_zero_iff_le_finrank_range]

section SingularSystem

open InnerProductSpace

variable (A : E →ₗ[𝕜] F)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The squared singular values are nonincreasing, including the zero tail. -/
theorem sq_singularValues_antitone : Antitone fun i : ℕ ↦ A.singularValues i ^ 2 :=
  fun _ _ hij ↦ pow_le_pow_left₀ (A.singularValues_nonneg _)
    (A.singularValues_antitone hij) 2

/-- The **right singular basis** of `A`: the orthonormal eigenbasis `(vᵢ)` of the source Gram
operator `A† A`, ordered so that `A† A vᵢ = σᵢ² vᵢ` for the singular values
`σᵢ = A.singularValues i` of `A`, listed in nonincreasing order. -/
noncomputable def rightSingularBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- The right singular basis is Mathlib's ordered eigenbasis of `A† A`; this connects it to the
`LinearMap.IsSymmetric.eigenvectorBasis` API. -/
theorem rightSingularBasis_def :
    A.rightSingularBasis = A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl :=
  (rfl)

/-- The right singular vectors are eigenvectors of `A† A` for the squared singular values. -/
theorem adjoint_comp_self_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    (adjoint A ∘ₗ A) (A.rightSingularBasis i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularBasis i := by
  rw [A.sq_singularValues_fin rfl, rightSingularBasis_def]
  exact A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i

/-- Inner products of `A vᵢ` against the range of `A`: `⟪A vᵢ, A x⟫ = σᵢ² ⟪vᵢ, x⟫` for a right
singular vector `vᵢ`. -/
theorem inner_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) (x : E) :
    ⟪A (A.rightSingularBasis i), A x⟫ =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) * ⟪A.rightSingularBasis i, x⟫ := by
  rw [← adjoint_inner_left, ← comp_apply, adjoint_comp_self_rightSingularBasis, inner_smul_left,
    RCLike.conj_ofReal]

/-- `A` stretches the `i`-th right singular vector by the `i`-th singular value:
`‖A vᵢ‖ = σᵢ`. -/
@[simp]
theorem norm_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    ‖A (A.rightSingularBasis i)‖ = A.singularValues i := by
  have h := A.inner_apply_rightSingularBasis i (A.rightSingularBasis i)
  simp only [inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one, RCLike.ofReal_one,
    one_pow, mul_one] at h
  norm_cast at h
  exact (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg _)).mp h

/-- On a one-dimensional source, the singular values of `A` are `‖A x‖` for any unit vector `x`,
followed by zeros. -/
theorem singularValues_eq_single_of_finrank_eq_one (hE : finrank 𝕜 E = 1) {x : E}
    (hx : ‖x‖ = 1) : A.singularValues = Finsupp.single 0 ‖A x‖ := by
  ext i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h0 : 0 < finrank 𝕜 E := hE ▸ one_pos
    -- The right singular vector `v₀` is a unit multiple `c • x` of `x`.
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' x (norm_ne_zero_iff.mp (by simp [hx]))).mp
      hE (A.rightSingularBasis ⟨0, h0⟩)
    have hc1 : ‖c‖ = 1 := by
      simpa [← hc, norm_smul, hx] using A.rightSingularBasis.norm_eq_one ⟨0, h0⟩
    have h := A.norm_apply_rightSingularBasis ⟨0, h0⟩
    rw [Fin.val_mk, ← hc, map_smul, norm_smul, hc1, one_mul] at h
    rw [Finsupp.single_eq_same, h]
  · rw [Finsupp.single_eq_of_ne (by omega), A.singularValues_of_finrank_le (by omega)]

/-- A right singular vector lies in the kernel of `A` exactly when its singular value
vanishes. -/
@[simp]
theorem apply_rightSingularBasis_eq_zero_iff {i : Fin (finrank 𝕜 E)} :
    A (A.rightSingularBasis i) = 0 ↔ A.singularValues i = 0 := by
  rw [← norm_eq_zero, norm_apply_rightSingularBasis]

/-- On the span of the right singular vectors `vᵢ` with `i ≤ n`, `A` stretches every vector by at
least the `n`-th singular value: `σₙ ‖x‖ ≤ ‖A x‖`. -/
theorem singularValues_mul_norm_le_norm_apply {n : ℕ} {x : E}
    (hx : x ∈ A.rightSingularBasis.spanIndices {i | (i : ℕ) ≤ n}) :
    A.singularValues n * ‖x‖ ≤ ‖A x‖ := by
  have h := A.isSymmetric_adjoint_comp_self.le_re_inner_of_eigenbasis A.rightSingularBasis
    A.adjoint_comp_self_rightSingularBasis (c := A.singularValues n ^ 2)
    (fun i hi ↦ A.sq_singularValues_antitone hi) hx
  rw [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (mul_nonneg (A.singularValues_nonneg n) (norm_nonneg x))
    (norm_nonneg _) two_ne_zero).mp h

/-- An upper bound on the Gram eigenvalues of a selected span bounds the norm of `A` there. -/
theorem norm_apply_le_of_mem_spanIndices_of_adjoint_comp_self_eigenbasis
    (A : E →ₗ[𝕜] F) {m : ℕ} (e : OrthonormalBasis (Fin m) 𝕜 E) {μ : Fin m → ℝ}
    (he : ∀ i, (adjoint A ∘ₗ A) (e i) = (μ i : 𝕜) • e i)
    {s : Set (Fin m)} {c : ℝ} (hc : 0 ≤ c) (hμ : ∀ i ∈ s, μ i ≤ c ^ 2)
    {x : E} (hx : x ∈ e.spanIndices s) : ‖A x‖ ≤ c * ‖x‖ := by
  have h := A.isSymmetric_adjoint_comp_self.re_inner_le_of_eigenbasis e he hμ hx
  rw [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg hc (norm_nonneg x)) two_ne_zero).mp h

/-- A sorted orthonormal eigenbasis of the Gram operator computes the squared singular values. -/
theorem sq_singularValues_eq_of_adjoint_comp_self_eigenbasis (A : E →ₗ[𝕜] F) {m : ℕ}
    (e : OrthonormalBasis (Fin m) 𝕜 E) {μ : Fin m → ℝ} (hμ : Antitone μ)
    (he : ∀ i, (adjoint A ∘ₗ A) (e i) = (μ i : 𝕜) • e i) (k : Fin m) :
    A.singularValues k ^ 2 = μ k := by
  have hm : finrank 𝕜 E = m := by
    rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  rw [A.sq_singularValues_fin hm k,
    A.isSymmetric_adjoint_comp_self.eigenvalues_eq_of_eigenbasis hm e hμ he]

/-- On the span of the right singular vectors `vᵢ` with `n ≤ i`, `A` stretches every vector by at
most the `n`-th singular value: `‖A x‖ ≤ σₙ ‖x‖`. -/
theorem norm_apply_le_singularValues_mul_norm {n : ℕ} {x : E}
    (hx : x ∈ A.rightSingularBasis.spanIndices {i | n ≤ (i : ℕ)}) :
    ‖A x‖ ≤ A.singularValues n * ‖x‖ := by
  exact A.norm_apply_le_of_mem_spanIndices_of_adjoint_comp_self_eigenbasis
    A.rightSingularBasis A.adjoint_comp_self_rightSingularBasis (A.singularValues_nonneg n)
    (fun i hi ↦ A.sq_singularValues_antitone hi) hx

/-- A right singular vector with singular value zero lies in the kernel, so `A vᵢ` is fixed by
the scalar `σᵢ⁻² σᵢ²` (with total field inversion) even when `σᵢ = 0`. -/
theorem inv_mul_smul_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    (((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * ((A.singularValues i ^ 2 : ℝ) : 𝕜)) •
      A (A.rightSingularBasis i) = A (A.rightSingularBasis i) := by
  by_cases hc : A.singularValues i = 0
  · rw [(A.apply_rightSingularBasis_eq_zero_iff).mpr hc, smul_zero]
  · rw [inv_mul_cancel₀ (by simpa using hc), one_smul]

/-- The **left singular vectors** of `A`: `uᵢ = σᵢ⁻¹ A vᵢ` for the right singular basis `(vᵢ)`,
with total field inversion, so that `uᵢ = 0` when `σᵢ = 0`. The vectors with `σᵢ ≠ 0` form an
orthonormal family (`LinearMap.orthonormal_leftSingularVector`). -/
noncomputable def leftSingularVector (i : Fin (finrank 𝕜 E)) : F :=
  ((A.singularValues i : ℝ) : 𝕜)⁻¹ • A (A.rightSingularBasis i)

/-- Unfolds the left singular vector `uᵢ = σᵢ⁻¹ A vᵢ`. -/
theorem leftSingularVector_def (i : Fin (finrank 𝕜 E)) :
    A.leftSingularVector i = ((A.singularValues i : ℝ) : 𝕜)⁻¹ • A (A.rightSingularBasis i) :=
  (rfl)

/-- The singular relation `A vᵢ = σᵢ uᵢ`, valid at every index, including those with
`σᵢ = 0`. -/
theorem apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    A (A.rightSingularBasis i) = ((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i := by
  rw [leftSingularVector_def, smul_smul]
  by_cases hc : A.singularValues i = 0
  · rw [(A.apply_rightSingularBasis_eq_zero_iff).mpr hc, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using hc), one_smul]

/-- The left singular vectors are orthonormal up to the zero vectors at the vanishing singular
values: `⟪uᵢ, uⱼ⟫` is `1` if `i = j` and `σᵢ ≠ 0`, and `0` otherwise. -/
theorem inner_leftSingularVector (i j : Fin (finrank 𝕜 E)) :
    ⟪A.leftSingularVector i, A.leftSingularVector j⟫ =
      if i = j ∧ A.singularValues i ≠ 0 then 1 else 0 := by
  simp only [leftSingularVector_def, inner_smul_left, inner_smul_right,
    inner_apply_rightSingularBasis, orthonormal_iff_ite.mp (A.rightSingularBasis).orthonormal]
  rcases eq_or_ne i j with rfl | hij
  · by_cases hc : A.singularValues i = 0
    · simp [hc]
    · have hc' : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := by simpa using hc
      simp [hc]
      field_simp [hc']
  · simp [hij]

/-- The left singular vectors with nonzero singular value form an orthonormal family. -/
theorem orthonormal_leftSingularVector :
    Orthonormal 𝕜 fun i : {i : Fin (finrank 𝕜 E) // A.singularValues i ≠ 0} ↦
      A.leftSingularVector i := by
  classical
  refine orthonormal_iff_ite.mpr fun i j ↦ ?_
  simp [inner_leftSingularVector, i.2, Subtype.ext_iff]

/-- A left singular vector vanishes exactly when its singular value does. -/
@[simp]
theorem leftSingularVector_eq_zero_iff {i : Fin (finrank 𝕜 E)} :
    A.leftSingularVector i = 0 ↔ A.singularValues i = 0 := by
  rw [← inner_self_eq_zero (𝕜 := 𝕜), inner_leftSingularVector]
  simp

/-- A left singular vector has norm at most one: it is a unit vector when its singular value is
nonzero and zero otherwise. -/
theorem norm_leftSingularVector_le_one (i : Fin (finrank 𝕜 E)) : ‖A.leftSingularVector i‖ ≤ 1 := by
  by_cases hσ : A.singularValues i = 0
  · simp [(A.leftSingularVector_eq_zero_iff).mpr hσ]
  · exact (A.orthonormal_leftSingularVector.1 ⟨i, hσ⟩).le

/-- **Bessel's inequality** for the left singular vectors: `∑ᵢ ‖⟪uᵢ, x⟫‖² ≤ ‖x‖²`. The vectors at
the vanishing singular values are zero, so the orthonormal subfamily carries the whole sum. -/
theorem sum_norm_inner_leftSingularVector_sq_le (x : F) :
    ∑ i, ‖⟪A.leftSingularVector i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  calc ∑ i, ‖⟪A.leftSingularVector i, x⟫‖ ^ 2
      = ∑ i : {i : Fin (finrank 𝕜 E) // A.singularValues i ≠ 0},
          ‖⟪A.leftSingularVector i, x⟫‖ ^ 2 := by
        rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun i ↦ A.singularValues i ≠ 0)
          (f := fun i ↦ ‖⟪A.leftSingularVector i, x⟫‖ ^ 2) fun i _ h hσ ↦ h (by
            simp [(A.leftSingularVector_eq_zero_iff).mpr hσ])]
        exact Finset.sum_subtype _ (by simp) _
    _ ≤ ‖x‖ ^ 2 := A.orthonormal_leftSingularVector.sum_inner_products_le x

/-- The adjoint singular relation `A† uᵢ = σᵢ vᵢ`, valid at every index, including those with
`σᵢ = 0`. -/
@[simp]
theorem adjoint_leftSingularVector (i : Fin (finrank 𝕜 E)) :
    adjoint A (A.leftSingularVector i) =
      ((A.singularValues i : ℝ) : 𝕜) • A.rightSingularBasis i := by
  rw [leftSingularVector_def, map_smul, ← comp_apply, adjoint_comp_self_rightSingularBasis]
  simp [smul_smul, sq, ← mul_assoc]

/-- The eigenvalue equation `A A† uᵢ = σᵢ² uᵢ` for the target Gram operator, at every index.
When `σᵢ ≠ 0`, `uᵢ` is an eigenvector of `A A†` for `σᵢ²`; when `σᵢ = 0`, `uᵢ = 0`. -/
theorem self_comp_adjoint_leftSingularVector (i : Fin (finrank 𝕜 E)) :
    (A ∘ₗ adjoint A) (A.leftSingularVector i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.leftSingularVector i := by
  simp [adjoint_leftSingularVector, apply_rightSingularBasis, smul_smul, sq]

/-- The **singular expansion** of a vector: `A x = ∑ᵢ σᵢ ⟪vᵢ, x⟫ uᵢ`. -/
theorem apply_eq_sum_singularValues_smul (x : E) :
    A x = ∑ i : Fin (finrank 𝕜 E), ((A.singularValues i : ℝ) : 𝕜) • ⟪A.rightSingularBasis i, x⟫ •
      A.leftSingularVector i := by
  conv_lhs => rw [← (A.rightSingularBasis).sum_repr' x]
  simp only [map_sum, map_smul, apply_rightSingularBasis]
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- The **singular value decomposition** in rank-one form: `A = ∑ᵢ σᵢ uᵢ ⊗ vᵢ`, where
`u ⊗ v` is the rank-one map `x ↦ ⟪v, x⟫ u`. -/
theorem eq_sum_singularValues_smul_rankOne :
    A = ∑ i : Fin (finrank 𝕜 E), ((A.singularValues i : ℝ) : 𝕜) •
      (rankOne 𝕜 (A.leftSingularVector i) (A.rightSingularBasis i)).toLinearMap := by
  ext x
  simp [A.apply_eq_sum_singularValues_smul x]

/-- The left singular vectors with nonzero singular value extend to an orthonormal basis of the
codomain, indexed compatibly with the right singular basis: there is an orthonormal basis `(wⱼ)`
of `F` with `wᵢ = uᵢ` whenever `σᵢ ≠ 0`. Together with `LinearMap.apply_rightSingularBasis`
this gives `A vᵢ = σᵢ wᵢ` at every index below both dimensions. -/
theorem exists_orthonormalBasis_apply_eq_leftSingularVector :
    ∃ w : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F, ∀ (i : Fin (finrank 𝕜 E))
      (j : Fin (finrank 𝕜 F)), (i : ℕ) = j → A.singularValues i ≠ 0 →
        w j = A.leftSingularVector i := by
  -- Reindex the left singular vectors by `Fin (finrank 𝕜 F)`, padding with zero, and extend the
  -- orthonormal subfamily at the nonzero singular values.
  have hlt {j : ℕ} (hj : A.singularValues j ≠ 0) : j < finrank 𝕜 E :=
    lt_of_not_ge fun h ↦ hj (A.singularValues_of_finrank_le h)
  let u : Fin (finrank 𝕜 F) → F := fun j ↦
    if h : (j : ℕ) < finrank 𝕜 E then A.leftSingularVector ⟨j, h⟩ else 0
  let s : Set (Fin (finrank 𝕜 F)) := {j | A.singularValues j ≠ 0}
  have hu : s.domRestrict u = (fun i : {i : Fin (finrank 𝕜 E) // A.singularValues i ≠ 0} ↦
      A.leftSingularVector i) ∘ fun j ↦ ⟨⟨j.1, hlt j.2⟩, j.2⟩ := by
    ext j
    simp [u, hlt j.2]
  have hs : Orthonormal 𝕜 (s.domRestrict u) := by
    rw [hu]
    exact A.orthonormal_leftSingularVector.comp _ fun j k h ↦ by
      simpa [Subtype.ext_iff, Fin.ext_iff] using h
  obtain ⟨w, hw⟩ := hs.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨w, fun i j hij hi ↦ ?_⟩
  have hj : j ∈ s := by simpa [s, ← hij] using hi
  rw [hw j hj]
  simp [u, ← hij]

end SingularSystem

section Comparison

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- If `‖B x‖ ≤ c * ‖A x‖` for every `x`, then every singular value of `B` is at most `c` times the
corresponding singular value of `A`. -/
theorem singularValues_le_mul_of_norm_apply_le {A : E →ₗ[𝕜] F} {B : E →ₗ[𝕜] G} {c : ℝ}
    (h : ∀ x, ‖B x‖ ≤ c * ‖A x‖) (i : ℕ) :
    B.singularValues i ≤ c * A.singularValues i := by
  rcases lt_or_ge c 0 with hc | hc
  · -- A negative constant forces `A = 0` and `B = 0`.
    have hA : A = 0 := ext fun x ↦ norm_le_zero_iff.mp <|
      nonpos_of_mul_nonneg_right ((norm_nonneg _).trans (h x)) hc
    have hB : B = 0 := ext fun x ↦ norm_le_zero_iff.mp <| by simpa [hA] using h x
    simp [hA, hB]
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  swap
  · simp [B.singularValues_of_finrank_le hi, A.singularValues_of_finrank_le hi]
  -- Courant–Fischer: on an `(i + 1)`-dimensional subspace where the Rayleigh quotient of `B† B` is
  -- at least `σᵢ(B)²`, find a unit vector where that of `A† A` is at most `σᵢ(A)²`.
  obtain ⟨V, hV, hBV⟩ :=
    B.isSymmetric_adjoint_comp_self.exists_submodule_forall_unit_eigenvalue_le_re_inner rfl ⟨i, hi⟩
  obtain ⟨x, hxV, hx, hAx⟩ :=
    A.isSymmetric_adjoint_comp_self.exists_unit_vector_re_inner_le_eigenvalue rfl ⟨i, hi⟩ V hV
  have hBx := hBV x hxV hx
  simp only [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq] at hAx hBx
  have hsq : B.singularValues i ^ 2 ≤ (c * A.singularValues i) ^ 2 := by
    rw [mul_pow, B.sq_singularValues_of_lt rfl hi, A.sq_singularValues_of_lt rfl hi]
    calc _ ≤ ‖B x‖ ^ 2 := hBx
      _ ≤ (c * ‖A x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h x) 2
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hAx (sq_nonneg c)
  exact (pow_le_pow_iff_left₀ (B.singularValues_nonneg i)
    (mul_nonneg hc (A.singularValues_nonneg i)) two_ne_zero).mp hsq

/-- **Bounded-factor domination.** If `‖C y‖ ≤ c * ‖y‖` for every `y` (for `c ≥ 0`: if `C` has
operator norm at most `c`), then `σᵢ(C A) ≤ c σᵢ(A)` for every `i`. -/
theorem singularValues_comp_le (C : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) {c : ℝ}
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) (i : ℕ) :
    (C ∘ₗ A).singularValues i ≤ c * A.singularValues i :=
  singularValues_le_mul_of_norm_apply_le (fun x ↦ hC (A x)) i

/-- If `‖A x‖ ≤ c * ‖x‖` for every `x` (for `c ≥ 0`: if `A` has operator norm at most `c`), then
every singular value of `A` is at most `c`. -/
theorem singularValues_le_of_norm_apply_le {A : E →ₗ[𝕜] F} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖A x‖ ≤ c * ‖x‖) (i : ℕ) : A.singularValues i ≤ c := by
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  · simpa [norm_apply_rightSingularBasis] using h (A.rightSingularBasis ⟨i, hi⟩)
  · rw [A.singularValues_of_finrank_le hi]
    exact hc

/-- Two maps with the same source and `‖B x‖ = ‖A x‖` for every `x` have the same singular
values. -/
theorem singularValues_eq_of_norm_apply_eq {A : E →ₗ[𝕜] F} {B : E →ₗ[𝕜] G}
    (h : ∀ x, ‖B x‖ = ‖A x‖) : B.singularValues = A.singularValues := by
  ext i
  exact le_antisymm
    (by simpa using singularValues_le_mul_of_norm_apply_le (c := 1) (by simp [h]) i)
    (by simpa using singularValues_le_mul_of_norm_apply_le (c := 1) (by simp [h]) i)

/-- The modulus `|A| = √(A† A)` of a map has the same singular values as the map itself. -/
@[simp]
theorem singularValues_operatorAbs (A : E →ₗ[𝕜] F) :
    A.operatorAbs.singularValues = A.singularValues :=
  singularValues_eq_of_norm_apply_eq A.norm_operatorAbs_apply

/-- Composing on the left with a linear isometry leaves the singular values unchanged. -/
@[simp]
theorem singularValues_linearIsometry_comp (W : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    (W.toLinearMap ∘ₗ A).singularValues = A.singularValues :=
  singularValues_eq_of_norm_apply_eq fun x ↦ by simp

/-- Composing on the right with the adjoint of a linear isometry leaves the singular values
unchanged. -/
@[simp]
theorem singularValues_comp_adjoint_linearIsometry (A : E →ₗ[𝕜] F) (W : E →ₗᵢ[𝕜] G) :
    (A ∘ₗ adjoint W.toLinearMap).singularValues = A.singularValues := by
  rw [← singularValues_adjoint, adjoint_comp, adjoint_adjoint, singularValues_linearIsometry_comp,
    singularValues_adjoint]

/-- Composing on the left with an isometric isomorphism leaves the singular values unchanged. -/
@[simp]
theorem singularValues_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    ((U : F →ₗ[𝕜] G) ∘ₗ A).singularValues = A.singularValues :=
  singularValues_linearIsometry_comp U.toLinearIsometry A

/-- Composing on the right with an isometric isomorphism leaves the singular values unchanged. -/
@[simp]
theorem singularValues_comp_linearIsometryEquiv (A : E →ₗ[𝕜] F) (V : G ≃ₗᵢ[𝕜] E) :
    (A ∘ₗ (V : G →ₗ[𝕜] E)).singularValues = A.singularValues := by
  rw [← singularValues_adjoint, adjoint_comp, V.adjoint_coe_eq_symm,
    singularValues_linearIsometryEquiv_comp, singularValues_adjoint]

/-- Scaling a map by `c` scales its singular values by `‖c‖`. -/
@[simp]
theorem singularValues_smul (c : 𝕜) (A : E →ₗ[𝕜] F) :
    (c • A).singularValues = ‖c‖ • A.singularValues := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  ext i
  rw [Finsupp.smul_apply, smul_eq_mul]
  refine le_antisymm (singularValues_le_mul_of_norm_apply_le (fun x ↦ by simp [norm_smul]) i) ?_
  have h := singularValues_le_mul_of_norm_apply_le (A := c • A) (B := A) (c := ‖c‖⁻¹)
    (fun x ↦ by simp [norm_smul, inv_mul_cancel_left₀ hc'.ne']) i
  rwa [le_inv_mul_iff₀ hc'] at h

end Comparison

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional 𝕜 E] in
/-- The diagonal operator of an orthonormal basis `(eᵢ)` with entries `(dᵢ)` has `eᵢ` as an
eigenvector with eigenvalue `dᵢ`. -/
@[simp]
theorem _root_.Matrix.toLin_diagonal_apply_self (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜)
    (i : ι) : Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d) (e i) = d i • e i := by
  simpa using (hasEigenvector_toLin_diagonal d i e.toBasis).apply_eq_smul

omit [FiniteDimensional 𝕜 E] in
/-- The Gram operator of a diagonal map has eigenvalues equal to the squared diagonal norms. -/
@[simp]
theorem _root_.Matrix.adjoint_comp_self_toLin_diagonal_apply
    (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜) (i : ι) :
    let := Module.Finite.of_basis e.toBasis
    let D := Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
    (adjoint D ∘ₗ D) (e i) = ((‖d i‖ ^ 2 : ℝ) : 𝕜) • e i := by
  let := Module.Finite.of_basis e.toBasis
  have hDadj : adjoint (Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)) =
      Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal (star d)) := by
    rw [← Matrix.toLin_conjTranspose, Matrix.diagonal_conjTranspose]
  simp [hDadj, smul_smul, RCLike.mul_conj]

omit [FiniteDimensional 𝕜 E] in
/-- Reindexing a diagonal basis preserves the Gram eigenvector equations, with the squared
diagonal norms reindexed by the same equivalence. -/
theorem _root_.OrthonormalBasis.adjoint_comp_self_toLin_diagonal_reindex_apply
    (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜) {κ : Type*} [Fintype κ]
    (π : κ ≃ ι) (i : κ) :
    let := Module.Finite.of_basis e.toBasis
    let D := Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
    (adjoint D ∘ₗ D) ((e.reindex π.symm) i) =
      ((‖d (π i)‖ ^ 2 : ℝ) : 𝕜) • (e.reindex π.symm) i := by
  simpa only [OrthonormalBasis.reindex_apply, Equiv.symm_symm] using
    Matrix.adjoint_comp_self_toLin_diagonal_apply e d (π i)

/-- **Singular values of a diagonal operator.** If `π` lists the indices so that the norms
`‖d (π k)‖` are nonincreasing, then the `k`-th singular value of the diagonal operator with entries
`d` in an orthonormal basis is `‖d (π k)‖`. The singular values from `Fintype.card ι` on vanish
(`LinearMap.singularValues_of_finrank_le`). -/
theorem _root_.Matrix.singularValues_toLin_diagonal (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜)
    {n : ℕ} (π : Fin n ≃ ι) (hπ : Antitone fun k ↦ ‖d (π k)‖) (k : Fin n) :
    (Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)).singularValues k = ‖d (π k)‖ := by
  set D := Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
  rw [← sq_eq_sq₀ (D.singularValues_nonneg _) (norm_nonneg _)]
  exact D.sq_singularValues_eq_of_adjoint_comp_self_eigenbasis (e.reindex π.symm)
    (fun i j hij ↦ pow_le_pow_left₀ (norm_nonneg _) (hπ hij) 2)
    (e.adjoint_comp_self_toLin_diagonal_reindex_apply d π) k

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The rectangular diagonal map with entries `d` in orthonormal bases `(eᵢ)_{i < m}` and
`(fⱼ)_{j < n}` sends `eᵢ` to `dᵢ fᵢ` when `i < n`, and to `0` otherwise. -/
theorem _root_.Matrix.toLin_of_ite_val_eq_apply {m n : ℕ} (e : OrthonormalBasis (Fin m) 𝕜 E)
    (f : OrthonormalBasis (Fin n) 𝕜 F) (d : ℕ → 𝕜) (i : Fin m) :
    Matrix.toLin e.toBasis f.toBasis (Matrix.of fun (j : Fin n) (i : Fin m) ↦
      if (j : ℕ) = i then d i else 0) (e i) =
      if h : (i : ℕ) < n then d i • f ⟨i, h⟩ else 0 := by
  rw [← e.coe_toBasis, Matrix.toLin_self]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩ (fun j _ hj ↦ by
      simp [show (j : ℕ) ≠ i from fun h' ↦ hj (Fin.ext h')]) (by simp)]
    simp
  · refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [show (j : ℕ) ≠ i from fun h' ↦ h (h' ▸ j.isLt)]

/-- **Rectangular singular-value factorization.** Every linear map `A : E →ₗ[𝕜] F` between
finite-dimensional inner product spaces factors as `A = U D V`, where `U` and `V` are linear
isometric equivalences of `F` and `E`, and `D` is the rectangular diagonal map whose matrix in
prescribed orthonormal bases `(eᵢ)` of `E` and `(fⱼ)` of `F` has the singular values of `A` on its
diagonal: `D eᵢ = σᵢ fᵢ` when `i` is also an index of `(fⱼ)`, and `D eᵢ = 0` otherwise. -/
theorem exists_linearIsometryEquiv_eq_comp_toLin_comp (A : E →ₗ[𝕜] F) {m n : ℕ}
    (e : OrthonormalBasis (Fin m) 𝕜 E) (f : OrthonormalBasis (Fin n) 𝕜 F) :
    ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), A = (U : F →ₗ[𝕜] F) ∘ₗ
      Matrix.toLin e.toBasis f.toBasis
        (Matrix.of fun j i ↦ if (j : ℕ) = i then (A.singularValues i : 𝕜) else 0) ∘ₗ
        (V : E →ₗ[𝕜] E) := by
  have hm : finrank 𝕜 E = m := by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  have hn : finrank 𝕜 F = n := by rw [finrank_eq_card_basis f.toBasis, Fintype.card_fin]
  subst hm hn
  -- `V` sends the right singular basis `(vᵢ)` to `(eᵢ)`, and `U` sends `(fⱼ)` to an orthonormal
  -- basis `(wⱼ)` extending the left singular vectors, so both sides send `vᵢ` to `σᵢ wᵢ`, read
  -- as `0` when `i` is not an index of `(wⱼ)`.
  obtain ⟨w, hw⟩ := A.exists_orthonormalBasis_apply_eq_leftSingularVector
  refine ⟨f.equiv w (.refl _), A.rightSingularBasis.equiv e (.refl _), ?_⟩
  refine A.rightSingularBasis.toBasis.ext fun i ↦ ?_
  simp only [coe_comp, Function.comp_apply, OrthonormalBasis.coe_toBasis, apply_rightSingularBasis,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, OrthonormalBasis.equiv_apply_basis,
    Equiv.refl_apply]
  rw [Matrix.toLin_of_ite_val_eq_apply (d := fun i ↦ (A.singularValues i : 𝕜))]
  split_ifs with hi
  · rcases eq_or_ne (A.singularValues i) 0 with hσ | hσ
    · simp [hσ]
    · simp [hw i ⟨i, hi⟩ rfl hσ]
  · simp [A.singularValues_of_finrank_le_right (not_lt.mp hi)]

/-- **Singular-value diagonal factorization.** Every endomorphism `A` of a finite-dimensional
inner product space factors as `A = U D V`, where `U` and `V` are linear isometric equivalences
and `D` is the diagonal operator whose entries in a prescribed orthonormal basis `(eᵢ)` are the
singular values of `A`. -/
theorem exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp (A : E →ₗ[𝕜] E) {n : ℕ}
    (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∃ U V : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ
      Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal fun i ↦ (A.singularValues i : 𝕜)) ∘ₗ
        (V : E →ₗ[𝕜] E) := by
  have hD : (Matrix.diagonal fun i : Fin n ↦ (A.singularValues i : 𝕜)) =
      Matrix.of fun j i : Fin n ↦ if (j : ℕ) = i then (A.singularValues i : 𝕜) else 0 := by
    ext j i
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [h, Fin.val_ne_of_ne h]
  rw [hD]
  exact A.exists_linearIsometryEquiv_eq_comp_toLin_comp e e

/-- **Compact singular value decomposition.** With `p = min (dim E) (dim F)`, every map
`A : E →ₗ[𝕜] F` is `∑_{i < p} σᵢ wᵢ ⊗ vᵢ` for orthonormal families `(vᵢ)` in `E` and `(wᵢ)` in
`F`, where `u ⊗ v` is the rank-one map `x ↦ ⟪v, x⟫ u`. Unlike
`LinearMap.eq_sum_singularValues_smul_rankOne`, both families are orthonormal, including at the
indices where `σᵢ = 0`. -/
theorem exists_orthonormal_eq_sum_singularValues_smul_rankOne (A : E →ₗ[𝕜] F) :
    ∃ (v : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → E)
      (w : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → F), Orthonormal 𝕜 v ∧ Orthonormal 𝕜 w ∧
        A = ∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)), ((A.singularValues i : ℝ) : 𝕜) •
          (InnerProductSpace.rankOne 𝕜 (w i) (v i)).toLinearMap := by
  let e := stdOrthonormalBasis 𝕜 E
  let f := stdOrthonormalBasis 𝕜 F
  obtain ⟨U, V, hA⟩ := A.exists_linearIsometryEquiv_eq_comp_toLin_comp e f
  let iE : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → Fin (finrank 𝕜 E) :=
    Fin.castLE (min_le_left _ _)
  let iF : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → Fin (finrank 𝕜 F) :=
    Fin.castLE (min_le_right _ _)
  refine ⟨V.symm ∘ e ∘ iE, U ∘ f ∘ iF,
    (e.orthonormal.comp _ (Fin.castLE_injective _)).comp_linearIsometryEquiv _,
    (f.orthonormal.comp _ (Fin.castLE_injective _)).comp_linearIsometryEquiv _, ?_⟩
  -- Compare both sides on the orthonormal basis `(V⁻¹ eₖ)`: each sends `V⁻¹ eₖ` to `σₖ U fₖ`,
  -- read as `0` when `k` is not an index of `(fⱼ)`.
  refine (e.map V.symm).toBasis.ext fun k ↦ ?_
  conv_lhs => rw [hA]
  simp only [OrthonormalBasis.toBasis_map, LinearIsometryEquiv.toLinearEquiv_symm,
    Basis.map_apply, OrthonormalBasis.coe_toBasis, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    coe_comp, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
    LinearIsometryEquiv.apply_symm_apply, coe_sum, coe_smul, ContinuousLinearMap.coe_coe,
    Finset.sum_apply, Pi.smul_apply, InnerProductSpace.rankOne_apply,
    LinearIsometryEquiv.inner_map_map, orthonormal_iff_ite.mp e.orthonormal, ite_smul, one_smul,
    zero_smul, smul_ite, smul_zero]
  rw [Matrix.toLin_of_ite_val_eq_apply (d := fun i ↦ (A.singularValues i : 𝕜))]
  have hiE (i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F))) : iE i = k ↔ (i : ℕ) = k := Fin.ext_iff
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k, lt_min k.2 hk⟩
      (fun i _ hi ↦ by simp [hiE, show (i : ℕ) ≠ k from fun h ↦ hi (Fin.ext h)]) (by simp)]
    simp [hiE, iF, f]
  · rw [Finset.sum_eq_zero fun i _ ↦ by
      simp [hiE, show (i : ℕ) ≠ k from fun h ↦ hk (h ▸ i.2.trans_le (min_le_right _ _))]]
    simp

end Diagonal

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- For a sorted orthonormal eigenbasis of `T† T`, the norm on the orthogonal complement
of its first `n` vectors is at most the `n`-th singular value, including the zero tail. -/
theorem norm_comp_orthogonal_spanIndices_le_of_adjoint_comp_self_eigenbasis
    (T : E →L[𝕜] F) {m : ℕ} (e : OrthonormalBasis (Fin m) 𝕜 E) {μ : Fin m → ℝ}
    (hμ : Antitone μ)
    (he : ∀ i, (LinearMap.adjoint (T : E →ₗ[𝕜] F) ∘ₗ (T : E →ₗ[𝕜] F)) (e i) =
      (μ i : 𝕜) • e i) (n : ℕ) :
    ‖T ∘L (e.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m)))ᗮ.subtypeL‖ ≤
      (T : E →ₗ[𝕜] F).singularValues n := by
  let A : E →ₗ[𝕜] F := T
  refine opNorm_le_bound _ (A.singularValues_nonneg n) fun x ↦ ?_
  have hx := e.mem_spanIndices_le_of_mem_orthogonal x.2
  by_cases hn : n < m
  · exact A.norm_apply_le_of_mem_spanIndices_of_adjoint_comp_self_eigenbasis e he
      (A.singularValues_nonneg n) (fun i hi ↦ by
        rw [A.sq_singularValues_eq_of_adjoint_comp_self_eigenbasis e hμ he ⟨n, hn⟩]
        exact hμ hi) hx
  · have htail : {i : Fin m | n ≤ (i : ℕ)} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (i.2.trans_le (le_of_not_gt hn))
    have hx0 : (x : E) = 0 := by
      simpa only [htail, e.spanIndices_eq_span, Set.image_empty, Submodule.span_empty,
        Submodule.mem_bot] using hx
    simp [hx0]

section RangeProjection

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- For an isometry `X`, an operator `T` has the same singular values after the projection onto
`range X` as after `X` itself: `T P_{range X} = (T X) X†` and `X†` is the adjoint of an isometry. -/
theorem singularValues_comp_starProjection_range {X : F →L[𝕜] E}
    (hX : Isometry X) (T : E →L[𝕜] G) :
    ((T ∘L X.range.starProjection : E →L[𝕜] G) : E →ₗ[𝕜] G).singularValues =
      ((T ∘L X : F →L[𝕜] G) : F →ₗ[𝕜] G).singularValues := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  let W : F →ₗᵢ[𝕜] E := ⟨X, AddMonoidHomClass.isometry_iff_norm _ |>.1 hX⟩
  -- The linear map underlying `W` is `X` by construction.
  have hW : W.toLinearMap = X := rfl
  rw [← comp_adjoint_eq_starProjection_range hX, ← comp_assoc, toLinearMap_comp,
    ← adjoint_toLinearMap, ← hW, LinearMap.singularValues_comp_adjoint_linearIsometry]

end RangeProjection

end ContinuousLinearMap
end
end TAF_LiteralSource_0375

section TAF_LiteralSource_0376
/- Original module: TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Unitarily invariant seminorms on rectangular linear maps

A seminorm `N` on the linear maps `E →ₗ[𝕜] F` between two inner product spaces is *unitarily
invariant* when `N (U A V) = N A` for all unitaries `U` of `F` and `V` of `E`, acting
independently on the target and the source. Square operators are the case `E = F`. Unitaries are
represented as linear isometric equivalences `F ≃ₗᵢ[𝕜] F` and `E ≃ₗᵢ[𝕜] E`. The structure
itself assumes neither finite-dimensionality nor boundedness: it is a seminorm on all algebraic
linear maps `E →ₗ[𝕜] F`.

When `E` and `F` are finite-dimensional, the operator norm, the Frobenius norm, the Ky Fan norms
and the nuclear norm are the standard examples; they are constructed in the neighbouring files
`OpNorm`, `Frobenius` and `KyFan` of this directory.

This file sets up the structure together with the elementary vocabulary for comparing its
values:

* the two-sided unitary orbit `U C V` of a map `C`, on which every unitarily invariant seminorm
  is constant; when `E` and `F` are finite-dimensional, the orbit of `C` consists exactly of the
  maps with the same singular values as `C`, so a unitarily invariant seminorm depends only on the
  singular values of its argument;
* the convex hull of the two-sided unitary orbit, on which every unitarily invariant seminorm is
  bounded by its value at `C`;
* finite orbit certificates, which write `X` as a combination `∑ᵢ aᵢ • Uᵢ C Vᵢ` of points of the
  orbit of `C`, and bound `N X` by the coefficient mass `∑ᵢ ‖aᵢ‖` times `N C`;
* transport of a unitarily invariant seminorm along isometric isomorphisms of the source and the
  target, and, for finite-dimensional `E` and `F`, to the adjoint maps;
* invariance under replacing an endomorphism `A` by its operator modulus `|A| = √(A† A)`, which
  has the same singular values as `A`.

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm`: seminorms on `E →ₗ[𝕜] F` invariant under unitaries of
  the source and of the target.
* `LinearMap.twoSidedUnitaryOrbit`: the set of maps `U C V` with `U`, `V` unitary.
* `LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq`: two maps lie in the same orbit
  exactly when they have the same singular values.
* `TauCeti.UnitarilyInvariantSeminorm.map_eq_of_singularValues_eq`: a unitarily invariant
  seminorm is determined by the singular values of its argument.
* `LinearMap.twoSidedUnitaryOrbitHull`: the convex combinations of points of the orbit;
  `LinearMap.twoSidedUnitaryOrbitHull_eq_convexHull` identifies it with `convexHull ℝ` of the orbit
  whenever the latter makes sense.
* `LinearMap.twoSidedUnitaryOrbitHull_subset`: the orbit hull is the smallest set containing the
  orbit and closed under convex combinations.
* `TauCeti.UnitaryOrbitCertificate`: a representation `X = ∑ᵢ aᵢ • Uᵢ C Vᵢ`, with its
  coefficient mass `TauCeti.UnitaryOrbitCertificate.mass`.
* `TauCeti.UnitaryOrbitCertificate.apply_le_mass_mul`: `N X ≤ mass * N C`.
* `TauCeti.UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull`: points of
  the orbit hull have certificates of mass one, so
  `TauCeti.UnitarilyInvariantSeminorm.map_le_of_mem_twoSidedUnitaryOrbitHull`: `N X ≤ N C` on the
  hull.
* `TauCeti.UnitarilyInvariantSeminorm.arrowCongr`: transport along isometric isomorphisms of the
  source and the target.
* `TauCeti.UnitarilyInvariantSeminorm.compAdjoint`: the seminorm `B ↦ N B†` on the adjoint maps.
* `TauCeti.UnitarilyInvariantSeminorm.map_operatorAbs`: on endomorphisms, `N |A| = N A` for the
  operator modulus `|A| = √(A† A)`.

## Source

The structure `UnitarilyInvariantSeminorm`, the two-sided unitary orbit and the finite orbit
certificates are adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Basic.lean`).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. Oxford
  Ser. (2) **11** (1960), 50–59.
-/

public section

open Module

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F']
  [InnerProductSpace 𝕜 F']

namespace LinearMap

/-- The **two-sided unitary orbit** of `C : E →ₗ[𝕜] F`: the maps `U ∘ C ∘ V` for unitaries `U`
of the target and `V` of the source. -/
def twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {X | ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) = X}

theorem mem_twoSidedUnitaryOrbit {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbit ↔
      ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) = X :=
  Iff.rfl

theorem linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) ∈ C.twoSidedUnitaryOrbit :=
  ⟨U, V, rfl⟩

@[simp]
theorem self_mem_twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : C ∈ C.twoSidedUnitaryOrbit :=
  ⟨.refl 𝕜 F, .refl 𝕜 E, rfl⟩

/-- Two-sided unitary orbits are equivalence classes: the orbit of any of its points is the whole
orbit. -/
theorem twoSidedUnitaryOrbit_eq_of_mem {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.twoSidedUnitaryOrbit = C.twoSidedUnitaryOrbit := by
  obtain ⟨U, V, rfl⟩ := h
  ext Y
  constructor
  · rintro ⟨U', V', rfl⟩
    exact ⟨U.trans U', V'.trans V, by ext; simp⟩
  · rintro ⟨U', V', rfl⟩
    exact ⟨U.symm.trans U', V'.trans V.symm, by ext; simp⟩

/-- Maps in the same two-sided unitary orbit have the same singular values. -/
theorem singularValues_eq_of_mem_twoSidedUnitaryOrbit [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.singularValues = C.singularValues := by
  obtain ⟨U, V, rfl⟩ := h
  simp

/-- **Determination of the orbit by singular values.** Two maps between finite-dimensional inner
product spaces lie in the same two-sided unitary orbit exactly when they have the same singular
values. -/
theorem mem_twoSidedUnitaryOrbit_iff_singularValues_eq [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbit ↔ X.singularValues = C.singularValues := by
  refine ⟨singularValues_eq_of_mem_twoSidedUnitaryOrbit, fun h ↦ ?_⟩
  -- Both maps are unitary multiples of the same rectangular diagonal map.
  obtain ⟨U, V, hC⟩ := C.exists_linearIsometryEquiv_eq_comp_toLin_comp
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 F)
  obtain ⟨U', V', hX⟩ := X.exists_linearIsometryEquiv_eq_comp_toLin_comp
    (stdOrthonormalBasis 𝕜 E) (stdOrthonormalBasis 𝕜 F)
  rw [h] at hX
  refine ⟨U.symm.trans U', V'.trans V.symm, ?_⟩
  conv_lhs => rw [hC]
  rw [hX]
  ext x
  simp

/-! ### The convex hull of the two-sided unitary orbit -/

/-- The **convex hull of the two-sided unitary orbit** of `C`: the convex combinations
`∑ᵢ tᵢ • Xᵢ` of maps `Xᵢ` in the two-sided unitary orbit of `C`, with real weights `tᵢ ≥ 0`
summing to `1`. The weights act through `ℝ → 𝕜`: for a general `RCLike` field `𝕜` the space
`E →ₗ[𝕜] F` carries no `ℝ`-module instance to which `convexHull ℝ` could be applied. -/
def twoSidedUnitaryOrbitHull (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {X | ∃ (n : ℕ) (t : Fin n → ℝ) (Y : Fin n → E →ₗ[𝕜] F), (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
    (∀ i, Y i ∈ C.twoSidedUnitaryOrbit) ∧ ∑ i, (t i : 𝕜) • Y i = X}

theorem mem_twoSidedUnitaryOrbitHull {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbitHull ↔
      ∃ (n : ℕ) (t : Fin n → ℝ) (Y : Fin n → E →ₗ[𝕜] F), (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧
        (∀ i, Y i ∈ C.twoSidedUnitaryOrbit) ∧ ∑ i, (t i : 𝕜) • Y i = X :=
  Iff.rfl

theorem twoSidedUnitaryOrbit_subset_twoSidedUnitaryOrbitHull (C : E →ₗ[𝕜] F) :
    C.twoSidedUnitaryOrbit ⊆ C.twoSidedUnitaryOrbitHull :=
  fun X hX ↦ mem_twoSidedUnitaryOrbitHull.mpr
    ⟨1, fun _ ↦ 1, fun _ ↦ X, fun _ ↦ zero_le_one, by simp, fun _ ↦ hX, by simp⟩

@[simp]
theorem self_mem_twoSidedUnitaryOrbitHull (C : E →ₗ[𝕜] F) : C ∈ C.twoSidedUnitaryOrbitHull :=
  C.twoSidedUnitaryOrbit_subset_twoSidedUnitaryOrbitHull C.self_mem_twoSidedUnitaryOrbit

/-- When `F` is also a real vector space compatibly with its `𝕜`-structure (for instance when `𝕜`
is `ℝ` or `ℂ`), the orbit hull is the convex hull `convexHull ℝ` of the two-sided unitary orbit. -/
theorem twoSidedUnitaryOrbitHull_eq_convexHull [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    (C : E →ₗ[𝕜] F) : C.twoSidedUnitaryOrbitHull = convexHull ℝ C.twoSidedUnitaryOrbit := by
  have hsmul (t : ℝ) (Y : E →ₗ[𝕜] F) : (t : 𝕜) • Y = t • Y := by
    ext x
    exact (RCLike.real_smul_eq_coe_smul t (Y x)).symm
  ext X
  rw [mem_twoSidedUnitaryOrbitHull, mem_convexHull_iff_exists_fintype]
  constructor
  · rintro ⟨n, t, Y, ht, htsum, hY, rfl⟩
    exact ⟨Fin n, inferInstance, t, Y, ht, htsum, hY, by simp only [hsmul]⟩
  · rintro ⟨ι, _, t, Y, ht, htsum, hY, rfl⟩
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, t ∘ e.symm, Y ∘ e.symm, fun i ↦ ht _, ?_, fun i ↦ hY _, ?_⟩
    · rw [← htsum]
      exact e.symm.sum_comp t
    · simp only [Function.comp_apply, hsmul]
      exact e.symm.sum_comp fun i ↦ t i • Y i

/-- The orbit hull depends only on the orbit: it is the same for every point of the orbit. -/
theorem twoSidedUnitaryOrbitHull_eq_of_mem {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.twoSidedUnitaryOrbitHull = C.twoSidedUnitaryOrbitHull := by
  ext
  simp only [mem_twoSidedUnitaryOrbitHull, twoSidedUnitaryOrbit_eq_of_mem h]

/-- The orbit hull is convex: it is closed under convex combinations of two of its points. -/
theorem smul_add_smul_mem_twoSidedUnitaryOrbitHull {C X Y : E →ₗ[𝕜] F}
    (hX : X ∈ C.twoSidedUnitaryOrbitHull) (hY : Y ∈ C.twoSidedUnitaryOrbitHull) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : 𝕜) • X + (b : 𝕜) • Y ∈ C.twoSidedUnitaryOrbitHull := by
  obtain ⟨n, t, X', ht, htsum, hX', rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp hX
  obtain ⟨m, s, Y', hs, hssum, hY', rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp hY
  refine mem_twoSidedUnitaryOrbitHull.mpr ⟨n + m, Fin.append (a • t) (b • s), Fin.append X' Y',
    fun i ↦ ?_, ?_, fun i ↦ ?_, ?_⟩
  · cases i using Fin.addCases <;> simp [mul_nonneg, *]
  · simp [Fin.sum_univ_add, ← Finset.mul_sum, htsum, hssum, hab]
  · cases i using Fin.addCases <;> simp [*]
  · simp [Fin.sum_univ_add, Finset.smul_sum, smul_smul]

/-- The orbit hull is invariant under unitaries of the source and of the target. -/
theorem linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbitHull {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbitHull) (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (U : F →ₗ[𝕜] F) ∘ₗ X ∘ₗ (V : E →ₗ[𝕜] E) ∈ C.twoSidedUnitaryOrbitHull := by
  obtain ⟨n, t, Y, ht, htsum, hY, rfl⟩ := mem_twoSidedUnitaryOrbitHull.mp h
  refine mem_twoSidedUnitaryOrbitHull.mpr
    ⟨n, t, fun i ↦ (U : F →ₗ[𝕜] F) ∘ₗ Y i ∘ₗ (V : E →ₗ[𝕜] E), ht, htsum, fun i ↦ ?_, ?_⟩
  · rw [← twoSidedUnitaryOrbit_eq_of_mem (hY i)]
    exact (Y i).linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbit U V
  · ext x
    simp

/-- **Minimality of the orbit hull.** The orbit hull of `C` is contained in every set that contains
the two-sided unitary orbit of `C` and is closed under convex combinations of two of its points. -/
theorem twoSidedUnitaryOrbitHull_subset {C : E →ₗ[𝕜] F} {S : Set (E →ₗ[𝕜] F)}
    (hS : C.twoSidedUnitaryOrbit ⊆ S)
    (hconv : ∀ X ∈ S, ∀ Y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (a : 𝕜) • X + (b : 𝕜) • Y ∈ S) :
    C.twoSidedUnitaryOrbitHull ⊆ S := by
  rintro _ ⟨n, t, Y, ht, htsum, hY, rfl⟩
  induction n with
  | zero => simp at htsum
  | succ n ih =>
    -- Split off the first point and rescale the remaining weights to sum to `1`.
    rw [Fin.sum_univ_succ] at htsum ⊢
    set s := ∑ i : Fin n, t i.succ
    have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ ht _
    rcases hs.eq_or_lt with hs | hs
    · have ht' (i : Fin n) : t i.succ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ ht _).mp hs.symm i (Finset.mem_univ _)
      have ht0 : t 0 = 1 := by simpa [← hs] using htsum
      simpa [ht', ht0] using hS (hY 0)
    · have hmem := ih (fun i ↦ t i.succ / s) (fun i ↦ Y i.succ) (fun i ↦ div_nonneg (ht _) hs.le)
        (by rw [← Finset.sum_div, div_self hs.ne']) fun i ↦ hY _
      convert hconv _ (hS (hY 0)) _ hmem (t 0) s (ht 0) hs.le htsum using 2
      simp only [Finset.smul_sum, smul_smul, RCLike.ofReal_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_div_cancel₀ _ (RCLike.ofReal_ne_zero.mpr hs.ne')]

/-- The orbit hull of a point of the orbit hull of `C` is contained in the orbit hull of `C`. -/
theorem twoSidedUnitaryOrbitHull_subset_of_mem {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbitHull) :
    X.twoSidedUnitaryOrbitHull ⊆ C.twoSidedUnitaryOrbitHull := by
  refine twoSidedUnitaryOrbitHull_subset (fun Y hY ↦ ?_)
    fun _ hX _ hY _ _ ha hb hab ↦ smul_add_smul_mem_twoSidedUnitaryOrbitHull hX hY ha hb hab
  obtain ⟨U, V, rfl⟩ := mem_twoSidedUnitaryOrbit.mp hY
  exact linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbitHull h U V

end LinearMap

namespace TauCeti

/-- A **unitarily invariant seminorm** on the linear maps `E →ₗ[𝕜] F`: a seminorm `N` with
`N (U ∘ A ∘ V) = N A` for every unitary `U` of the target `F` and every unitary `V` of the source
`E`, acting independently. Square operators are the case `E = F`. -/
structure UnitarilyInvariantSeminorm (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] extends Seminorm 𝕜 (E →ₗ[𝕜] F) where
  /-- Invariance under unitaries of the target and of the source. -/
  map_linearIsometryEquiv_comp_comp' (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    toSeminorm ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = toSeminorm A

namespace UnitarilyInvariantSeminorm

instance : FunLike (UnitarilyInvariantSeminorm 𝕜 E F) (E →ₗ[𝕜] F) ℝ where
  coe N := N.toFun
  coe_injective := by
    rintro ⟨N, _⟩ ⟨M, _⟩ h
    congr
    exact Seminorm.ext (congrFun h)

instance : SeminormClass (UnitarilyInvariantSeminorm 𝕜 E F) 𝕜 (E →ₗ[𝕜] F) where
  map_zero N := N.map_zero'
  map_add_le_add N := N.add_le'
  map_neg_eq_map N := N.neg'
  map_smul_eq_mul N := N.smul'

@[ext]
theorem ext {N M : UnitarilyInvariantSeminorm 𝕜 E F} (h : ∀ A, N A = M A) : N = M :=
  DFunLike.ext N M h

@[simp]
theorem coe_toSeminorm (N : UnitarilyInvariantSeminorm 𝕜 E F) : ⇑N.toSeminorm = N :=
  (rfl)

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/-- **Unitary invariance**: `N (U ∘ A ∘ V) = N A` for unitaries `U` of the target and `V` of the
source. -/
theorem map_linearIsometryEquiv_comp_comp (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) : N ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = N A :=
  N.map_linearIsometryEquiv_comp_comp' U V A

@[simp]
theorem map_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N ((U : F →ₗ[𝕜] F) ∘ₗ A) = N A := by
  convert N.map_linearIsometryEquiv_comp_comp U (.refl 𝕜 E) A using 2
  ext; simp

@[simp]
theorem map_comp_linearIsometryEquiv (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    N (A ∘ₗ (V : E →ₗ[𝕜] E)) = N A := by
  convert N.map_linearIsometryEquiv_comp_comp (.refl 𝕜 F) V A using 2
  ext; simp

/-- A unitarily invariant seminorm is constant on each two-sided unitary orbit. -/
theorem map_eq_of_mem_twoSidedUnitaryOrbit {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbit) : N X = N C := by
  obtain ⟨U, V, rfl⟩ := h
  exact N.map_linearIsometryEquiv_comp_comp U V C

/-- **Determination by singular values.** On maps between finite-dimensional inner product spaces,
a unitarily invariant seminorm takes equal values at maps with the same singular values. -/
theorem map_eq_of_singularValues_eq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A B : E →ₗ[𝕜] F} (h : A.singularValues = B.singularValues) : N A = N B :=
  N.map_eq_of_mem_twoSidedUnitaryOrbit
    (LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq.mpr h)

/-! ### Transport along isometric isomorphisms -/

/-- The value of `N` on maps `E' →ₗ[𝕜] F'` read through isometric isomorphisms `E ≃ E'` and
`F ≃ F'`; `UnitarilyInvariantSeminorm.arrowCongr` packages it as an equivalence. -/
private noncomputable def transport (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F')
    (N : UnitarilyInvariantSeminorm 𝕜 E F) : UnitarilyInvariantSeminorm 𝕜 E' F' where
  toSeminorm := N.toSeminorm.comp
    (LinearEquiv.arrowCongr eE.toLinearEquiv eF.toLinearEquiv).symm.toLinearMap
  map_linearIsometryEquiv_comp_comp' U V A := by
    -- Conjugating `U` and `V` back to `F` and `E` turns `U ∘ A ∘ V` into a two-sided unitary
    -- multiple of the transported map.
    have h := N.map_linearIsometryEquiv_comp_comp (eF.trans (U.trans eF.symm))
      (eE.trans (V.trans eE.symm)) ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E'))
    rw [Seminorm.comp_apply, Seminorm.comp_apply, coe_toSeminorm]
    convert h using 2 <;> ext <;> simp

private theorem transport_apply (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F')
    (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E' →ₗ[𝕜] F') :
    transport eE eF N A = N ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E')) :=
  (rfl)

/-- **Transport** of unitarily invariant seminorms along isometric isomorphisms `eE : E ≃ E'` of
the sources and `eF : F ≃ F'` of the targets: `N` corresponds to the seminorm
`A ↦ N (eF⁻¹ ∘ A ∘ eE)` on `E' →ₗ[𝕜] F'`, which is again unitarily invariant. -/
noncomputable def arrowCongr (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    UnitarilyInvariantSeminorm 𝕜 E F ≃ UnitarilyInvariantSeminorm 𝕜 E' F' where
  toFun := transport eE eF
  invFun := transport eE.symm eF.symm
  left_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp
  right_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp

@[simp]
theorem arrowCongr_apply (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') (A : E' →ₗ[𝕜] F') :
    arrowCongr eE eF N A = N ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E')) :=
  transport_apply eE eF N A

@[simp]
theorem arrowCongr_symm (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    (arrowCongr (𝕜 := 𝕜) eE eF).symm = arrowCongr eE.symm eF.symm :=
  (rfl)

/-- Transport along unitaries of the source and the target leaves every unitarily invariant
seminorm unchanged. -/
@[simp]
theorem arrowCongr_eq_self (U : E ≃ₗᵢ[𝕜] E) (V : F ≃ₗᵢ[𝕜] F) : arrowCongr U V N = N := by
  ext A
  rw [arrowCongr_apply, map_linearIsometryEquiv_comp_comp]

/-! ### Transport to the adjoint maps -/

section Adjoint

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The **adjoint transport** of a unitarily invariant seminorm `N` on `E →ₗ[𝕜] F`: the seminorm
`B ↦ N B†` on `F →ₗ[𝕜] E`, again unitarily invariant. -/
noncomputable def compAdjoint : UnitarilyInvariantSeminorm 𝕜 F E where
  toSeminorm := N.toSeminorm.comp (LinearMap.adjoint (𝕜 := 𝕜) (E := F) (F := E)).toLinearMap
  map_linearIsometryEquiv_comp_comp' U V B := by
    rw [Seminorm.comp_apply, Seminorm.comp_apply]
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc] using
      N.map_linearIsometryEquiv_comp_comp V.symm U.symm (LinearMap.adjoint B)

@[simp]
theorem compAdjoint_apply (B : F →ₗ[𝕜] E) : N.compAdjoint B = N (LinearMap.adjoint B) :=
  (rfl)

@[simp]
theorem compAdjoint_compAdjoint : N.compAdjoint.compAdjoint = N := by
  ext A
  simp

end Adjoint

/-! ### The operator modulus -/

/-- **Modulus invariance.** A unitarily invariant seminorm on the endomorphisms of a
finite-dimensional inner product space takes the same value at an endomorphism `A` and at its
modulus `|A| = √(A† A)`. -/
@[simp]
theorem map_operatorAbs [FiniteDimensional 𝕜 E] (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (A : E →ₗ[𝕜] E) : N A.operatorAbs = N A :=
  N.map_eq_of_singularValues_eq A.singularValues_operatorAbs

end UnitarilyInvariantSeminorm

/-! ### Finite orbit certificates -/

/-- A **finite unitary orbit certificate** for `X` over `C`, indexed by a finite type `ι`: a
representation `X = ∑ᵢ aᵢ • Uᵢ ∘ C ∘ Vᵢ` of `X` as a linear combination of points of the
two-sided unitary orbit of `C`. Its coefficient mass `∑ᵢ ‖aᵢ‖` bounds every unitarily invariant
seminorm of `X` by the same seminorm of `C`
(`TauCeti.UnitaryOrbitCertificate.apply_le_mass_mul`). -/
@[ext]
structure UnitaryOrbitCertificate (ι : Type*) [Fintype ι] (C X : E →ₗ[𝕜] F) where
  /-- The coefficients `aᵢ`. -/
  coeff : ι → 𝕜
  /-- The unitaries `Uᵢ` of the target. -/
  left : ι → F ≃ₗᵢ[𝕜] F
  /-- The unitaries `Vᵢ` of the source. -/
  right : ι → E ≃ₗᵢ[𝕜] E
  /-- The representation `∑ᵢ aᵢ • Uᵢ ∘ C ∘ Vᵢ = X`. -/
  sum_smul_comp_comp_eq :
    ∑ i, coeff i • ((left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (right i : E →ₗ[𝕜] E)) = X

namespace UnitaryOrbitCertificate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {C X : E →ₗ[𝕜] F}
  (c : UnitaryOrbitCertificate ι C X)

/-- The **coefficient mass** `∑ᵢ ‖aᵢ‖` of an orbit certificate. -/
noncomputable def mass : ℝ :=
  ∑ i, ‖c.coeff i‖

theorem mass_def : c.mass = ∑ i, ‖c.coeff i‖ :=
  (rfl)

theorem mass_nonneg : 0 ≤ c.mass :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- **Certificate bound**: if `X` has an orbit certificate over `C` of mass `m`, then
`N X ≤ m * N C` for every unitarily invariant seminorm `N`. -/
theorem apply_le_mass_mul (N : UnitarilyInvariantSeminorm 𝕜 E F) : N X ≤ c.mass * N C := by
  calc N X = N (∑ i, c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))) := by
        rw [c.sum_smul_comp_comp_eq]
    _ ≤ ∑ i, N (c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
    _ = c.mass * N C := by
        simp [mass_def, Finset.sum_mul, map_smul_eq_mul, N.map_linearIsometryEquiv_comp_comp]

/-- **Reindexing** an orbit certificate along an equivalence of its finite index types. -/
def reindex (e : ι ≃ κ) : UnitaryOrbitCertificate κ C X where
  coeff := c.coeff ∘ e.symm
  left := c.left ∘ e.symm
  right := c.right ∘ e.symm
  sum_smul_comp_comp_eq := (e.symm.sum_comp fun i ↦
    c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))).trans
      c.sum_smul_comp_comp_eq

@[simp]
theorem coeff_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).coeff k = c.coeff (e.symm k) :=
  (rfl)

@[simp]
theorem left_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).left k = c.left (e.symm k) :=
  (rfl)

@[simp]
theorem right_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).right k = c.right (e.symm k) :=
  (rfl)

@[simp]
theorem mass_reindex (e : ι ≃ κ) : (c.reindex e).mass = c.mass := by
  simp only [mass_def, coeff_reindex]
  exact e.symm.sum_comp fun i ↦ ‖c.coeff i‖

end UnitaryOrbitCertificate

/-- **Certificates from convex combinations.** Every point `X = ∑ᵢ tᵢ • Uᵢ C Vᵢ` of the convex hull
of the two-sided unitary orbit of `C` has an orbit certificate over `C` of mass one. -/
theorem UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull
    {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbitHull) :
    ∃ (n : ℕ) (c : UnitaryOrbitCertificate (Fin n) C X), c.mass = 1 := by
  obtain ⟨n, t, Y, ht, htsum, hY, rfl⟩ := LinearMap.mem_twoSidedUnitaryOrbitHull.mp h
  choose U V hUV using fun i ↦ LinearMap.mem_twoSidedUnitaryOrbit.mp (hY i)
  refine ⟨n, ⟨fun i ↦ (t i : 𝕜), U, V, by simp only [hUV]⟩, ?_⟩
  simp [mass_def, abs_of_nonneg (ht _), htsum]

/-- A unitarily invariant seminorm is bounded on the convex hull of the two-sided unitary orbit of
`C` by its value at `C`. -/
theorem UnitarilyInvariantSeminorm.map_le_of_mem_twoSidedUnitaryOrbitHull
    (N : UnitarilyInvariantSeminorm 𝕜 E F) {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbitHull) : N X ≤ N C := by
  obtain ⟨n, c, hc⟩ := UnitaryOrbitCertificate.exists_mass_eq_one_of_mem_twoSidedUnitaryOrbitHull h
  simpa [hc] using c.apply_le_mass_mul N

end TauCeti
end
end TAF_LiteralSource_0376

section TAF_LiteralSource_0377
/- Original module: TauCeti.Analysis.Matrix.SingularValues -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Singular values and two-sided unitary matrix orbits

Rectangular matrices lie in the same two-sided unitary orbit exactly when their singular values
agree. The singular values are Mathlib's `LinearMap.singularValues`, applied through
`Matrix.toEuclideanLin`; no second enumeration is introduced.

`Matrix.exists_unitary_mul_diagonal_mul_unitary` reads the operator singular value decomposition
in the standard orthonormal basis. The orbit characterization then identifies the diagonal
entries as complete invariants, including for singular matrices and in dimension zero.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Section 2.6.
-/

public section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Left multiplication by a unitary matrix preserves every singular value. -/
theorem singularValues_toEuclideanLin_unitary_mul
    (A : Matrix ι κ 𝕜) (U : unitaryGroup ι 𝕜) :
    (toEuclideanLin ((U : Matrix ι ι 𝕜) * A)).singularValues =
      (toEuclideanLin A).singularValues := by
  apply LinearMap.singularValues_eq_of_norm_apply_eq
  intro x
  have hU := Unitary.map_mem (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) U.property
  simpa only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply,
    ← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe] using
    ContinuousLinearMap.norm_map_of_mem_unitary hU (toEuclideanLin A x)

omit [DecidableEq ι] in
/-- Right multiplication by a unitary matrix preserves every singular value. -/
theorem singularValues_toEuclideanLin_mul_unitary
    (A : Matrix ι κ 𝕜) (U : unitaryGroup κ 𝕜) :
    (toEuclideanLin (A * (U : Matrix κ κ 𝕜))).singularValues =
      (toEuclideanLin A).singularValues := by
  classical
  rw [← LinearMap.singularValues_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_mul]
  exact (singularValues_toEuclideanLin_unitary_mul Aᴴ (star U)).trans
    (by rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.singularValues_adjoint])

/-- Every square matrix is a product of two unitary matrices and the diagonal matrix of its
singular values in decreasing order. Zero singular values are allowed. -/
theorem exists_unitary_mul_diagonal_mul_unitary (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U V : unitaryGroup (Fin n) 𝕜,
      A = (U : Matrix (Fin n) (Fin n) 𝕜) *
        diagonal (fun i : Fin n ↦ ((toEuclideanLin A).singularValues i : 𝕜)) * V := by
  let e := EuclideanSpace.basisFun (Fin n) 𝕜
  obtain ⟨U, V, h⟩ := (toEuclideanLin A).exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp e
  -- The operator theorem coerces isometries through continuous linear equivalences;
  -- matrix conversion uses their underlying linear equivalences. Compare these maps explicitly.
  have hc (W : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n)) :
      (W : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) =
        W.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  rw [hc U, hc V] at h
  refine ⟨⟨U.toMatrix e.toBasis e.toBasis, U.toMatrix_mem_unitaryGroup e e⟩,
    ⟨V.toMatrix e.toBasis e.toBasis, V.toMatrix_mem_unitaryGroup e e⟩, ?_⟩
  simpa only [e, toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_comp e.toBasis e.toBasis e.toBasis, LinearMap.toMatrix_toLin,
    mul_assoc] using
    congrArg (LinearMap.toMatrix e.toBasis e.toBasis) h

/-- In a two-sided unitary factorization with a nonnegative decreasing real diagonal,
the diagonal entries are the singular values. -/
theorem singularValues_toEuclideanLin_of_unitary_mul_diagonal_mul_unitary
    (A : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hanti : Antitone d) (U V : unitaryGroup (Fin n) 𝕜)
    (h : A = (U : Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i ↦ (d i : 𝕜)) * V)
    (i : Fin n) : (toEuclideanLin A).singularValues i = d i := by
  rw [h, singularValues_toEuclideanLin_mul_unitary, singularValues_toEuclideanLin_unitary_mul]
  have hnorm (j : Fin n) : ‖(d j : 𝕜)‖ = d j := RCLike.norm_of_nonneg (hd j)
  simpa only [toEuclideanLin_eq_toLin_orthonormal, Equiv.refl_apply, hnorm] using
    Matrix.singularValues_toLin_diagonal (EuclideanSpace.basisFun (Fin n) 𝕜)
      (fun j ↦ (d j : 𝕜)) (Equiv.refl _)
      (by simpa only [Equiv.refl_apply, hnorm] using hanti) i

/-- Singular values classify two-sided unitary orbits of rectangular matrices. This is the matrix
form of `LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq`. -/
theorem exists_unitary_mul_mul_unitary_iff_singularValues_eq
    (A B : Matrix ι κ 𝕜) :
    (∃ (U : unitaryGroup ι 𝕜) (V : unitaryGroup κ 𝕜),
      B = (U : Matrix ι ι 𝕜) * A * (V : Matrix κ κ 𝕜)) ↔
      (toEuclideanLin A).singularValues = (toEuclideanLin B).singularValues := by
  constructor
  · rintro ⟨U, V, rfl⟩
    rw [singularValues_toEuclideanLin_mul_unitary,
      singularValues_toEuclideanLin_unitary_mul]
  · intro h
    obtain ⟨U, V, hUV⟩ := LinearMap.mem_twoSidedUnitaryOrbit.mp
      ((LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq
        (C := toEuclideanLin A) (X := toEuclideanLin B)).mpr h.symm)
    let eι := EuclideanSpace.basisFun ι 𝕜
    let eκ := EuclideanSpace.basisFun κ 𝕜
    -- Compare the continuous-linear and linear-equivalence coercions before taking matrices.
    have hcU : (U : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) =
        U.toLinearEquiv.toLinearMap := by
      ext x
      rfl
    have hcV : (V : EuclideanSpace 𝕜 κ →ₗ[𝕜] EuclideanSpace 𝕜 κ) =
        V.toLinearEquiv.toLinearMap := by
      ext x
      rfl
    rw [hcU, hcV] at hUV
    refine ⟨⟨U.toMatrix eι.toBasis eι.toBasis, U.toMatrix_mem_unitaryGroup eι eι⟩,
      ⟨V.toMatrix eκ.toBasis eκ.toBasis, V.toMatrix_mem_unitaryGroup eκ eκ⟩, ?_⟩
    simpa only [eι, eκ, toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_comp eκ.toBasis eκ.toBasis eι.toBasis,
      LinearMap.toMatrix_comp eκ.toBasis eι.toBasis eι.toBasis, LinearMap.toMatrix_toLin,
      Matrix.mul_assoc] using
      congrArg (LinearMap.toMatrix eκ.toBasis eι.toBasis) hUV.symm

end Matrix
end
end TAF_LiteralSource_0377

section TAF_LiteralSource_0378
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Matrix.mvPolynomialX`, the matrix of variables, and `Matrix.eval_det_mvPolynomialX` occur in the
-- statements and proofs below; this module also supplies `MvPolynomial.eval`.
-- The `GL` notation, the coercion of an element of `GL n k` to a matrix,
-- `Matrix.GeneralLinearGroup.det` and `Matrix.GeneralLinearGroup.det_ne_zero`.

/-!
# Polynomial and rational functions on the general linear group

Two subalgebras of the `k`-valued functions on `GL n k`: the functions given by a polynomial in the
matrix entries, and those given by such a polynomial divided by a power of the determinant.  They
are the coordinate-level bookkeeping behind the polynomial and rational representations of
`GL n ℂ`, where a representation is polynomial or rational exactly when all of its matrix
coefficients lie in one of them.

The rational condition is stated multiplicatively, as `det ^ m * f` being polynomial, so that no
inverse is taken and it lives over an arbitrary commutative ring, as the polynomial condition does
over an arbitrary commutative semiring;
`TauCeti.Matrix.GeneralLinearGroup.mem_rationalFunctions_iff_inv` is the equivalent `(det ^ m)⁻¹`
form over a field.

Over a finite field every function on the finite set `GL n k` is the evaluation of a polynomial in
the matrix entries, so `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` is then the whole
function algebra and the distinction between the two collapses.  Consumers for which the distinction
is the point work over an infinite field.

## Main definitions

* `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions`,
  `TauCeti.Matrix.GeneralLinearGroup.rationalFunctions`: the two subalgebras of `GL (Fin n) k → k`.

## Main results

* `TauCeti.Matrix.GeneralLinearGroup.det_zpow_mem_rationalFunctions`: every integral power of the
  determinant is a rational function.
* `TauCeti.Matrix.GeneralLinearGroup.exists_forall_det_pow_mul_eq_of_forall_mem_rationalFunctions`
  and its field form
  `TauCeti.Matrix.GeneralLinearGroup.exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions`: a
  finite family of rational functions admits a common denominator.
-/

public section

open Matrix MvPolynomial

universe u w

namespace TauCeti

namespace Matrix.GeneralLinearGroup

section CommSemiring

variable {k : Type u} [CommSemiring k] {n : ℕ}

variable (k n) in
/-- **The polynomial functions on `GL n k`**: those `f : GL (Fin n) k → k` obtained by evaluating a
polynomial in the matrix entries, that is, the range of the algebra map sending the variable indexed
by `(i, j)` to the `(i, j)` entry. -/
noncomputable def polynomialFunctions : Subalgebra k (GL (Fin n) k → k) :=
  (MvPolynomial.aeval fun p : Fin n × Fin n =>
    fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) p.1 p.2).range

/-- Evaluating the generator of `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions` at a group
element is evaluation of the polynomial at the entries of that element. -/
private theorem aeval_entry_apply (P : MvPolynomial (Fin n × Fin n) k) (g : GL (Fin n) k) :
    (MvPolynomial.aeval fun p : Fin n × Fin n =>
        fun h : GL (Fin n) k => (h : Matrix (Fin n) (Fin n) k) p.1 p.2) P g
      = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P := by
  simpa [MvPolynomial.aeval_eq_eval] using MvPolynomial.comp_aeval_apply
    (fun p : Fin n × Fin n => fun h : GL (Fin n) k => (h : Matrix (Fin n) (Fin n) k) p.1 p.2)
    (Pi.evalAlgHom k (fun _ : GL (Fin n) k => k) g) P

/-- **Membership in the polynomial functions**: `f` is polynomial exactly when some polynomial in
the matrix entries evaluates to `f g` at every `g`. -/
theorem mem_polynomialFunctions {f : GL (Fin n) k → k} :
    f ∈ polynomialFunctions k n ↔ ∃ P : MvPolynomial (Fin n × Fin n) k, ∀ g : GL (Fin n) k,
      f g = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P, fun g => aeval_entry_apply P g⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, funext fun g => (aeval_entry_apply P g).trans (hP g).symm⟩

/-- The matrix entries themselves are polynomial functions. -/
@[simp]
theorem entry_mem_polynomialFunctions (i j : Fin n) :
    (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) ∈ polynomialFunctions k n :=
  mem_polynomialFunctions.mpr ⟨X (i, j), fun g => by simp⟩

end CommSemiring

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Evaluating the generic determinant at the entries of `g` gives `det g`. -/
@[simp]
theorem eval_entries_det_mvPolynomialX (g : GL (Fin n) k) :
    MvPolynomial.eval (fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) k) p.1 p.2)
        (_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det
      = (g : Matrix (Fin n) (Fin n) k).det := by
  rw [_root_.Matrix.eval_det_mvPolynomialX]
  congr 1

variable (k n)

/-- **The rational functions on `GL n k`**: those `f : GL (Fin n) k → k` some determinant power of
which is polynomial in the matrix entries.  Stated multiplicatively, as `det ^ m * f` being
polynomial, so that no inverse is taken and the definition makes sense over a commutative ring;
`TauCeti.Matrix.GeneralLinearGroup.mem_rationalFunctions_iff_inv` is the form with `(det ^ m)⁻¹`
over a field. -/
noncomputable def rationalFunctions : Subalgebra k (GL (Fin n) k → k) where
  carrier := {f | ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ), ∀ g : GL (Fin n) k,
    (g : Matrix (Fin n) (Fin n) k).det ^ m * f g
      = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P}
  mul_mem' := by
    rintro f₁ f₂ ⟨P₁, m₁, hP₁⟩ ⟨P₂, m₂, hP₂⟩
    refine ⟨P₁ * P₂, m₁ + m₂, fun g => ?_⟩
    rw [map_mul, ← hP₁ g, ← hP₂ g, pow_add, Pi.mul_apply]
    ring
  one_mem' := ⟨1, 0, fun g => by simp⟩
  add_mem' := by
    rintro f₁ f₂ ⟨P₁, m₁, hP₁⟩ ⟨P₂, m₂, hP₂⟩
    refine ⟨(_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det ^ m₂ * P₁
      + (_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det ^ m₁ * P₂, m₁ + m₂, fun g => ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, eval_entries_det_mvPolynomialX, ← hP₁ g,
      ← hP₂ g, pow_add, Pi.add_apply]
    ring
  zero_mem' := ⟨0, 0, fun g => by simp⟩
  algebraMap_mem' c := ⟨C c, 0, fun g => by simp⟩

variable {k n}

/-- **Membership in the rational functions**: `f` is rational exactly when some determinant power
`det ^ m` makes `det ^ m * f` the evaluation of a polynomial in the matrix entries. -/
theorem mem_rationalFunctions {f : GL (Fin n) k → k} :
    f ∈ rationalFunctions k n ↔ ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ g : GL (Fin n) k, (g : Matrix (Fin n) (Fin n) k).det ^ m * f g
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P :=
  Iff.rfl

/-- A polynomial function is rational. -/
theorem polynomialFunctions_le_rationalFunctions :
    polynomialFunctions k n ≤ rationalFunctions k n := by
  intro f hf
  obtain ⟨P, hP⟩ := mem_polynomialFunctions.mp hf
  exact ⟨P, 0, fun g => by simp [hP g]⟩

/-- The determinant is a polynomial function. -/
@[simp]
theorem det_mem_polynomialFunctions :
    (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det) ∈ polynomialFunctions k n :=
  mem_polynomialFunctions.mpr
    ⟨(_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det, fun g => by simp⟩

/-- **Every integral determinant power is a rational function.**  For `0 ≤ m` it is even a
polynomial function, by `TauCeti.Matrix.GeneralLinearGroup.det_mem_polynomialFunctions`. -/
@[simp]
theorem det_zpow_mem_rationalFunctions (m : ℤ) :
    (fun g : GL (Fin n) k => ((_root_.Matrix.GeneralLinearGroup.det g ^ m : kˣ) : k))
      ∈ rationalFunctions k n := by
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    have hpow :
        (fun g : GL (Fin n) k => ((_root_.Matrix.GeneralLinearGroup.det g ^ (m : ℤ) : kˣ) : k))
          = (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det) ^ m := by
      funext g
      simp [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hpow]
    exact polynomialFunctions_le_rationalFunctions (pow_mem det_mem_polynomialFunctions m)
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = -(M : ℤ) := ⟨(-m).toNat, by omega⟩
    refine ⟨1, M, fun g => ?_⟩
    rw [← _root_.Matrix.GeneralLinearGroup.val_det_apply, map_one,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast,
      ← zpow_add (_root_.Matrix.GeneralLinearGroup.det g)]
    simp

/-- **A finite family of rational functions has a common denominator**: a single determinant power
and a family of numerator polynomials express every member of the family. -/
theorem exists_forall_det_pow_mul_eq_of_forall_mem_rationalFunctions {ι : Type w} [Finite ι]
    {f : ι → GL (Fin n) k → k} (hf : ∀ i, f i ∈ rationalFunctions k n) :
    ∃ (P : ι → MvPolynomial (Fin n × Fin n) k) (m : ℕ), ∀ (i : ι) (g : GL (Fin n) k),
      (g : Matrix (Fin n) (Fin n) k).det ^ m * f i g
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) (P i) := by
  have : Fintype ι := Fintype.ofFinite ι
  choose P m hPm using fun i => mem_rationalFunctions.mp (hf i)
  refine ⟨fun i => (_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det ^ (Finset.univ.sup m - m i)
    * P i, Finset.univ.sup m, fun i g => ?_⟩
  have hle : m i ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ i)
  rw [map_mul, map_pow, eval_entries_det_mvPolynomialX, ← hPm i g, ← mul_assoc, ← pow_add]
  congr 2
  omega

end CommRing

section Field

variable {k : Type u} [Field k] {n : ℕ}

/-- Over a field, membership in the rational functions is the expected statement that `f` is a
polynomial in the matrix entries divided by a power of the determinant. -/
theorem mem_rationalFunctions_iff_inv {f : GL (Fin n) k → k} :
    f ∈ rationalFunctions k n ↔ ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ g : GL (Fin n) k, f g = ((g : Matrix (Fin n) (Fin n) k).det ^ m)⁻¹ *
        MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P := by
  rw [mem_rationalFunctions]
  refine exists_congr fun P => exists_congr fun m => forall_congr' fun g => ?_
  have hdet : (g : Matrix (Fin n) (Fin n) k).det ^ m ≠ 0 :=
    pow_ne_zero _ (_root_.Matrix.GeneralLinearGroup.det_ne_zero g)
  rw [eq_comm, eq_inv_mul_iff_mul_eq₀ hdet, eq_comm]

/-- **A finite family of rational functions has a common denominator**, in the form with the
determinant power inverted.  This is what lets the coordinate form of rationality carry a single
exponent for the whole matrix. -/
theorem exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions {ι : Type w} [Finite ι]
    {f : ι → GL (Fin n) k → k} (hf : ∀ i, f i ∈ rationalFunctions k n) :
    ∃ (P : ι → MvPolynomial (Fin n × Fin n) k) (m : ℕ), ∀ (i : ι) (g : GL (Fin n) k),
      f i g = ((g : Matrix (Fin n) (Fin n) k).det ^ m)⁻¹ *
        MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) (P i) := by
  obtain ⟨P, m, hPm⟩ := exists_forall_det_pow_mul_eq_of_forall_mem_rationalFunctions hf
  refine ⟨P, m, fun i g => ?_⟩
  rw [← hPm i g, inv_mul_cancel_left₀
    (pow_ne_zero _ (_root_.Matrix.GeneralLinearGroup.det_ne_zero g))]

end Field

end Matrix.GeneralLinearGroup

end TauCeti
end
end TAF_LiteralSource_0378

section TAF_LiteralSource_0379
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Unitary -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The unitary group is Zariski dense in the complex matrices

A polynomial in the entries of a square complex matrix is determined by its values on the
unitary matrices. The unitary group is cut out by the equations `star A * A = 1`, which involve
complex conjugation and so are not polynomial; it is a real form of `GL n ℂ`, not an algebraic
subgroup of it, and over `ℂ` it is Zariski dense.

The proof is the singular value decomposition `A = U * diagonal d * V` with `U`, `V` unitary
(`Matrix.exists_unitary_mul_diagonal_mul_unitary`). Substituting `U * diagonal z * V` into a
polynomial gives a polynomial in `z ∈ ℂⁿ`, and `U * diagonal z * V` is unitary whenever every
`zᵢ` lies on the unit circle. A polynomial in `n` variables vanishing on the torus `(S¹)ⁿ` is zero,
since the circle is infinite (`MvPolynomial.funext_set`), so evaluating at `z = d` recovers the
value at `A`.

The same holds for the rational functions on `GL n ℂ`, those of the form `P / det ^ m`: two of
them agreeing on the unitary group agree everywhere. This is the algebraic input to Weyl's
unitarian trick, which reduces questions about the rational representations of `GL n ℂ` to
questions about the continuous representations of the compact group `U(n)`.

Over `ℝ` the analogous statement fails: the orthogonal group is cut out by polynomial equations,
so it is a proper Zariski-closed subset of the real matrices.

## Main results

* `MvPolynomial.eq_of_eval_eq_on_unitaryGroup`: two polynomials in the entries of a complex
  matrix that agree on the unitary group are equal. This is the unitary counterpart of Mathlib's
  `MvPolynomial.eq_of_eval_eq_on_gl`.
* `TauCeti.Matrix.GeneralLinearGroup.eq_of_mem_rationalFunctions_of_forall_unitary`: two rational
  functions on `GL n ℂ` that agree on the unitary group are equal.

## References

* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter VIII, §11.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 2.4.
-/

public section

namespace MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The unitary group is Zariski dense in the complex matrices.** Two polynomials in the entries
of a square complex matrix that take the same value at every unitary matrix are equal. -/
theorem eq_of_eval_eq_on_unitaryGroup {p q : MvPolynomial (ι × ι) ℂ}
    (h : ∀ U ∈ Matrix.unitaryGroup ι ℂ,
      eval (fun ij => U ij.1 ij.2) p = eval (fun ij => U ij.1 ij.2) q) :
    p = q := by
  refine MvPolynomial.funext fun x => ?_
  -- Only the shape `U * diagonal d * V` of the singular value decomposition is used; it is
  -- transported from `Fin (Fintype.card ι)` along an enumeration of `ι`.
  obtain ⟨d, U, V, hA⟩ : ∃ (d : ι → ℂ) (U V : Matrix.unitaryGroup ι ℂ),
      Matrix.of (fun i j => x (i, j)) = (U : Matrix ι ι ℂ) * Matrix.diagonal d * V := by
    let e := Fintype.equivFin ι
    obtain ⟨d, U, V, hUV⟩ : ∃ (d : Fin (Fintype.card ι) → ℂ)
        (U V : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ),
        (Matrix.of fun i j => x (i, j)).submatrix e.symm e.symm =
          (U : Matrix _ _ ℂ) * Matrix.diagonal d * (V : Matrix _ _ ℂ) :=
      ⟨_, Matrix.exists_unitary_mul_diagonal_mul_unitary _⟩
    refine ⟨d ∘ e, ⟨(U : Matrix _ _ ℂ).submatrix e e, Matrix.submatrix_equiv_mem_unitary.mpr U.2⟩,
      ⟨(V : Matrix _ _ ℂ).submatrix e e, Matrix.submatrix_equiv_mem_unitary.mpr V.2⟩, ?_⟩
    rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, ← hUV, Matrix.submatrix_submatrix]
    simp
  -- Substituting `U * diagonal z * V` for the matrix of variables, as a polynomial in `z`.
  let F : ι × ι → MvPolynomial ι ℂ := fun ij =>
    ∑ k, C ((U : Matrix ι ι ℂ) ij.1 k * (V : Matrix ι ι ℂ) k ij.2) * X k
  have hF (z : ι → ℂ) (r : MvPolynomial (ι × ι) ℂ) :
      eval z (bind₁ F r) = eval (fun ij => ((U : Matrix ι ι ℂ) * Matrix.diagonal z * V) ij.1 ij.2)
        r := by
    -- `eval z` is `eval₂Hom (RingHom.id ℂ) z` by definition.
    refine (eval₂Hom_bind₁ (RingHom.id ℂ) z F r).trans
      (congrArg (fun y => eval y r) (_root_.funext fun ij => ?_))
    rw [Matrix.mul_apply]
    simp only [F, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply,
      Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- The unit circle is infinite, being connected with more than one point.
  have hS : (Metric.sphere (0 : ℂ) 1).Infinite :=
    IsPreconnected.infinite_of_nontrivial
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0
        zero_le_one).isPreconnected ⟨1, by simp, -1, by simp, by norm_num⟩
  have hpq : bind₁ F p = bind₁ F q := by
    refine MvPolynomial.funext_set (fun _ => Metric.sphere (0 : ℂ) 1) (fun _ => hS)
      fun z hz => ?_
    rw [hF, hF]
    refine h _ (mul_mem (mul_mem U.2 ?_) V.2)
    refine Matrix.diagonal_mem_unitary.mpr (Pi.mem_unitary_iff.mpr fun i => ?_)
    -- A complex number of modulus one is unitary: `conj z * z = ‖z‖ ^ 2 = 1`.
    rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
      mem_sphere_zero_iff_norm.mp (hz i trivial)]
    norm_num
  have hx : x = fun ij => ((U : Matrix ι ι ℂ) * Matrix.diagonal d * V) ij.1 ij.2 :=
    _root_.funext fun ij => congrFun (congrFun hA ij.1) ij.2
  rw [hx, ← hF, ← hF, hpq]

end MvPolynomial

namespace TauCeti.Matrix.GeneralLinearGroup

open _root_.Matrix

variable {n : ℕ}

/-- **A rational function on `GL n ℂ` is determined by its values on the unitary group.** Two
rational functions, polynomials in the entries divided by a power of the determinant, that agree
at every unitary matrix are equal. -/
theorem eq_of_mem_rationalFunctions_of_forall_unitary {f g : GL (Fin n) ℂ → ℂ}
    (hf : f ∈ rationalFunctions ℂ n) (hg : g ∈ rationalFunctions ℂ n)
    (h : ∀ u : unitaryGroup (Fin n) ℂ, f (Unitary.toUnits u) = g (Unitary.toUnits u)) :
    f = g := by
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions.mp (sub_mem hf hg)
  have hP0 : P = 0 := by
    refine MvPolynomial.eq_of_eval_eq_on_unitaryGroup fun U hU => ?_
    have h1 := hP (Unitary.toUnits ⟨U, hU⟩)
    rw [Pi.sub_apply, h, sub_self, mul_zero] at h1
    simpa using h1.symm
  funext x
  have hx := hP x
  rw [hP0, map_zero, Pi.sub_apply, mul_eq_zero, sub_eq_zero] at hx
  exact hx.resolve_left (pow_ne_zero _ (_root_.Matrix.GeneralLinearGroup.det_ne_zero x))

end TauCeti.Matrix.GeneralLinearGroup
end
end TAF_LiteralSource_0379

section TAF_LiteralSource_0380
/- Original module: TauCeti.LinearAlgebra.PiTensorProduct.Map -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor maps of families of linear maps

Mathlib's `PiTensorProduct.map_update_add` says that `PiTensorProduct.map` is additive in each
factor. This file records the form of that statement used when two tensor maps are compared
directly: if two families of linear maps agree away from one index `k`, then the sum of their
tensor maps is the tensor map of the family whose `k`-th factor is the sum of the two `k`-th
factors. It also records that a tensor map over an empty index type is the identity.

## Main results

* `TauCeti.PiTensorProduct.map_add_map_eq_map_update`: the sum of two tensor maps whose factors
  agree away from one index.
* `TauCeti.PiTensorProduct.map_of_isEmpty`: a tensor map over an empty index type is the
  identity.
-/

public section

universe uι uR us ut

namespace TauCeti.PiTensorProduct

variable {ι : Type uι} {R : Type uR} {s : ι → Type us} {t : ι → Type ut} [DecidableEq ι]
  [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)] [∀ i, AddCommMonoid (t i)]
  [∀ i, Module R (t i)]

/-- Two tensor maps whose factors agree away from one index `k` add up to the tensor map with the
sum of their factors at `k`. -/
theorem map_add_map_eq_map_update (f g : ∀ i, s i →ₗ[R] t i) (k : ι)
    (h : ∀ i, i ≠ k → f i = g i) :
    PiTensorProduct.map f + PiTensorProduct.map g =
      PiTensorProduct.map (Function.update f k (f k + g k)) := by
  have hg : g = Function.update f k (g k) := by
    funext i
    by_cases hi : i = k
    · subst hi
      simp
    · simp [Function.update_of_ne hi, h i hi]
  rw [PiTensorProduct.map_update_add, Function.update_eq_self, ← hg]

omit [DecidableEq ι] in
/-- Over an empty index type, every tensor map of endomorphisms is the identity. -/
@[simp]
theorem map_of_isEmpty [IsEmpty ι] (f : ∀ i, s i →ₗ[R] s i) :
    PiTensorProduct.map f = LinearMap.id := by
  rw [Subsingleton.elim f fun _ ↦ LinearMap.id, PiTensorProduct.map_id]

end TauCeti.PiTensorProduct
end
end TAF_LiteralSource_0380

section TAF_LiteralSource_0381
/- Original module: TauCeti.LinearAlgebra.TensorPower.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic operations on tensor powers

Mathlib's `TensorPower.mulEquiv` identifies `⨂[R]^k M ⊗[R] ⨂[R]^m M` with `⨂[R]^(k + m) M`.  This
file records the inverse operation: `TensorPower.splitAt` cuts a tensor power of length `n` after
its first `k` factors, landing in `⨂[R]^k M ⊗[R] ⨂[R]^(n - k) M`, together with its value on pure
tensors and the fact that it is injective. It also identifies the first tensor power with the
underlying module, and shows that `TensorPower.mulEquiv` is natural with respect to tensor-power
maps.

## Main definitions

* `TensorPower.splitAt`: split a tensor power at a specified position.
* `TauCeti.TensorPower.oneEquiv`: identify the first tensor power with the underlying module.

## Main results

* `TauCeti.TensorPower.mulEquiv_comp_map`: `TensorPower.mulEquiv` intertwines tensor-power maps
  with the tensor-power map of the appended family.

-/

public section

open scoped TensorProduct

universe uR uM

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TauCeti.TensorPower

/-- A tensor word of length one is a single letter. -/
noncomputable def oneEquiv : TensorPower R 1 M ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0

/-- The length-one tensor-power equivalence evaluates a pure tensor at its unique index. -/
@[simp]
theorem oneEquiv_tprod (f : Fin 1 → M) :
    oneEquiv R M (PiTensorProduct.tprod R f) = f 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod 0 f

/-- The inverse length-one tensor-power equivalence sends a letter to the corresponding pure
tensor. -/
@[simp]
theorem oneEquiv_symm_apply (a : M) :
    (oneEquiv R M).symm a = PiTensorProduct.tprod R (fun _ ↦ a) :=
  PiTensorProduct.subsingletonEquiv_symm_apply' 0 a

section map

variable {R M} {N : Type*} [AddCommMonoid N] [Module R N]

/-- Concatenating tensor powers intertwines the tensor product of two tensor-power maps with the
tensor-power map of the appended family of factors. -/
theorem mulEquiv_comp_map {d e : ℕ} (f : Fin d → M →ₗ[R] N) (g : Fin e → M →ₗ[R] N) :
    (TensorPower.mulEquiv (R := R) (M := N) (n := d) (m := e)).toLinearMap ∘ₗ
        TensorProduct.map (PiTensorProduct.map f) (PiTensorProduct.map g) =
      PiTensorProduct.map (Fin.append f g) ∘ₗ TensorPower.mulEquiv.toLinearMap := by
  refine TensorProduct.ext ?_
  ext x y
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
    PiTensorProduct.map_tprod, ← TensorPower.gMul_def, TensorPower.tprod_mul_tprod]
  congr 1 with i
  refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) i <;> simp

/-- Conjugating by `TensorPower.mulEquiv` turns the tensor product of two tensor-power
endomorphisms into the tensor-power endomorphism of the appended family. -/
theorem mulEquiv_conj_map {d e : ℕ} (f : Fin d → M →ₗ[R] M) (g : Fin e → M →ₗ[R] M) :
    (TensorPower.mulEquiv (R := R) (M := M) (n := d) (m := e)).conj
        (TensorProduct.map (PiTensorProduct.map f) (PiTensorProduct.map g)) =
      PiTensorProduct.map (Fin.append f g) := by
  rw [LinearEquiv.conj_apply, mulEquiv_comp_map, LinearMap.comp_assoc,
    LinearEquiv.comp_symm, LinearMap.comp_id]

end map

end TauCeti.TensorPower

namespace TensorPower

/-- Split a tensor power after its first `k` factors. -/
noncomputable def splitAt (n k : ℕ) (hk : k ≤ n) :
    TensorPower R n M →ₗ[R] TensorPower R k M ⊗[R] TensorPower R (n - k) M :=
  (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
    (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).toLinearMap

@[simp]
theorem mulEquiv_splitAt (n k : ℕ) (hk : k ≤ n) (x : TensorPower R n M) :
    TensorPower.mulEquiv (splitAt R M n k hk x) =
      TensorPower.cast R M (Nat.add_sub_of_le hk).symm x := by
  simp [splitAt]

/-- Splitting a tensor power at a fixed position loses no information: it is the composite of two
linear equivalences. -/
theorem splitAt_injective (n k : ℕ) (hk : k ≤ n) :
    Function.Injective (splitAt R M n k hk) := by
  intro x y hxy
  have := congrArg (TensorPower.mulEquiv (R := R) (M := M)) hxy
  rw [mulEquiv_splitAt, mulEquiv_splitAt] at this
  exact (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).injective this

/-- Splitting a pure tensor separates its first `k` entries from the remaining entries. -/
@[simp]
theorem splitAt_tprod (n k : ℕ) (hk : k ≤ n) (x : Fin n → M) :
    splitAt R M n k hk (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i : Fin k ↦ x (Fin.castLE hk i)) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun j : Fin (n - k) ↦ x ⟨k + j.1, by omega⟩) := by
  apply TensorPower.mulEquiv.injective
  rw [mulEquiv_splitAt, TensorPower.cast_tprod, ← TensorPower.gMul_def,
    TensorPower.tprod_mul_tprod]
  congr 1
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i.1 < k
  · let j : Fin k := ⟨i.1, hi⟩
    have hij : Fin.castAdd (n - k) j = i := by ext; rfl
    rw [← hij, Fin.append_left]
    congr 1
  · let j : Fin (n - k) := ⟨i.1 - k, by omega⟩
    have hij : Fin.natAdd k j = i := by ext; simp [j]; omega
    rw [← hij, Fin.append_right]
    congr 1

/-- Identifying the empty left tensor block with scalars agrees with concatenation. -/
theorem lid_map_algebraMap₀_symm (n : ℕ) (z : TensorPower R 0 M ⊗[R] TensorPower R n M) :
    TensorProduct.lid R (TensorPower R n M)
      (TensorProduct.map (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap
        LinearMap.id z) =
      TensorPower.cast R M (Nat.zero_add n) (TensorPower.mulEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    obtain ⟨a, rfl⟩ := (TensorPower.algebraMap₀ (R := R) (M := M)).surjective a
    simpa only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply, TensorProduct.lid_tmul,
      ← TensorPower.gMul_def] using (TensorPower.algebraMap₀_mul a b).symm

/-- Identifying the empty right tensor block with scalars agrees with concatenation. -/
theorem rid_map_algebraMap₀_symm (n : ℕ) (z : TensorPower R n M ⊗[R] TensorPower R 0 M) :
    TensorProduct.rid R (TensorPower R n M)
      (TensorProduct.map LinearMap.id
        (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap z) =
      TensorPower.cast R M (Nat.add_zero n) (TensorPower.mulEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    obtain ⟨b, rfl⟩ := (TensorPower.algebraMap₀ (R := R) (M := M)).surjective b
    simpa only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply, TensorProduct.rid_tmul,
      ← TensorPower.gMul_def] using (TensorPower.mul_algebraMap₀ b a).symm

/-- Splitting a tensor power into three consecutive blocks is independent of the order of
the two cuts, after applying the tensor associator. -/
theorem mulEquiv_symm_assoc (p q r : ℕ) (x : TensorPower R (p + q + r) M) :
    (TensorProduct.assoc R _ _ _)
      (TensorProduct.map (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        LinearMap.id ((TensorPower.mulEquiv (R := R) (M := M)).symm x)) =
      TensorProduct.map LinearMap.id
        (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        ((TensorPower.mulEquiv (R := R) (M := M)).symm
          (TensorPower.cast R M (Nat.add_assoc p q r) x)) := by
  obtain ⟨x, rfl⟩ := (TensorPower.mulEquiv (R := R) (M := M)
    (n := p + q) (m := r)).surjective x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    obtain ⟨a, rfl⟩ := (TensorPower.mulEquiv (R := R) (M := M)
      (n := p) (m := q)).surjective a
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, TensorProduct.add_tmul, ha, hb]
    | tmul a b =>
      simp only [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
        LinearEquiv.coe_coe, LinearMap.id_apply, TensorProduct.assoc_tmul]
      rw [← TensorPower.gMul_def, ← TensorPower.gMul_def, TensorPower.mul_assoc]
      simp only [TensorPower.gMul_def, LinearEquiv.symm_apply_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]

end TensorPower
end
end TAF_LiteralSource_0381

section TAF_LiteralSource_0382
/- Original module: TauCeti.RepresentationTheory.Tensor.Power -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor powers of representations

This file equips the tensor power of a representation with its diagonal action. The action on a
pure tensor applies the original action in every factor. Concatenation of tensor factors is an
equivalence of representations, so the character of a tensor power is the corresponding power of
the character.

## Main definitions

* `Representation.tensorPower` is the diagonal action on `⨂[R]^d M`.
* `Representation.tensorPowerAddEquiv` identifies the tensor product of the `d`-th and `e`-th
  tensor-power representations with the `(d + e)`-th one.

## Main results

* `Representation.char_tensorPower`: the character of the `d`-th tensor power is the `d`-th
  power of the character.
-/

public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {G : Type v} {M : Type w}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The diagonal action of `G` on the `d`-fold tensor power of a representation. -/
noncomputable def tensorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⨂[R]^d M) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun _ : Fin d => ρ)

/-- The tensor-power action applies the original action in every tensor factor. -/
@[simp]
theorem tensorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.tensorPower d g = PiTensorProduct.map fun _ : Fin d => ρ g := by
  rfl

/-- The action on the zero-fold tensor power is the identity.

This is intentionally not a simp lemma: `tensorPower_apply` followed by
`TauCeti.PiTensorProduct.map_of_isEmpty` already performs this simplification. -/
theorem tensorPower_zero_apply (ρ : Representation R G M) (g : G) :
    ρ.tensorPower 0 g = LinearMap.id := by
  simp

/-- Splitting the factors gives an equivalence from the tensor product of two tensor-power
representations to the tensor power indexed by their sum. -/
noncomputable def tensorPowerAddEquiv (ρ : Representation R G M) (d e : ℕ) :
    ((ρ.tensorPower d).tprod (ρ.tensorPower e)).Equiv (ρ.tensorPower (d + e)) :=
  .mk TensorPower.mulEquiv fun g => by
    have h : Fin.append (fun _ : Fin d => ρ g) (fun _ : Fin e => ρ g) = fun _ => ρ g :=
      Fin.append_castAdd_natAdd (f := fun _ : Fin (d + e) => ρ g)
    simpa only [tprod_apply, tensorPower_apply, h] using
      TauCeti.TensorPower.mulEquiv_comp_map (fun _ : Fin d => ρ g) (fun _ : Fin e => ρ g)

end CommSemiring

section Field

variable [Field R] [Monoid G] [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- The character of a tensor-power representation is the corresponding power of the character. -/
@[simp]
theorem char_tensorPower (ρ : Representation R G M) (d : ℕ) (g : G) :
    (ρ.tensorPower d).character g = (ρ.character g) ^ d := by
  induction d with
  | zero =>
    rw [character, tensorPower_zero_apply, LinearMap.trace_id,
      (PiTensorProduct.isEmptyEquiv (Fin 0)).finrank_eq, Module.finrank_self, Nat.cast_one,
      pow_zero]
  | succ d ih =>
    have h_one : (ρ.tensorPower 1).character g = ρ.character g := by
      rw [character, character, ← LinearMap.trace_conj' _ (TauCeti.TensorPower.oneEquiv R M)]
      congr 1
      ext x
      simp [LinearEquiv.conj_apply]
    rw [← char_iso (ρ.tensorPowerAddEquiv d 1), char_tensor, Pi.mul_apply, ih, h_one, pow_succ]

end Field

end Representation
end
end TAF_LiteralSource_0382

section TAF_LiteralSource_0383
/- Original module: TauCeti.RepresentationTheory.MatrixCoefficients -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Representation.IntertwiningMap` occurs in the statements below, and this module supplies
-- `Representation` itself together with `Representation.tprod`.
-- `LinearMap.toMatrix` and `Module.Basis.tensorProduct` occur in the statements below, and
-- `TensorProduct.toMatrix_map` is what computes the entries of a tensor product.
-- `Basis.piTensorProduct`, the basis of pure tensors the tensor-power entries are read
-- against.
-- `Representation.tensorPower` occurs in the statements below.

/-!
# Matrix coefficients of a representation

The **matrix coefficients** of a representation `ρ` against a basis `b` of its carrier are the
functions `g ↦ LinearMap.toMatrix b b (ρ g) i j` on the group.  A property of a representation is
often expressed by asking that all of them lie in some fixed algebra `A` of functions on the group:
that they are polynomial in the entries of `g`, say, or bounded, or continuous.

This file collects the closure properties of such a condition that hold for *every* subalgebra `A`,
so that a proof of the condition never has to be repeated for each choice:

* a surjective intertwining map carries the condition from source to target, because a basis vector
  of the target lifts to a vector of the source, and the entries against the target basis are then
  fixed linear combinations of the entries against the source basis, with coefficients read off the
  lift and independent of `g`;
* changing the basis of a single representation is the special case of the identity map, so the
  condition is basis independent;
* against the basis of pure tensors of basis vectors, the matrix coefficients of a tensor power of a
  representation are the products of matrix coefficients of the representation;
* against a tensor product of bases, the matrix coefficients of a tensor product of representations
  are the products of matrix coefficients of the two factors.

All but the last need only a commutative semiring of scalars; the tensor-product entries are read
off `TensorProduct.toMatrix_map`, which Mathlib states over a commutative ring.

## Main results

* `Representation.toMatrix_mem_of_toMatrix_mem_of_surjective`: the matrix coefficients of a
  quotient representation stay inside any subalgebra containing those of the source.
* `Representation.toMatrix_mem_of_toMatrix_mem`: changing basis keeps the matrix
  coefficients inside any subalgebra.
* `Representation.toMatrix_tensorPower` and
  `Representation.toMatrix_tensorPower_mem`: the matrix coefficients of a tensor power are
  products of matrix coefficients, hence stay inside any subalgebra containing those of the
  representation.
* `Representation.toMatrix_tprod` and `Representation.toMatrix_tprod_mem`: the
  matrix coefficients of a tensor product are products of matrix coefficients, hence stay inside
  any subalgebra containing those of the two factors.
-/

public section

universe u v w x y z

namespace Representation

section CommSemiring

variable {k : Type u} [CommSemiring k] {G : Type z} [Monoid G] {W : Type v} [AddCommMonoid W]
  [Module k W]
variable {V : Type y} [AddCommMonoid V] [Module k V]

/-- **The matrix coefficients of a quotient representation stay inside any subalgebra of
functions.**  If `σ` is the image of `ρ` under a surjective intertwining map, and every matrix
coefficient of `ρ` against a basis of the source lies in a subalgebra `A` of the functions on the
group, then so does every matrix coefficient of `σ` against a basis of the target. -/
theorem toMatrix_mem_of_toMatrix_mem_of_surjective (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f)
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : κ) :
    (fun g => LinearMap.toMatrix c c (σ g) i j) ∈ A := by
  obtain ⟨w, hw⟩ := hf (c j)
  have key : (fun g => LinearMap.toMatrix c c (σ g) i j)
      = ∑ p : ι, ∑ l : ι, (b.repr w l * c.repr (f (b p)) i) •
          fun g => LinearMap.toMatrix b b (ρ g) p l := by
    funext g
    have hfg : σ g (c j) = f (ρ g w) := by
      rw [← hw]
      exact (Representation.IntertwiningMap.isIntertwining ρ σ f g w).symm
    have hexp : ∀ p, b.repr (ρ g w) p = ∑ l, b.repr w l * LinearMap.toMatrix b b (ρ g) p l := by
      intro p
      simpa [Matrix.mulVec, dotProduct, mul_comm] using
        (congr_fun (LinearMap.toMatrix_mulVec_repr b b (ρ g) w) p).symm
    rw [LinearMap.toMatrix_apply, hfg]
    conv_lhs => rw [← b.sum_repr (ρ g w)]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, hexp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [key]
  exact Subalgebra.sum_mem _ fun p _ =>
    Subalgebra.sum_mem _ fun l _ => Subalgebra.smul_mem _ (h p l) _

/-- **Changing basis keeps the matrix coefficients inside any subalgebra of functions**: if every
matrix coefficient of `ρ` against one basis lies in a subalgebra `A` of the functions on the group,
so does every matrix coefficient against any other basis. -/
theorem toMatrix_mem_of_toMatrix_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k W)
    (ρ : Representation k G W)
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : κ) :
    (fun g => LinearMap.toMatrix c c (ρ g) i j) ∈ A :=
  toMatrix_mem_of_toMatrix_mem_of_surjective A b c (.id ρ) (fun v => ⟨v, rfl⟩) h i j

/-- Against the basis of pure tensors of basis vectors, a matrix coefficient of the `d`-fold tensor
power of `ρ` is the product of the `d` matrix coefficients of `ρ` listed by the two indices. -/
theorem toMatrix_tensorPower {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k W)
    (ρ : Representation k G W) (d : ℕ) (g : G) (i j : Fin d → ι) :
    LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => b)
        (Basis.piTensorProduct fun _ : Fin d => b) (ρ.tensorPower d g) i j
      = ∏ l : Fin d, LinearMap.toMatrix b b (ρ g) (i l) (j l) := by
  rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    _root_.Representation.tensorPower_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp [LinearMap.toMatrix_apply]

/-- **The matrix coefficients of a tensor power stay inside any subalgebra of functions**
containing those of the representation. -/
theorem toMatrix_tensorPower_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k W)
    {ρ : Representation k G W} {d : ℕ}
    (h : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A) (i j : Fin d → ι) :
    (fun g => LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => b)
        (Basis.piTensorProduct fun _ : Fin d => b) (ρ.tensorPower d g) i j) ∈ A := by
  have hentry : (fun g => LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => b)
        (Basis.piTensorProduct fun _ : Fin d => b) (ρ.tensorPower d g) i j)
      = ∏ l : Fin d, fun g => LinearMap.toMatrix b b (ρ g) (i l) (j l) := by
    funext g
    simpa using toMatrix_tensorPower b ρ d g i j
  rw [hentry]
  exact prod_mem fun l _ => h (i l) (j l)

end CommSemiring

section CommRing

variable {k : Type u} [CommRing k] {G : Type z} [Monoid G] {W : Type v} [AddCommGroup W]
  [Module k W]
variable {V : Type y} [AddCommGroup V] [Module k V]

/-- Against a tensor product of bases, the matrix coefficients of a tensor product of
representations are the products of the matrix coefficients of the two factors: the Kronecker
product, read entrywise. -/
theorem toMatrix_tprod {ι : Type w} [Fintype ι] [DecidableEq ι]
    {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V} (g : G) (i j : ι × κ) :
    LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c) ((ρ.tprod σ) g) i j
      = LinearMap.toMatrix b b (ρ g) i.1 j.1 * LinearMap.toMatrix c c (σ g) i.2 j.2 := by
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  simp [Matrix.kroneckerMap_apply]

/-- **The matrix coefficients of a tensor product stay inside any subalgebra of functions**
containing those of the two factors. -/
theorem toMatrix_tprod_mem (A : Subalgebra k (G → k))
    {ι : Type w} [Fintype ι] [DecidableEq ι] {κ : Type x} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι k W) (c : Module.Basis κ k V)
    {ρ : Representation k G W} {σ : Representation k G V}
    (hb : ∀ p l, (fun g => LinearMap.toMatrix b b (ρ g) p l) ∈ A)
    (hc : ∀ p l, (fun g => LinearMap.toMatrix c c (σ g) p l) ∈ A) (i j : ι × κ) :
    (fun g => LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c) ((ρ.tprod σ) g) i j)
      ∈ A := by
  have hentry : (fun g => LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c)
        ((ρ.tprod σ) g) i j)
      = (fun g => LinearMap.toMatrix b b (ρ g) i.1 j.1) *
        fun g => LinearMap.toMatrix c c (σ g) i.2 j.2 :=
    funext fun g => toMatrix_tprod b c g i j
  rw [hentry]
  exact mul_mem (hb i.1 j.1) (hc i.2 j.2)

end CommRing

end Representation
end
end TAF_LiteralSource_0383

section TAF_LiteralSource_0384
/- Original module: TauCeti.LinearAlgebra.ExteriorPower.Basis -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Action and trace formulas in exterior-power bases

A basis of a module induces a basis of each exterior power, indexed by subsets of the basis
indices. An endomorphism diagonal in the original basis acts diagonally in this exterior-power
basis, with eigenvalues given by products over the indexing subsets. Their sum is the trace.

A basis indexed by `Fin n` identifies the degree-`n` exterior power with the scalars by sending an
exterior product to its determinant against that basis. The induced endomorphism acts by its
determinant in this degree. These formulas hold over every commutative ring, including the zero
ring. When the ring is nontrivial, `n` is the module's rank and this is its top exterior power.

## Main definitions

* `Module.Basis.exteriorPowerTopEquiv` identifies the degree-`n` exterior power with the scalars
  for a basis indexed by `Fin n`.

## Main results

* `Module.Basis.toMatrix_exteriorPower_map` expresses the induced matrix in terms of minors.
* `RingHom.map_toMatrix_exteriorPower` changes the coefficient ring of the induced matrix.
* `Module.Basis.map_exteriorPower_of_apply` gives the eigenvalues in the exterior-power basis.
* `Module.Basis.trace_map_exteriorPower_of_apply` sums those eigenvalues to compute the trace.
* `Module.Basis.exteriorPower_ιMulti_eq_det_smul` expands a degree-`n` exterior product in terms
  of the wedge of a basis indexed by `Fin n`.
* `Module.Basis.map_exteriorPower_top_eq_det_smul` gives the degree-`n` action as its determinant
  for a basis indexed by `Fin n`.
* `LinearMap.map_exteriorPower_finrank_eq_det_smul` gives the action in degree `Module.finrank`
  as its determinant.
* `Module.Basis.trace_map_exteriorPower_top` gives the degree-`n` trace as the determinant
  for a basis indexed by `Fin n`.

## References

The results use Mathlib's exterior-power basis from `Mathlib.LinearAlgebra.ExteriorPower.Basis`,
by Sophie Morel and Daniel Morrison, and the determinant of a family against a basis from
`Mathlib.LinearAlgebra.Determinant`.
-/

public section

open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Diagonal

variable [CommRing R]
variable {I : Type*} [LinearOrder I]
variable [AddCommGroup M] [Module R M]

/-- **An endomorphism diagonal in a basis is diagonal in the induced basis of the exterior
power**: the basis vector indexed by the `d`-element subset `s` is an eigenvector, with eigenvalue
the product of the eigenvalues indexed by `s`. Summing those eigenvalues over all `s` gives the
trace, `Module.Basis.trace_map_exteriorPower_of_apply`. -/
theorem _root_.Module.Basis.map_exteriorPower_of_apply (b : Module.Basis I R M) (f : M →ₗ[R] M)
    (a : I → R) (hf : ∀ i, f (b i) = a i • b i) (d : ℕ) (s : Set.powersetCard I d) :
    map d f (b.exteriorPower d s) = (∏ i ∈ (s : Finset I), a i) • b.exteriorPower d s := by
  have hprod : ∏ j : Fin d, a (Set.powersetCard.ofFinEmbEquiv.symm s j)
      = ∏ i ∈ (s : Finset I), a i := by
    rw [← Finset.prod_coe_sort s.1 a]
    apply Fintype.prod_equiv (s.1.orderIsoOfFin s.2).toEquiv
    intro j
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact congrArg a (Finset.coe_orderIsoOfFin_apply s.1 s.2 j)
  have hfun :
      (f ∘ b) ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
        fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j) •
          b (Set.powersetCard.ofFinEmbEquiv.symm s j) := by
    funext j
    simp only [Function.comp_apply, hf]
  rw [basis_apply, map_apply_ιMulti_family, ιMulti_family, ιMulti_family, hfun, ← hprod]
  simpa only [Function.comp_def] using
    (ιMulti R d).map_smul_univ (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j))
      (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm s j))

end Diagonal

section Trace

variable [CommRing R]
variable {I : Type*} [Fintype I]
variable [AddCommGroup M] [Module R M]

/-- If an endomorphism is diagonal in a finite basis, then its trace on the `d`th exterior
power is the `d`th elementary symmetric sum of its eigenvalues. -/
theorem _root_.Module.Basis.trace_map_exteriorPower_of_apply (b : Module.Basis I R M)
    (f : M →ₗ[R] M)
    (a : I → R) (d : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (⋀[R]^d M) (map d f) =
      ∑ s : Set.powersetCard I d, ∏ i ∈ (s : Finset I), a i := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower d), Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    b.map_exteriorPower_of_apply f a hf d s, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

end Trace

section Top

variable [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- Given a basis indexed by `Fin n`, an exterior product of `n` vectors is the determinant of
that family against the basis, times the exterior product of the basis. -/
theorem _root_.Module.Basis.exteriorPower_ιMulti_eq_det_smul (b : Module.Basis (Fin n) R M)
    (v : Fin n → M) :
    ιMulti R n v = b.det v • ιMulti R n ⇑b := by
  -- Compare both sides coordinatewise in the basis of `⋀[R]^n M` induced by `b`: each coordinate
  -- is an `R`-valued alternating form, hence a multiple of `b.det`.
  refine (b.exteriorPower n).ext_elem fun s ↦ ?_
  -- The `s`th coordinate of `ιMulti R n v` is an alternating form in `v`.
  set φ : M [⋀^Fin n]→ₗ[R] R := (ιMultiDual R n b s).compAlternatingMap (ιMulti R n) with hφ
  have hφ_apply (w : Fin n → M) :
      φ w = (b.exteriorPower n).repr (ιMulti R n w) s := by
    rw [hφ, basis_repr_apply, LinearMap.compAlternatingMap_apply]
  have hdet : φ = φ ⇑b • b.det := φ.eq_smul_basis_det b
  calc (b.exteriorPower n).repr (ιMulti R n v) s
      = φ v := (hφ_apply v).symm
    _ = φ ⇑b * b.det v := by rw [hdet]; simp [Module.Basis.det_self]
    _ = b.det v * (b.exteriorPower n).repr (ιMulti R n ⇑b) s := by
        rw [← hφ_apply ⇑b, mul_comm]
    _ = (b.exteriorPower n).repr (b.det v • ιMulti R n ⇑b) s := by simp

/-- For a basis indexed by `Fin n`, an endomorphism acts on the degree-`n` exterior power as
multiplication by its determinant. -/
theorem _root_.Module.Basis.map_exteriorPower_top_eq_det_smul (b : Module.Basis (Fin n) R M)
    (f : M →ₗ[R] M) :
    map n f = LinearMap.det f • LinearMap.id := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  rw [map_apply_ιMulti, b.exteriorPower_ιMulti_eq_det_smul (f ∘ v),
    b.exteriorPower_ιMulti_eq_det_smul v, Module.Basis.det_comp, mul_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]

/-- The basis-free form of `Module.Basis.map_exteriorPower_top_eq_det_smul`: an endomorphism of a
free module acts on the exterior power in degree `Module.finrank R M` by its determinant.
For a nonfinite module over a nontrivial ring, this is the identity in degree zero. -/
@[simp]
theorem _root_.LinearMap.map_exteriorPower_finrank_eq_det_smul
    [Module.Free R M]
    (f : M →ₗ[R] M) :
    map (Module.finrank R M) f = LinearMap.det f • LinearMap.id := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R (⋀[R]^(Module.finrank R M) M)
    exact Subsingleton.elim _ _
  · classical
    by_cases h : Module.Finite R M
    · have := h
      exact (Module.finBasis R M).map_exteriorPower_top_eq_det_smul f
    · rw [Module.finrank_of_not_finite h, LinearMap.det_eq_one_of_not_module_finite h f,
        one_smul]
      exact (LinearMap.cancel_left (zeroEquiv R M).injective).mp
        (by simpa only [LinearMap.comp_id] using zeroEquiv_naturality f)

/-- A basis indexed by `Fin n` identifies the degree-`n` exterior power with the scalars by
sending an exterior product of vectors to their determinant against the basis. -/
noncomputable def _root_.Module.Basis.exteriorPowerTopEquiv (b : Module.Basis (Fin n) R M) :
    ⋀[R]^n M ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R (⋀[R]^n M) (ιMulti R n ⇑b))
    (by
      ext
      simp [Module.Basis.det_self])
    (by
      refine LinearMap.ext_on (ιMulti_span R n M) ?_
      rintro _ ⟨v, rfl⟩
      simp [b.exteriorPower_ιMulti_eq_det_smul v, Module.Basis.det_self])

/-- The identification for a basis indexed by `Fin n` sends an exterior product to its determinant
against the basis. -/
@[simp]
lemma _root_.Module.Basis.exteriorPowerTopEquiv_apply_ιMulti (b : Module.Basis (Fin n) R M)
    (v : Fin n → M) :
    b.exteriorPowerTopEquiv (ιMulti R n v) = b.det v := by
  simp [Module.Basis.exteriorPowerTopEquiv]

/-- The inverse identification sends a scalar to that multiple of the basis wedge. -/
@[simp]
lemma _root_.Module.Basis.exteriorPowerTopEquiv_symm_apply (b : Module.Basis (Fin n) R M) (r : R) :
    b.exteriorPowerTopEquiv.symm r = r • ιMulti R n ⇑b := by
  simp [Module.Basis.exteriorPowerTopEquiv]

/-- For a basis indexed by `Fin n`, the trace of the induced endomorphism on the degree-`n`
exterior power is the determinant. -/
theorem _root_.Module.Basis.trace_map_exteriorPower_top
    (b : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) :
    LinearMap.trace R (⋀[R]^n M) (map n f) = LinearMap.det f := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · have := Module.Free.of_basis b
    have := Module.Finite.of_basis b
    -- The top exterior power is one-dimensional, the diagonal case `Nat.choose n n = 1`.
    rw [b.map_exteriorPower_top_eq_det_smul f, map_smul, LinearMap.trace_id, finrank_eq,
      Module.finrank_eq_card_basis b, Fintype.card_fin, Nat.choose_self]
    simp

end Top

end exteriorPower

namespace Module.Basis

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I] [Fintype I]

/-- The matrix of an exterior-power map consists of the corresponding minors. -/
@[simp]
theorem toMatrix_exteriorPower_map (b : Basis I R M) (n : ℕ) (f : M →ₗ[R] M)
    (s t : Set.powersetCard I n) :
    LinearMap.toMatrix (b.exteriorPower n) (b.exteriorPower n) (exteriorPower.map n f) s t =
      (Matrix.of fun i j : Fin n ↦
        LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (Set.powersetCard.ofFinEmbEquiv.symm t i)).det := by
  simp [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Basis.coord_apply]

end Module.Basis

namespace RingHom

variable {R S I : Type*} [CommRing R] [CommRing S] [LinearOrder I] [Fintype I]

/-- Exterior-power matrices commute with a change of coefficient ring. -/
theorem map_toMatrix_exteriorPower (φ : R →+* S) (n : ℕ) (A : Matrix I I R) :
    φ.mapMatrix (LinearMap.toMatrix ((Pi.basisFun R I).exteriorPower n)
      ((Pi.basisFun R I).exteriorPower n) (exteriorPower.map n A.toLin')) =
    LinearMap.toMatrix ((Pi.basisFun S I).exteriorPower n)
      ((Pi.basisFun S I).exteriorPower n) (exteriorPower.map n (φ.mapMatrix A).toLin') := by
  classical
  ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    Module.Basis.toMatrix_exteriorPower_map, Module.Basis.toMatrix_exteriorPower_map]
  simp only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [RingHom.map_det]
  rfl

end RingHom
end
end TAF_LiteralSource_0384

section TAF_LiteralSource_0385
/- Original module: TauCeti.LinearAlgebra.End.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic facts about module endomorphisms

A nontrivial endomorphism semiring forces the underlying module to be nontrivial. Together with
Mathlib's converse instance, this identifies nontriviality on the two sides without assumptions on
the endomorphism semiring beyond nontriviality itself.

A vector on which every endomorphism of a list acts by the same scalar `z` is acted on by their
product through `z ^ l.length` (`Module.End.list_prod_apply_eq_pow_smul`).

An endomorphism of a torsion-free module over a domain some power of which is a scalar other than
one has no nonzero fixed vectors (`TauCeti.injective_one_sub_of_pow_eq_smul_one`).
-/

public section

namespace TauCeti

/-- A module with nontrivial endomorphism semiring is nontrivial. -/
theorem nontrivial_of_nontrivial_end {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial (Module.End R M)] : Nontrivial M := by
  have : Nontrivial (M → M) := (DFunLike.coe_injective (F := Module.End R M)).nontrivial
  exact Function.nontrivial_of_nontrivial M M

/-- **`1 - φ` is injective when a power of `φ` is a scalar other than one**, for an endomorphism
of a torsion-free module over a domain. If `φ v = v` then `m • v = φ ^ n v = v`, so
`(1 - m) • v = 0` and `v = 0`. For the character map `φ` of a Steinberg endomorphism some power of
`φ` is `q • 1` with `q` a power of the characteristic. The hypothesis `m ≠ 1` cannot be dropped:
`φ = 1` satisfies `φ ^ 1 = 1 • 1`. -/
theorem injective_one_sub_of_pow_eq_smul_one {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M] {φ : Module.End A M} {n : ℕ} {m : A}
    (h : φ ^ n = m • 1) (hm : m ≠ 1) : Function.Injective ⇑(1 - φ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  -- `1 - φ ^ n = (∑ i < n, φ ^ i) * (1 - φ)` kills `v`, and it is multiplication by `1 - m`.
  have hn : (1 - φ ^ n) v = 0 := by
    rw [← geom_sum_mul_neg, Module.End.mul_apply, hv, map_zero]
  have hmv : (1 - m) • v = 0 := by
    rw [sub_smul, one_smul]
    simpa [h] using hn
  exact (smul_eq_zero.mp hmv).resolve_left (sub_ne_zero.mpr hm.symm)

end TauCeti

namespace Module.End

/-- A product of endomorphisms each of which acts on `s` by the scalar `z` acts on `s` by
`z ^ l.length`. -/
theorem list_prod_apply_eq_pow_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {l : List (Module.End R M)} {z : R} {s : M} (h : ∀ a ∈ l, a s = z • s) :
    l.prod s = z ^ l.length • s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih fun a ha ↦ h a (List.mem_cons_of_mem _ ha),
      map_smul, h a List.mem_cons_self, smul_smul, List.length_cons, pow_succ]

end Module.End
end
end TAF_LiteralSource_0385

section TAF_LiteralSource_0386
/- Original module: TauCeti.RingTheory.LocalRing.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic facts about local rings

This file records basic facts about possibly noncommutative local rings. Their only idempotents
are `0` and `1`; this fact applies to endomorphism rings in the Krull-Schmidt theorem. In
characteristic two the idempotent criterion identifies the zeros of the Artin–Schreier map
`t ↦ t² + t`, without a finiteness assumption.

## Main results

* `IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing`: an idempotent of a local ring is `0`
  or `1`.
* `TauCeti.IsLocalRing.isDedekindFiniteMonoid`: a local ring is Dedekind-finite.
* `TauCeti.isUnit_add_of_isUnit_of_not_isUnit`: adding a nonunit to a unit in a local ring
  yields a unit.
* `TauCeti.isUnit_sub_of_not_isUnit_of_isUnit`: subtracting a unit from a nonunit in a local ring
  yields a unit.
* `TauCeti.IsLocalRing.sq_add_self_eq_zero_iff`: in characteristic two, `t² + t = 0` exactly
  when `t = 0` or `t = 1`.
* `Nat.Coprime.isUnit_natCast`: if a natural number is not a unit, every coprime natural
  number is a unit.
* `IsCoprime.isUnit_or_isUnit`: of two coprime elements of a commutative local semiring, one is a
  unit.
* `IsLocalRing.sub_one_mem_maximalIdeal_of_card_residueField_eq_two`: when the residue field has
  two elements, every unit is congruent to `1` modulo the maximal ideal, and
  `IsLocalRing.two_mem_maximalIdeal_of_card_residueField_eq_two`: `2` lies in the maximal ideal.
-/

public section

/-- An idempotent of a possibly noncommutative local ring is `0` or `1`. -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  -- One of `a` and `1 - a` is a unit, and an idempotent unit is `1`.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha.one_sub))

namespace TauCeti

/-- A local ring is Dedekind-finite: a left inverse is also a right inverse. -/
instance IsLocalRing.isDedekindFiniteMonoid {R : Type*} [Ring R] [IsLocalRing R] :
    IsDedekindFiniteMonoid R where
  mul_eq_one_symm := by
    intro p q hpq
    have he : IsIdempotentElem (q * p) := by
      rw [IsIdempotentElem]
      calc
        (q * p) * (q * p) = q * (p * q) * p := by simp only [mul_assoc]
        _ = q * p := by rw [hpq, mul_one]
    rcases IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing he with h0 | h1
    · exfalso
      exact one_ne_zero (by
        simpa only [mul_assoc, hpq, mul_one, mul_zero, zero_mul] using
          congrArg (fun a ↦ p * a * q) h0)
    · exact h1

/-- In a local ring, adding a nonunit to a unit yields a unit. -/
theorem isUnit_add_of_isUnit_of_not_isUnit {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : ¬ IsUnit b) : IsUnit (a + b) := by
  by_contra hab
  have hsum := IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hab)
    (mem_nonunits_iff.mpr ((IsUnit.neg_iff b).not.mpr hb))
  have ha' : a ∈ nonunits R := by
    simpa only [add_assoc, add_neg_cancel, add_zero] using hsum
  exact (mem_nonunits_iff.mp ha') ha

/-- In a local ring, subtracting a unit from a nonunit yields a unit. -/
theorem isUnit_sub_of_not_isUnit_of_isUnit {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (ha : ¬ IsUnit a) (hb : IsUnit b) : IsUnit (a - b) := by
  have h := isUnit_add_of_isUnit_of_not_isUnit hb
    ((IsUnit.neg_iff a).not.mpr ha)
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg] using h.neg

/-- Over a local ring of characteristic two, the zeros of `t ↦ t² + t` are `0` and `1`. -/
@[simp]
theorem IsLocalRing.sq_add_self_eq_zero_iff {R : Type*} [Ring R] [IsLocalRing R] [CharP R 2]
    (t : R) : t ^ 2 + t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [CharTwo.add_eq_zero, pow_two]
  constructor
  · exact IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing
  · rintro (rfl | rfl) <;> simp

end TauCeti

/-- Of two coprime elements of a commutative local semiring, one is a unit: a relation
`u * a + v * b = 1` makes one of the two summands a unit. -/
theorem IsCoprime.isUnit_or_isUnit {R : Type*} [CommSemiring R] [IsLocalRing R] {a b : R}
    (h : IsCoprime a b) : IsUnit a ∨ IsUnit b := by
  obtain ⟨u, v, huv⟩ := h
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one huv).imp isUnit_of_mul_isUnit_right
    isUnit_of_mul_isUnit_right

/-- In a possibly noncommutative local ring, a natural number coprime to a nonunit natural
number is a unit. -/
theorem Nat.Coprime.isUnit_natCast {R : Type*} [Ring R] [IsLocalRing R] {m n : ℕ}
    (h : m.Coprime n) (hn : ¬IsUnit (n : R)) : IsUnit (m : R) := by
  have hab := Nat.gcd_eq_gcd_ab m n
  rw [h.gcd_eq_one, Nat.cast_one] at hab
  have hab' : (m : R) * (m.gcdA n : R) + n * (m.gcdB n : R) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → R) hab.symm
  exact ((IsLocalRing.isUnit_or_isUnit_of_add_one hab').imp isUnit_of_mul_isUnit_left
    isUnit_of_mul_isUnit_left).resolve_right hn

/-- When the residue field of a commutative local ring has two elements, every unit is congruent
to `1` modulo the maximal ideal: its residue is a nonzero element of `𝔽₂`. -/
theorem IsLocalRing.sub_one_mem_maximalIdeal_of_card_residueField_eq_two {R : Type*} [CommRing R]
    [IsLocalRing R] (hR : Nat.card (IsLocalRing.ResidueField R) = 2) {u : R} (hu : IsUnit u) :
    u - 1 ∈ IsLocalRing.maximalIdeal R := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : IsLocalRing.ResidueField R)).mp hR
  rw [hy _ ((IsLocalRing.residue_ne_zero_iff_isUnit u).mpr hu), hy 1 one_ne_zero]

/-- When the residue field of a commutative local ring has two elements, `2` lies in the maximal
ideal: the residue field has characteristic two. -/
theorem IsLocalRing.two_mem_maximalIdeal_of_card_residueField_eq_two {R : Type*} [CommRing R]
    [IsLocalRing R] (hR : Nat.card (IsLocalRing.ResidueField R) = 2) :
    (2 : R) ∈ IsLocalRing.maximalIdeal R := by
  have h := (IsLocalRing.maximalIdeal R).neg_mem
    (IsLocalRing.sub_one_mem_maximalIdeal_of_card_residueField_eq_two hR isUnit_one.neg)
  rwa [show -(-1 - 1 : R) = 2 by ring] at h
end
end TAF_LiteralSource_0386

section TAF_LiteralSource_0387
/- Original module: TauCeti.RingTheory.KrullSchmidt.Indecomposable -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Indecomposable modules and Fitting's lemma

A module is *indecomposable* when it is nonzero and is not the internal direct sum of two nonzero
submodules. This file introduces the predicate, records its idempotent reformulation, and proves
**Fitting's lemma**: an endomorphism of an indecomposable module of finite length is either
nilpotent or bijective, so the endomorphism ring of such a module is local.

Mathlib has the Fitting *decomposition* of an endomorphism of a Noetherian and Artinian module
(`LinearMap.eventually_isCompl_ker_pow_range_pow`) and `CategoryTheory.Indecomposable` for objects
of a category with binary biproducts, but no module-level indecomposability predicate and no
local-endomorphism-ring theorem. Both are supplied here.

## Main definitions

* `TauCeti.IsIndecomposableModule A M`: `M` is a nonzero `A`-module admitting no decomposition
  `M = N ⊕ P` with `N` and `P` both nonzero.

## Main results

* `TauCeti.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem`: indecomposability
  says exactly that `M` is nontrivial and `0` and `1` are the only idempotents of `Module.End A M`.
* `TauCeti.isIndecomposableModule_iff_isIndecomposableModule_of_algebraMap_surjective`:
  indecomposability is unchanged by restricting scalars along a surjective algebra map.
* `TauCeti.IsIndecomposableModule.bijective_of_bijective_comp`: a split injection into an
  indecomposable module is an isomorphism, that is, if `g ∘ₗ f` is bijective and the module `f`
  lands in is indecomposable, then `f` is bijective.
* `TauCeti.IsIndecomposableModule.isNilpotent_or_bijective`: **Fitting's lemma**, for a module that
  is Noetherian and Artinian, together with
  `TauCeti.IsIndecomposableModule.isNilpotent_iff_not_isUnit`, which reads it as an identification
  of the non-units of the endomorphism ring with its nilpotents.
* `TauCeti.isLocalRing_end_of_isIndecomposable`: the endomorphism ring of an indecomposable module
  of finite length is local.
* `TauCeti.isIndecomposableModule_iff_isLocalRing_end`: for a module of finite length the converse
  holds too, so indecomposability is *equivalent* to having a local endomorphism ring.
* `TauCeti.isIndecomposableModule_self`: a local semiring is indecomposable over itself, and
  `TauCeti.isLocalRing_of_isIndecomposableModule_self` the converse for a ring of finite length
  over itself; `TauCeti.isIndecomposableModule_self_iff` reads indecomposability of a ring over
  itself off its idempotents.
* `TauCeti.IsIndecomposableModule.nonempty_linearEquiv_of_free`: an indecomposable free module is
  isomorphic to the scalar semiring.

## Implementation notes

`IsIndecomposableModule`, its two projections, its transport along a semilinear equivalence, and
restriction of scalars along a surjection are stated for a semimodule over a semiring, since the
submodule lattice and its order isomorphisms need no subtraction. So are the free-module theorem
and `isIndecomposableModule_self` for local semirings. The idempotent, splitting, and Fitting
results are stated over a ring, where Mathlib puts the tools they use:
`LinearMap.IsIdempotentElem.isCompl` and `Submodule.projection` build a projection by subtracting,
and `IsSimpleModule` is itself only defined for modules over a ring.

The finiteness hypothesis is carried as the pair of instances `[IsNoetherian A M] [IsArtinian A M]`
on the lemmas that consume it, which is what Mathlib's Fitting decomposition asks for. The
`IsFiniteLength A M` spelling appears on the headline statements
`isLocalRing_end_of_isIndecomposable` and `isIndecomposableModule_iff_isLocalRing_end`, which
unpack it through `isFiniteLength_iff_isNoetherian_isArtinian`.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v w

section Semiring

variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]

/-- A module is **indecomposable** when it is nonzero and is not the internal direct sum of two
nonzero submodules. -/
def IsIndecomposableModule : Prop :=
  Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥

variable {A M}

/-- `IsIndecomposableModule` restated as the conjunction defining it, so that clients can
establish and consume it without unfolding the definition. -/
theorem isIndecomposableModule_iff_nontrivial_and_forall_isCompl :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥ :=
  Iff.rfl

/-- A nontrivial module along none of whose decompositions `M = N ⊕ P` both summands are nonzero is
indecomposable. -/
theorem isIndecomposableModule_of_forall_isCompl [Nontrivial M]
    (h : ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥) : IsIndecomposableModule A M :=
  ⟨‹_›, h⟩

theorem IsIndecomposableModule.nontrivial (h : IsIndecomposableModule A M) : Nontrivial M := h.1

theorem IsIndecomposableModule.eq_bot_or_eq_bot (h : IsIndecomposableModule A M)
    {N P : Submodule A M} (hNP : IsCompl N P) : N = ⊥ ∨ P = ⊥ :=
  h.2 N P hNP

/-- Indecomposability transfers along a semilinear equivalence over mutually inverse scalar
homomorphisms. -/
theorem IsIndecomposableModule.of_linearEquiv {B : Type*} [Semiring B]
    {σ : A →+* B} {τ : B →+* A} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    {N : Type w} [AddCommMonoid N] [Module B N]
    (h : IsIndecomposableModule A M) (e : M ≃ₛₗ[σ] N) : IsIndecomposableModule B N := by
  have := h.nontrivial
  refine ⟨e.symm.toEquiv.nontrivial, fun P Q hPQ ↦ ?_⟩
  simpa using h.eq_bot_or_eq_bot ((Submodule.orderIsoMapComap e.symm).isCompl hPQ)

/-! ### Restriction of scalars along a surjection -/

/-- **Indecomposability is insensitive to restriction of scalars along a surjection**: when
`algebraMap R A` is surjective, the `R`-submodules and the `A`-submodules of `M` are the same, so
`M` is indecomposable over `R` exactly when it is over `A`. -/
theorem isIndecomposableModule_iff_isIndecomposableModule_of_algebraMap_surjective
    {R : Type*} [CommSemiring R] [Algebra R A] [Module R M] [IsScalarTower R A M]
    (h : Function.Surjective (algebraMap R A)) :
    IsIndecomposableModule R M ↔ IsIndecomposableModule A M := by
  have : RingHomSurjective (algebraMap R A) := ⟨h⟩
  -- The identity on `M` is semilinear for the surjective algebra map.
  let f : M →ₛₗ[algebraMap R A] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ (algebraMap_smul A _ _).symm }
  let e := (Submodule.orderIsoMapComapOfBijective f Function.bijective_id).symm
  refine and_congr_right fun _ ↦ ⟨fun hR N P hNP ↦ ?_, fun hA N P hNP ↦ ?_⟩
  · simpa using hR (e N) (e P) (e.isCompl hNP)
  · simpa using hA (e.symm N) (e.symm P) (e.symm.isCompl hNP)

/-! ### Indecomposable local semirings -/

variable (A) in
/-- **A local semiring is indecomposable as a left module over itself**: if two left ideals sum
to the whole semiring, one contains a unit and hence is the whole semiring. -/
theorem isIndecomposableModule_self [IsLocalRing A] : IsIndecomposableModule A A := by
  refine isIndecomposableModule_of_forall_isCompl fun N P hNP ↦ ?_
  have hsum : (1 : A) ∈ N ⊔ P := by simp [hNP.sup_eq_top]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsum
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hua | hub
  · have hN : N = ⊤ := Ideal.eq_top_of_isUnit_mem N ha hua
    exact Or.inr (by simpa [hN] using hNP.disjoint)
  · have hP : P = ⊤ := Ideal.eq_top_of_isUnit_mem P hb hub
    exact Or.inl (by simpa [hP] using hNP.disjoint)

end Semiring

section Ring

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

/-! ### Indecomposability through idempotent endomorphisms -/

/-- The idempotent endomorphisms of an indecomposable module are `0` and `1`: an idempotent splits
the module as the direct sum of its range and its kernel, and one of the two must vanish. -/
theorem IsIndecomposableModule.eq_zero_or_eq_one_of_isIdempotentElem
    (h : IsIndecomposableModule A M) {f : Module.End A M} (hf : IsIdempotentElem f) :
    f = 0 ∨ f = 1 := by
  rcases h.eq_bot_or_eq_bot (LinearMap.IsIdempotentElem.isCompl hf) with hrange | hker
  · exact Or.inl (LinearMap.range_eq_bot.mp hrange)
  · refine Or.inr (LinearMap.ext fun x ↦ ?_)
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    have hx : f (f x) = f x := DFunLike.congr_fun hf x
    simpa using hinj hx

/-- A nonzero module whose only idempotent endomorphisms are `0` and `1` is indecomposable: a
decomposition `M = N ⊕ P` is witnessed by the projection onto `N` along `P`. -/
theorem isIndecomposableModule_of_forall_isIdempotentElem [Nontrivial M]
    (h : ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1) :
    IsIndecomposableModule A M := by
  refine isIndecomposableModule_of_forall_isCompl fun N P hNP ↦ ?_
  rcases h (N.projection P hNP) (Submodule.isIdempotentElem_projection hNP) with h₀ | h₁
  · exact Or.inl (by simpa [h₀] using (Submodule.range_projection hNP).symm)
  · exact Or.inr (by simpa [h₁, Module.End.one_eq_id] using (Submodule.ker_projection hNP).symm)

/-- Indecomposability of a module is exactly the statement that it is nontrivial and its
endomorphism ring has no idempotents besides `0` and `1`. -/
theorem isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1 :=
  ⟨fun h ↦ ⟨h.nontrivial, fun _ hf ↦ h.eq_zero_or_eq_one_of_isIdempotentElem hf⟩,
    fun ⟨_, h⟩ ↦ isIndecomposableModule_of_forall_isIdempotentElem h⟩

/-- A simple module is indecomposable: it has no proper nonzero submodule to decompose along. -/
theorem IsSimpleModule.isIndecomposableModule [IsSimpleModule A M] :
    IsIndecomposableModule A M := by
  refine ⟨IsSimpleModule.nontrivial A M, fun N P hNP ↦ ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · exact Or.inl hN
  · refine Or.inr ?_
    have hdisj : Disjoint (⊤ : Submodule A M) P := hN ▸ hNP.disjoint
    simpa using hdisj

/-- An indecomposable semisimple module is simple. -/
theorem IsIndecomposableModule.isSimpleModule [IsSemisimpleModule A M]
    (h : IsIndecomposableModule A M) : IsSimpleModule A M := by
  have := h.nontrivial
  refine (isSimpleModule_iff A M).mpr ⟨fun N ↦ ?_⟩
  obtain ⟨P, hNP⟩ := exists_isCompl N
  rcases h.eq_bot_or_eq_bot hNP with hN | hP
  · exact Or.inl hN
  · exact Or.inr (by simpa [hP] using hNP.sup_eq_top)

/-! ### Splitting off an indecomposable module -/

/-- If `N` is nontrivial, `P` is indecomposable, and `g ∘ₗ f` is bijective for linear maps
`f : N →ₗ[A] P` and `g : P →ₗ[A] N`, then `f` is bijective. -/
theorem IsIndecomposableModule.bijective_of_bijective_comp {N P : Type*}
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] [Nontrivial N]
    (hP : IsIndecomposableModule A P) {f : N →ₗ[A] P} {g : P →ₗ[A] N}
    (h : Function.Bijective (g ∘ₗ f)) : Function.Bijective f := by
  let u := LinearEquiv.ofBijective (g ∘ₗ f) h
  have hinj : Function.Injective f := Function.Injective.of_comp (f := g) (g := f) h.1
  let p := f.rangeRestrict ∘ₗ u.symm.toLinearMap ∘ₗ g
  have hcompl : IsCompl f.range p.ker := LinearMap.isCompl_of_proj (f := p) (by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    exact congrArg f (u.symm_apply_apply x))
  have hker := (hP.eq_bot_or_eq_bot hcompl).resolve_left fun hf ↦
    LinearMap.ne_zero_of_injective hinj (LinearMap.range_eq_bot.mp hf)
  refine ⟨hinj, LinearMap.range_eq_top.mp ?_⟩
  simpa [hker] using hcompl.sup_eq_top

/-! ### Fitting's lemma -/

section Fitting

variable [IsNoetherian A M] [IsArtinian A M]

/-- **Fitting's lemma**: an endomorphism of an indecomposable module that is both Noetherian and
Artinian is either nilpotent or bijective.

For a large enough exponent `m`, Mathlib's Fitting decomposition splits `M` as
`ker (f ^ m) ⊕ range (f ^ m)`. Indecomposability collapses one of the two summands: if the range
vanishes then `f ^ m = 0`, and if the kernel vanishes then `f` is injective while the range, being
everything, forces `f` to be surjective. -/
theorem IsIndecomposableModule.isNilpotent_or_bijective (h : IsIndecomposableModule A M)
    (f : Module.End A M) : IsNilpotent f ∨ Function.Bijective f := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  -- The exponent `n + 1` is positive, so `f` itself inherits injectivity and surjectivity from
  -- `f ^ (n + 1)`; the threshold `n` alone could be `0`, where the decomposition says nothing.
  have hcompl := hn (n + 1) (Nat.le_succ n)
  rcases h.eq_bot_or_eq_bot hcompl with hker | hrange
  · apply Or.inr
    rw [← Module.End.isUnit_iff, ← isUnit_pow_succ_iff (n := n), Module.End.isUnit_iff]
    refine ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp ?_⟩
    simpa [hker] using hcompl.sup_eq_top
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩

/-- **Fitting's lemma**, restated: an endomorphism of an indecomposable module that is both
Noetherian and Artinian is either nilpotent or a unit of the endomorphism ring. -/
theorem IsIndecomposableModule.isNilpotent_or_isUnit (h : IsIndecomposableModule A M)
    (f : Module.End A M) : IsNilpotent f ∨ IsUnit f :=
  (h.isNilpotent_or_bijective f).imp id (Module.End.isUnit_iff f).mpr

/-- On an indecomposable module that is Noetherian and Artinian, the non-units of the endomorphism
ring are exactly the nilpotent endomorphisms. This identifies the maximal ideal produced by
`TauCeti.isLocalRing_end_of_isIndecomposable`. -/
theorem IsIndecomposableModule.isNilpotent_iff_not_isUnit (h : IsIndecomposableModule A M)
    (f : Module.End A M) : IsNilpotent f ↔ ¬ IsUnit f := by
  have := h.nontrivial
  exact ⟨IsNilpotent.not_isUnit, (h.isNilpotent_or_isUnit f).resolve_right⟩

end Fitting

/-! ### Local endomorphism rings -/

/-- The endomorphism ring of an indecomposable module of finite length is **local**.

This is the form of Fitting's lemma that drives the Krull-Schmidt theorem: a non-unit endomorphism
is nilpotent, and `1 - f` is then a unit. -/
theorem isLocalRing_end_of_isIndecomposable (hM : IsFiniteLength A M)
    (h : IsIndecomposableModule A M) : IsLocalRing (Module.End A M) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have := h.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  exact (h.isNilpotent_or_isUnit f).symm.imp id IsNilpotent.isUnit_one_sub

/-- A module with local endomorphism ring is indecomposable. This is the converse of
`TauCeti.isLocalRing_end_of_isIndecomposable`, and needs no finiteness hypothesis; nontriviality
comes for free, by `TauCeti.nontrivial_of_nontrivial_end`. -/
theorem isIndecomposableModule_of_isLocalRing_end [IsLocalRing (Module.End A M)] :
    IsIndecomposableModule A M :=
  have := nontrivial_of_nontrivial_end (R := A) (M := M)
  isIndecomposableModule_of_forall_isIdempotentElem fun _ hf ↦
    IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing hf

/-- For a module of finite length, indecomposability is **equivalent** to having a local
endomorphism ring. -/
theorem isIndecomposableModule_iff_isLocalRing_end (hM : IsFiniteLength A M) :
    IsIndecomposableModule A M ↔ IsLocalRing (Module.End A M) := by
  refine ⟨isLocalRing_end_of_isIndecomposable hM, fun h ↦ ?_⟩
  have := h
  exact isIndecomposableModule_of_isLocalRing_end

variable (A) in
/-- **A ring is indecomposable as a left module over itself exactly when it is nontrivial and `0`
and `1` are its only idempotents.** An endomorphism of the left module `A` is right multiplication
by an element, and it is idempotent exactly when that element is. -/
theorem isIndecomposableModule_self_iff :
    IsIndecomposableModule A A ↔ Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine and_congr_right fun _ ↦ ⟨fun h e he ↦ ?_, fun h f hf ↦ ?_⟩
  · have hop : IsIdempotentElem (MulOpposite.op e) := by
      rw [IsIdempotentElem, ← MulOpposite.op_mul, he.eq]
    have hf := h (RingEquiv.moduleEndSelf A (MulOpposite.op e))
      (hop.map (RingEquiv.moduleEndSelf A))
    rw [map_eq_zero_iff _ (RingEquiv.moduleEndSelf A).injective,
      map_eq_one_iff _ (RingEquiv.moduleEndSelf A).injective, MulOpposite.op_eq_zero_iff,
      MulOpposite.op_eq_one_iff] at hf
    exact hf
  · obtain ⟨e, rfl⟩ := (RingEquiv.moduleEndSelf A).surjective f
    have he : IsIdempotentElem e.unop := by
      have hee : e * e = e := (RingEquiv.moduleEndSelf A).injective (by rw [map_mul, hf.eq])
      rw [IsIdempotentElem, ← MulOpposite.unop_mul, hee]
    rcases h e.unop he with h0 | h1
    · exact Or.inl (by rw [← MulOpposite.op_unop e, h0, MulOpposite.op_zero, map_zero])
    · exact Or.inr (by rw [← MulOpposite.op_unop e, h1, MulOpposite.op_one, map_one])

/-- **A ring of finite length over itself which is indecomposable over itself is local**, the
converse of `TauCeti.isIndecomposableModule_self` under finite length: by Fitting's lemma the
endomorphism ring of the left module `A`, which is the opposite ring, is local. -/
theorem isLocalRing_of_isIndecomposableModule_self (hA : IsFiniteLength A A)
    (h : IsIndecomposableModule A A) : IsLocalRing A := by
  have := h.nontrivial
  have := isLocalRing_end_of_isIndecomposable hA h
  have : IsLocalRing Aᵐᵒᵖ := .of_surjective' (RingEquiv.moduleEndSelf A).symm.toRingHom
    (RingEquiv.moduleEndSelf A).symm.surjective
  exact .of_surjective' (RingEquiv.opOp A).symm.toRingHom (RingEquiv.opOp A).symm.surjective

end Ring

/-! ### Indecomposable free modules -/

section Free

variable {A : Type u} {M : Type v} [Semiring A] [AddCommMonoid M] [Module A M]

/-- **An indecomposable free module is isomorphic to the scalar semiring.** For a basis vector
`b i`, its span and the span of the remaining basis vectors are complementary, so the latter span
is zero and `i` is the only index. -/
theorem IsIndecomposableModule.nonempty_linearEquiv_of_free [Module.Free A M]
    (h : IsIndecomposableModule A M) : Nonempty (M ≃ₗ[A] A) := by
  have := h.nontrivial
  have := Module.nontrivial A M
  let b := Module.Free.chooseBasis A M
  obtain ⟨i⟩ := b.index_nonempty
  have hi (j : Module.Free.ChooseBasisIndex A M) : j = i := by
    by_contra hji
    rcases h.eq_bot_or_eq_bot (b.linearIndependent.isCompl_span_image b.span_eq
      (isCompl_compl (x := {i}))) with hbot | hbot
    · exact b.ne_zero i (Submodule.span_eq_bot.mp hbot _ ⟨i, rfl, rfl⟩)
    · exact b.ne_zero j (Submodule.span_eq_bot.mp hbot _ ⟨j, hji, rfl⟩)
  have : Subsingleton (Module.Free.ChooseBasisIndex A M) :=
    ⟨fun j j' ↦ (hi j).trans (hi j').symm⟩
  exact ⟨b.repr.trans (Finsupp.uniqueLinearEquiv A A i)⟩

end Free

end TauCeti
end
end TAF_LiteralSource_0387

section TAF_LiteralSource_0388
/- Original module: TauCeti.LinearAlgebra.End.Centralizer -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Endomorphisms commuting with a subalgebra

An endomorphism linear over a subalgebra of `Module.End K N` commutes with that subalgebra.
Restricting scalars therefore gives an element of its centralizer in `Module.End K N`.
This fact uses only semiring scalars and an additive commutative monoid, independently of
semisimplicity or finiteness assumptions used in double centralizer theorems.

For an algebra generated by a set, commuting with the actions of its generators is
equivalent to linearity over the algebra. The resulting algebra equivalence identifies
the centralizer of those scalar actions with the algebra of module endomorphisms.
-/

public section

namespace Subalgebra

variable {K N : Type*} [CommSemiring K] [AddCommMonoid N] [Module K N]

/-- An endomorphism linear over a subalgebra of `Module.End K N` lies in its centralizer after
restricting scalars to `K`. -/
theorem restrictScalars_mem_centralizer (A : Subalgebra K (Module.End K N))
    (g : Module.End A N) :
    g.restrictScalars K ∈ centralizer K (A : Set (Module.End K N)) := by
  refine (mem_centralizer_iff K).2 fun a ha => ?_
  ext m
  exact (g.map_smul ⟨a, ha⟩ m).symm

end Subalgebra

namespace TauCeti

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- If `s` generates `A`, the centralizer of its scalar actions is the algebra of
`A`-linear endomorphisms. -/
def centralizerLsmulAlgEquivEnd (s : Set A) (hs : Algebra.adjoin R s = ⊤) :
    Subalgebra.centralizer R (Algebra.lsmul R R M '' s) ≃ₐ[R] Module.End A M where
  toFun f :=
    { __ := f.val
      map_smul' b := by
        -- The inherited `toFun` and the identity scalar homomorphism reduce to
        -- the underlying function and the original scalar, respectively.
        suffices ∀ x, f.val (b • x) = b • f.val x from this
        have hb : b ∈ Algebra.adjoin R s := hs ▸ trivial
        induction hb using Algebra.adjoin_induction with
        | mem b hb =>
          intro x
          exact (congrArg (fun g : Module.End R M => g x)
            ((Subalgebra.mem_centralizer_iff R).1 f.property _
              (Set.mem_image_of_mem _ hb))).symm
        | algebraMap r => intro x; simp [algebraMap_smul]
        | add b c hb hc ihb ihc => intro x; simp [add_smul, ihb, ihc]
        | mul b c hb hc ihb ihc => intro x; simp [mul_smul, ihb, ihc] }
  invFun f := ⟨f.restrictScalars R, by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    ext x
    exact (f.map_smul a x).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The centralizer equivalence preserves the underlying function. -/
@[simp]
theorem centralizerLsmulAlgEquivEnd_apply (s : Set A) (hs : Algebra.adjoin R s = ⊤)
    (f : Subalgebra.centralizer R (Algebra.lsmul R R M '' s)) (x : M) :
    centralizerLsmulAlgEquivEnd s hs f x = f.val x := (rfl)

/-- The inverse centralizer equivalence restricts scalars. -/
@[simp]
theorem centralizerLsmulAlgEquivEnd_symm_apply (s : Set A) (hs : Algebra.adjoin R s = ⊤)
    (f : Module.End A M) :
    ((centralizerLsmulAlgEquivEnd s hs).symm f).val = f.restrictScalars R := (rfl)

end TauCeti
end
end TAF_LiteralSource_0388

section TAF_LiteralSource_0389
/- Original module: TauCeti.RingTheory.SimpleModule.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Simple and semisimple modules: multiplication by `n`, products, linear maps, idempotents

Mathlib closes `IsSemisimpleModule` under submodules, quotients, `Finsupp`, and finite dependent
products `Π i, M i`. The dependent product covers a binary product only when both factors lie in
the same universe, since the family `M : ι → Type u` is universe-monomorphic; this file supplies
the binary case with the two factors in unrelated universes.

For a **simple** module it records that a natural number either kills no nonzero element or kills
every element.

It also records which elements a linear map from a semisimple module can connect: some
`R`-linear map sends `w : M` to `x : N` exactly when every scalar killing `w` kills `x`. The target
module `N` can be arbitrary. Specializing to endomorphisms gives a containment between torsion
ideals useful in centralizer arguments.

Over a semisimple ring, the torsion ideal of an element is a direct summand of the ring, so the
element generates a copy of the projective left ideal `R f` for an idempotent `f`. Minimal graded
projective covers over an algebra with semisimple degree-zero part are assembled from such
idempotents.

## Main results

* `TauCeti.forall_nsmul_eq_zero_of_ne_zero_of_nsmul_eq_zero`: in a simple module, a natural number
  killing one nonzero element kills every element.
* `IsSemisimpleModule.prod`: a product of two semisimple modules is semisimple.
* `IsSemisimpleModule.exists_apply_eq_iff`: a linear map from a semisimple module
  sends `w` to `x` if and only if the torsion ideal of `w` is contained in that of `x`.
* `IsSemisimpleRing.exists_isIdempotentElem_smul_eq_zero_iff`: over a semisimple ring,
  every cyclic submodule `R ∙ v` is isomorphic to `R f` for an idempotent `f` fixing `v`.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section SimpleModule

/-- **In a simple module a natural number that kills one nonzero element kills every element.** -/
theorem forall_nsmul_eq_zero_of_ne_zero_of_nsmul_eq_zero [IsSimpleModule R M] {n : ℕ} {m₀ : M}
    (hm₀ : m₀ ≠ 0) (h : n • m₀ = 0) (m : M) : n • m = 0 := by
  obtain ⟨r, rfl⟩ := _root_.IsSimpleModule.toSpanSingleton_surjective R hm₀ m
  simp only [LinearMap.toSpanSingleton_apply, ← smul_comm r n, h, smul_zero]

end SimpleModule

/-- **A product of two semisimple modules is semisimple.** -/
instance _root_.IsSemisimpleModule.prod [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  -- The plan is that of Mathlib's binary-product `IsSemisimpleRing` instance, one level down:
  -- `M × N` is the join of the two coordinate copies, each of which is a semisimple submodule.
  have hsup := IsSemisimpleModule.sup
    (IsSemisimpleModule.range (LinearMap.inl R M N))
    (IsSemisimpleModule.range (LinearMap.inr R M N))
  rw [LinearMap.sup_range_inl_inr] at hsup
  exact .congr Submodule.topEquiv.symm

/-- **Linear maps from a semisimple module with a prescribed value.** Some `R`-linear map from
the semisimple module `M` to an arbitrary module `N` sends `w` to `x` exactly when every scalar
annihilating `w` annihilates `x`, that is, when
`Ideal.torsionOf R M w ≤ Ideal.torsionOf R N x`. -/
theorem _root_.IsSemisimpleModule.exists_apply_eq_iff [IsSemisimpleModule R M] {w : M} {x : N} :
    (∃ f : M →ₗ[R] N, f w = x) ↔ Ideal.torsionOf R M w ≤ Ideal.torsionOf R N x := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, rfl⟩ r hr
    rw [Ideal.mem_torsionOf_iff] at hr ⊢
    rw [← f.map_smul, hr, map_zero]
  · -- `r • w ↦ r • x` is well defined on `R ∙ w ≃ R ⧸ torsionOf w`; extend it to all of `M`
    let g : (R ∙ w) →ₗ[R] N :=
      (Ideal.torsionOf R M w).liftQ (LinearMap.toSpanSingleton R N x) h ∘ₗ
        (Ideal.quotTorsionOfEquivSpanSingleton R M w).symm.toLinearMap
    obtain ⟨f, hf⟩ := IsSemisimpleModule.extension_property _
      (R ∙ w).subtype_injective g
    refine ⟨f, ?_⟩
    have hw := Ideal.quotTorsionOfEquivSpanSingleton_apply_mk w (1 : R)
    rw [one_smul] at hw
    have hfw := LinearMap.congr_fun hf ⟨w, Submodule.mem_span_singleton_self w⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at hfw
    rw [hfw, ← hw]
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    -- `liftQ` evaluates on the class of `1` to `1 • x` by definition; the `Ideal R` and
    -- `Submodule R R` forms of the kernel condition block rewriting with `Submodule.liftQ_apply`
    exact one_smul R x

/-- **Cyclic modules over a semisimple ring are generated by idempotents.** Over a semisimple ring,
every element `v` of a module is fixed by an idempotent `f` whose left multiples meet the
annihilator `Ideal.torsionOf R M v` only in zero: `c • v = 0` exactly when `c * f = 0`. Thus
`c * f ↦ c • v` identifies the projective left ideal `R f` with the cyclic submodule `R ∙ v`. -/
theorem _root_.IsSemisimpleRing.exists_isIdempotentElem_smul_eq_zero_iff [IsSemisimpleRing R]
    (v : M) :
    ∃ f : R, IsIdempotentElem f ∧ f • v = v ∧ ∀ c : R, c • v = 0 ↔ c * f = 0 := by
  obtain ⟨u, hu, hL⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.torsionOf R M v)
  have hmem (c : R) : c • v = 0 ↔ ∃ r, r * u = c := by
    rw [← Ideal.mem_torsionOf_iff, hL, Ideal.mem_span_singleton']
  have huv : u • v = 0 := (hmem u).2 ⟨1, one_mul u⟩
  refine ⟨1 - u, hu.one_sub, by rw [sub_smul, one_smul, huv, sub_zero], fun c => ?_⟩
  rw [hmem, mul_sub, mul_one, sub_eq_zero]
  constructor
  · rintro ⟨r, rfl⟩
    rw [mul_assoc, hu.eq]
  · exact fun hc => ⟨c, hc.symm⟩

end TauCeti
end
end TAF_LiteralSource_0389

section TAF_LiteralSource_0390
/- Original module: TauCeti.RingTheory.Semisimple.DoubleCentralizer -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The double centralizer theorem

Mathlib's Jacobson density theorem (`Module.Finite.toModuleEnd_moduleEnd_surjective`) says that for
a semisimple `R`-module `M` which is finite over its endomorphism ring `D = Module.End R M`, the
natural map `R → Module.End D M` is **surjective**. This file sharpens that to a **bijection** for
a faithful such `M`, so that `R` is recovered from its action: `R ≃+* Module.End D M`.

The half that is missing upstream is injectivity, and injectivity is exactly faithfulness of `M`.
Faithfulness is not automatic, but it is automatic in the case the structure theory cares about:
a nontrivial module over a **simple** ring is faithful, because the elements killing `M` form a
two-sided ideal not containing `1`. So over a simple ring every nontrivial semisimple module finite
over `D` gives `R ≃+* Module.End D M`. When `M` is simple, this is the Wedderburn presentation
in module-internal form: no ambient base field is involved, only finiteness over `D`.

The last section restates the theorem in the form a representation uses: for a subalgebra `A` of
`Module.End K N` over which `N` is semisimple, the double centralizer of `A` *inside*
`Module.End K N` is `A` itself. Here faithfulness is automatic, `A` being a set of endomorphisms,
so only Mathlib's surjectivity is needed; the centralizer `A'` is the ring of `A`-linear
endomorphisms of `N`, and an element of `A''` is exactly an `A'`-linear endomorphism. This is a
different theorem from `Subalgebra.centralizer_centralizer_of_isSimpleRing` of
`TauCeti/Algebra/CentralSimple/Centralizer/Simple.lean`, which computes the double centralizer of a
*simple* subalgebra of a central simple algebra by a dimension count; neither hypothesis
implies the other.

## Main results

* `TauCeti.faithfulSMul_of_isSimpleRing`: a nontrivial module over a simple ring is faithful.
* `TauCeti.toModuleEnd_moduleEnd_bijective`: **the double centralizer theorem**. For a faithful
  semisimple module `M` finite over `D = Module.End R M`, the map `R → Module.End D M` is bijective;
  `TauCeti.ringEquivEndEnd` packages it as a ring isomorphism, and
  `TauCeti.algEquivEndEnd` as an algebra isomorphism over a compatible base ring.
* `TauCeti.toModuleEnd_moduleEnd_bijective_of_isSimpleRing`: the specialization to a nontrivial
  semisimple module over a simple ring, where faithfulness is automatic.
* `LinearIndependent.exists_smul_eq`: the Jacobson-Chevalley form of density. Over a
  simple module, a single element of `R` carries any finite `D`-linearly independent family
  to an arbitrary family of targets.
* `TauCeti.algEquivEndEndOfIsSimpleRing`: the finite-dimensional-algebra form, where the finiteness
  hypothesis is supplied by finiteness over a commutative base ring acting compatibly.
* `Subalgebra.centralizer_centralizer_of_isSemisimpleModule`: the **subalgebra form**. A subalgebra
  `A` of `Module.End K N` over which `N` is semisimple, `N` finite over `Module.End A N`, is its
  own double centralizer inside `Module.End K N`.
* `AlgHom.centralizer_centralizer_range`: the same statement for the image of a semisimple
  algebra, the form a representation supplies. The image, not the algebra itself, is what the
  double centralizer returns, since the representation need not be faithful.
* `Subalgebra.exists_mem_centralizer_apply_eq_iff_of_isSemisimpleModule` and
  `AlgHom.exists_mem_centralizer_range_apply_eq_iff`: an endomorphism commuting with `A`
  (respectively with the image of a semisimple algebra) carries `w` to `x` exactly when everything
  in `A` killing `w` kills `x`.

## Implementation notes

The finiteness hypothesis is `Module.Finite (Module.End R M) M`, finiteness over the endomorphism
ring itself, rather than finite-dimensionality over an unrelated base ring. That is the hypothesis
surjectivity of the action needs. When a base ring `K` acts compatibly, its scalars are `R`-linear
endomorphisms, so `Module.Finite K M` gives it by
`Module.Finite.of_restrictScalars_finite`.

A faithful simple module makes `R` a *primitive* ring, not necessarily a simple one, so
`TauCeti.toModuleEnd_moduleEnd_bijective` is genuinely more general than its simple-ring corollary.
It is also stated for a merely semisimple `M`, which is all that Mathlib's surjectivity needs.

The main theorem is named after the Mathlib lemma it sharpens,
`Module.Finite.toModuleEnd_moduleEnd_surjective`, keeping the surjective/bijective pair in step.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, Chapter 4, and N. Jacobson,
*Basic Algebra II*, Chapter 4.
-/

public section

namespace TauCeti

open Module

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Faithfulness over a simple ring -/

/-- A nontrivial module over a simple ring is faithful: the elements of `R` killing `M` are the
kernel of a ring homomorphism out of `R`, a two-sided ideal not containing `1`, hence `⊥`. -/
theorem faithfulSMul_of_isSimpleRing [IsSimpleRing R] [Nontrivial M] : FaithfulSMul R M where
  eq_of_smul_eq_smul {_ _} h :=
    (Module.toModuleEnd (Module.End R M) M (S := R)).injective (LinearMap.ext h)

/-! ### The double centralizer theorem -/

section Density

variable (R M)

/-- **The double centralizer theorem.** Let `M` be a faithful semisimple `R`-module which is finite
over its endomorphism ring `D = Module.End R M`. Then the natural map `R → Module.End D M` is
bijective: `R` is exactly the ring of `D`-linear endomorphisms of `M`.

This sharpens Mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective` from surjectivity to
bijectivity; the extra input is faithfulness, which is what makes the map injective. -/
theorem toModuleEnd_moduleEnd_bijective [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End R M) M (S := R)) :=
  ⟨fun _ _ h ↦ eq_of_smul_eq_smul (α := M) fun m ↦ LinearMap.congr_fun h m,
    Module.Finite.toModuleEnd_moduleEnd_surjective⟩

/-- The double centralizer theorem as a ring isomorphism: a faithful semisimple module finite over
its endomorphism ring `D` identifies `R` with `Module.End D M`. -/
noncomputable def ringEquivEndEnd [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    R ≃+* Module.End (Module.End R M) M :=
  RingEquiv.ofBijective _ (toModuleEnd_moduleEnd_bijective R M)

variable {R M}

@[simp]
theorem ringEquivEndEnd_apply [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (r : R) (m : M) :
    ringEquivEndEnd R M r m = r • m := by
  simp [ringEquivEndEnd]

@[simp]
theorem ringEquivEndEnd_symm_smul [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (f : Module.End (Module.End R M) M) (m : M) :
    (ringEquivEndEnd R M).symm f • m = f m := by
  rw [← ringEquivEndEnd_apply ((ringEquivEndEnd R M).symm f) m, RingEquiv.apply_symm_apply]

variable (R M)

/-- The double centralizer isomorphism as an isomorphism of `K`-algebras, for a commutative base
ring `K` acting on `M` compatibly with `R`. -/
noncomputable def algEquivEndEnd (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    R ≃ₐ[K] Module.End (Module.End R M) M :=
  AlgEquiv.ofRingEquiv (f := ringEquivEndEnd R M) fun k ↦ by
    ext m
    rw [ringEquivEndEnd_apply, algebraMap_smul, Module.algebraMap_end_apply]

variable {R M}

@[simp]
theorem algEquivEndEnd_apply (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (r : R) (m : M) :
    algEquivEndEnd R M K r m = r • m :=
  ringEquivEndEnd_apply r m

@[simp]
theorem algEquivEndEnd_symm_smul (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (f : Module.End (Module.End R M) M) (m : M) :
    (algEquivEndEnd R M K).symm f • m = f m := by
  rw [← algEquivEndEnd_apply K ((algEquivEndEnd R M K).symm f) m, AlgEquiv.apply_symm_apply]

variable (R M)

/-- **The double centralizer theorem for a simple ring.** A nontrivial semisimple module over a
simple ring is automatically faithful. If it is finite over its endomorphism ring `D`, it presents
`R` as `Module.End D M`. -/
theorem toModuleEnd_moduleEnd_bijective_of_isSimpleRing [IsSimpleRing R]
    [IsSemisimpleModule R M] [Nontrivial M] [Module.Finite (Module.End R M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End R M) M (S := R)) :=
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  toModuleEnd_moduleEnd_bijective R M

end Density

/-! ### Jacobson-Chevalley density -/

/-- **Jacobson-Chevalley density.** For a simple module `M`, a finite linearly independent family
over `D = Module.End R M` can be carried to an arbitrary family of targets by a single scalar
from `R`. No finiteness assumption on `M` is needed.

Linear independence is essential: a `D`-linear relation among the `v i` is inherited by the
`r • v i`, so the targets could not be arbitrary. -/
theorem _root_.LinearIndependent.exists_smul_eq [IsSimpleModule R M]
    {ι : Type*} [Finite ι] {v : ι → M}
    (hv : LinearIndependent (Module.End R M) v) (w : ι → M) :
    ∃ r : R, ∀ i, r • v i = w i := by
  classical
  -- `v` is a basis of its span, so it has the prescribed values under some `D`-linear map on that
  -- span; extend that map to all of `M` and let density realize the extension by a scalar.
  obtain ⟨f, hf⟩ := ((Basis.span hv).constr ℕ w).exists_extend
  obtain ⟨r, hr⟩ := jacobson_density (R := R) f (Set.finite_range v).toFinset
  refine ⟨r, fun i ↦ ?_⟩
  have hvi : f (v i) = w i := by
    -- `f` agrees on the span with `(Basis.span hv).constr ℕ w`, which sends the `i`-th basis
    -- vector to `w i`; that basis vector is `v i` viewed inside the span.
    have h := LinearMap.congr_fun hf ((Basis.span hv) i)
    rw [Basis.constr_basis] at h
    simpa using h
  exact (hr (v i) (by simp)).symm.trans hvi

/-! ### The finite-dimensional algebra case -/

variable (R M)

/-- **The double centralizer theorem for a finite module over a simple algebra.** If `R` is a
simple `K`-algebra and `M` a nontrivial semisimple `R`-module finite as a `K`-module, then `M`
presents `R` as the algebra of `D`-linear endomorphisms of `M`, where `D = Module.End R M`. -/
noncomputable def algEquivEndEndOfIsSimpleRing (K : Type*) [CommSemiring K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R]
    [IsSemisimpleModule R M] [Nontrivial M] :
    R ≃ₐ[K] Module.End (Module.End R M) M :=
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  have := Module.Finite.of_restrictScalars_finite K (Module.End R M) M
  algEquivEndEnd R M K

variable {R M}

@[simp]
theorem algEquivEndEndOfIsSimpleRing_apply (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R]
    [IsSemisimpleModule R M] [Nontrivial M] (r : R) (m : M) :
    algEquivEndEndOfIsSimpleRing R M K r m = r • m :=
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  have := Module.Finite.of_restrictScalars_finite K (Module.End R M) M
  algEquivEndEnd_apply K r m

@[simp]
theorem algEquivEndEndOfIsSimpleRing_symm_smul (K : Type*) [CommSemiring K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R]
    [IsSemisimpleModule R M] [Nontrivial M]
    (f : Module.End (Module.End R M) M) (m : M) :
    (algEquivEndEndOfIsSimpleRing R M K).symm f • m = f m := by
  rw [← algEquivEndEndOfIsSimpleRing_apply K ((algEquivEndEndOfIsSimpleRing R M K).symm f) m,
    AlgEquiv.apply_symm_apply]

/-! ### The double centralizer of a subalgebra of an endomorphism algebra -/

section EndSubalgebra

variable {K : Type*} [CommRing K] {N : Type*} [AddCommGroup N] [Module K N]
  (A : Subalgebra K (Module.End K N))

/-- **The double centralizer theorem inside an endomorphism algebra.** Let `A` be a `K`-subalgebra
of `Module.End K N`, and suppose `N` is semisimple as an `A`-module and finite over
`Module.End A N`. Then `A` is its own double centralizer: an endomorphism commuting with everything
that commutes with `A` already lies in `A`.

The inclusion `A ≤ A''` is formal (`Subalgebra.le_centralizer_centralizer`); the content is the
reverse one, which is Jacobson density. The centralizer `A'` is the ring of `A`-linear
endomorphisms of `N`, so an element of `A''` is an `A'`-linear endomorphism, and density writes
every such endomorphism as the action of an element of `A`.

Finiteness is over `Module.End A N`, the hypothesis density actually needs; a caller with a finite
`K`-module `N` gets it from `Module.Finite.of_restrictScalars_finite`. -/
theorem _root_.Subalgebra.centralizer_centralizer_of_isSemisimpleModule
    [Module.Finite (Module.End A N) N] [IsSemisimpleModule A N] :
    Subalgebra.centralizer K
        (Subalgebra.centralizer K (A : Set (Module.End K N)) : Set (Module.End K N)) = A := by
  refine le_antisymm (fun x hx => ?_) (Subalgebra.le_centralizer_centralizer K)
  rw [Subalgebra.mem_centralizer_iff] at hx
  -- `x` commutes with every `A`-linear endomorphism, so it is `A'`-linear.
  let f : Module.End (Module.End A N) N :=
    { toFun := x
      map_add' := x.map_add
      map_smul' := fun g m => by
        -- Evaluating the commutation of `x` with `g.restrictScalars K` at `m` gives
        -- `x (g m) = g (x m)`, which is the required `A'`-linearity once the scalar action of
        -- `Module.End ↥A N` on `N` is `Module.End.smul_def` and the restriction of scalars is
        -- `LinearMap.coe_restrictScalars`.
        have h := congrArg (fun t : Module.End K N => t m)
          (hx _ (A.restrictScalars_mem_centralizer g))
        simpa only [Module.End.smul_def, RingHom.id_apply, Module.End.mul_apply,
          LinearMap.coe_restrictScalars] using h.symm }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := N) f
  have hx' : x = (a : Module.End K N) := by
    ext m
    exact (congrArg (fun t : Module.End (Module.End A N) N => t m) ha).symm
  exact hx' ▸ a.2

/-- **The double centralizer theorem for the image of a semisimple algebra.** The image of a
semisimple `K`-algebra `S` in `Module.End K N` is its own double centralizer when `N` is finite
over the endomorphism ring of the image's action.

The image is a quotient of `S`, hence semisimple, so `N` is a semisimple module over it and
`Subalgebra.centralizer_centralizer_of_isSemisimpleModule` applies. A caller with a finite
`K`-module gets the required finiteness from `Module.Finite.of_restrictScalars_finite`. It is the
image and not `S` that is recovered: the representation `S → Module.End K N` need not be
injective. -/
theorem _root_.AlgHom.centralizer_centralizer_range
    {S : Type*} [Ring S] [Algebra K S] [IsSemisimpleRing S] (ρ : S →ₐ[K] Module.End K N)
    [Module.Finite (Module.End ρ.range N) N] :
    Subalgebra.centralizer K
        (Subalgebra.centralizer K (ρ.range : Set (Module.End K N)) : Set (Module.End K N)) =
      ρ.range := by
  have : IsSemisimpleRing ρ.range :=
    RingHom.isSemisimpleRing_of_surjective ρ.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  have : IsSemisimpleModule ρ.range N := IsSemisimpleRing.isSemisimpleModule
  exact Subalgebra.centralizer_centralizer_of_isSemisimpleModule _

/-- **The centralizer moves vectors as freely as annihilators allow.** Let `A` be a `K`-subalgebra
of `Module.End K N` over which `N` is semisimple. Some endomorphism commuting with `A` sends `w` to
`x` if and only if every element of `A` annihilating `w` also annihilates `x`. -/
theorem _root_.Subalgebra.exists_mem_centralizer_apply_eq_iff_of_isSemisimpleModule
    [IsSemisimpleModule A N] {w x : N} :
    (∃ f ∈ Subalgebra.centralizer K (A : Set (Module.End K N)), f w = x) ↔
      ∀ a ∈ A, a w = 0 → a x = 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, rfl⟩ a ha haw
    rw [← Module.End.mul_apply, (Subalgebra.mem_centralizer_iff K).1 hf a ha,
      Module.End.mul_apply, haw, map_zero]
  obtain ⟨f, hf⟩ := (IsSemisimpleModule.exists_apply_eq_iff (R := A)).mpr
    fun a ha => h a a.2 ha
  exact ⟨f.restrictScalars K, A.restrictScalars_mem_centralizer f, hf⟩

/-- **The centralizer of a semisimple image moves vectors as freely as annihilators allow.** For a
semisimple `K`-algebra `S` acting on `N` through `ρ`, some endomorphism commuting with the image of
`ρ` sends `w` to `x` if and only if every `s` with `ρ s w = 0` also has `ρ s x = 0`. -/
theorem _root_.AlgHom.exists_mem_centralizer_range_apply_eq_iff {S : Type*} [Ring S] [Algebra K S]
    [IsSemisimpleRing S] (ρ : S →ₐ[K] Module.End K N) {w x : N} :
    (∃ f ∈ Subalgebra.centralizer K (Set.range ρ), f w = x) ↔ ∀ s, ρ s w = 0 → ρ s x = 0 := by
  have : IsSemisimpleRing ρ.range :=
    RingHom.isSemisimpleRing_of_surjective ρ.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  have : IsSemisimpleModule ρ.range N := IsSemisimpleRing.isSemisimpleModule
  rw [← AlgHom.coe_range, Subalgebra.exists_mem_centralizer_apply_eq_iff_of_isSemisimpleModule]
  exact ⟨fun h s => h _ ⟨s, rfl⟩, by rintro h _ ⟨s, rfl⟩; exact h s⟩

end EndSubalgebra

end TauCeti
end
end TAF_LiteralSource_0390

section TAF_LiteralSource_0391
/- Original module: TauCeti.RingTheory.Semisimple.Schur -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Schur's lemma for simple modules

This file packages the two forms of Schur's lemma used by the semisimple-algebra development.

For simple modules over an arbitrary ring, Mathlib proves that a linear map is either bijective or
zero (`LinearMap.bijective_or_eq_zero`). Consequently the entire hom group vanishes exactly when the
two modules are not linearly equivalent. When an equivalence does exist, Mathlib's
`LinearEquiv.arrowCongrAddEquiv` identifies the hom group with either endomorphism ring by
composition; no separate construction is needed here.

Over an algebraically closed field `k`, a domain algebra that is integral over `k` is `k` itself.
The proof uses Mathlib's theorem that the algebra map from an algebraically closed field into such
an algebra is bijective; a finite-dimensional division algebra is a special case, with integrality
coming from finite dimensionality. The same collapse for the endomorphism ring of a
finite-dimensional simple module is Mathlib's
`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`, packaged here as an algebra equivalence.

Both forms are then read as statements about dimensions, for a `k`-algebra `A` acting on modules
that are `k`-modules compatibly: the hom space between inequivalent simple modules has dimension
`0`, and between equivalent finite-dimensional simple modules it is a line. Transporting a hom
space along an isomorphism of its target, `LinearEquiv.homCongrRight`, carries the endomorphism
computation to an arbitrary equivalent target.

## Main results

* `TauCeti.hom_eq_zero_of_isEmpty_linearEquiv`: every map between inequivalent simple modules is
  zero.
* `TauCeti.subsingleton_linearMap_iff_isEmpty_linearEquiv`: the corresponding characterization of
  the whole hom group.
* `TauCeti.nontrivial_linearMap_iff_nonempty_linearEquiv`: two simple modules are equivalent exactly
  when their hom group is nontrivial.
* `TauCeti.nonempty_algEquiv_self_of_isIntegral`: a domain algebra over an algebraically closed
  field that is integral over that field is isomorphic to it as an algebra, with
  `TauCeti.nonempty_algEquiv_self_of_finiteDimensional_divisionRing` the finite-dimensional
  division algebra special case.
* `TauCeti.endAlgEquivSelfOfIsSimpleModule`: the endomorphism ring of a finite-dimensional simple
  module over an algebraically closed field collapses to that field, canonically, as the inverse
  of the structure map; `TauCeti.nonempty_end_algEquiv_self_of_isSimpleModule` is its existence
  form.
* `TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv` and
  `LinearEquiv.finrank_linearMap_eq_one`: the two forms of Schur's lemma in
  dimensions. More generally, `TauCeti.finiteDimensional_linearMap_of_isSimpleModule` shows that
  maps from any finite-dimensional module into a simple module form a finite-dimensional space.

## References

See N. Jacobson, *Basic Algebra II*, Chapter 3, or T. Y. Lam, *A First Course in Noncommutative
Rings*, Chapter 1.
-/

public section

namespace TauCeti

universe u v w

/-! ### Maps between simple modules -/

section SimpleModules

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [IsSimpleModule R M] [IsSimpleModule R N]

/-- **Schur's lemma, vanishing form.** A linear map between simple modules is zero if the two
modules are not linearly equivalent.

The `IsEmpty` hypothesis is the constructive form of saying that no equivalence exists. -/
theorem hom_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) (f : M →ₗ[R] N) :
    f = 0 := by
  rcases f.bijective_or_eq_zero with hf | hf
  · exact (h.false (LinearEquiv.ofBijective f hf)).elim
  · exact hf

/-- The hom group between simple modules is a subsingleton if the modules are not linearly
equivalent. -/
theorem subsingleton_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) :
    Subsingleton (M →ₗ[R] N) :=
  ⟨fun f g ↦ sub_eq_zero.mp (hom_eq_zero_of_isEmpty_linearEquiv h (f - g))⟩

/-- The hom group between two simple modules is a subsingleton exactly when the modules are not
linearly equivalent. -/
theorem subsingleton_linearMap_iff_isEmpty_linearEquiv :
    Subsingleton (M →ₗ[R] N) ↔ IsEmpty (M ≃ₗ[R] N) := by
  constructor
  · intro h
    let := h
    exact ⟨fun e ↦ by
      have hzero : e.toLinearMap = 0 := Subsingleton.elim _ _
      have := IsSimpleModule.nontrivial R M
      exact e.toLinearMap.ne_zero_of_injective e.injective hzero⟩
  · exact subsingleton_linearMap_of_isEmpty_linearEquiv

/-- The hom group between two simple modules is nontrivial exactly when the modules are linearly
equivalent. This is the existence form of Schur's lemma. -/
theorem nontrivial_linearMap_iff_nonempty_linearEquiv :
    Nontrivial (M →ₗ[R] N) ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_linearMap_iff_isEmpty_linearEquiv,
    not_isEmpty_iff]

end SimpleModules

/-! ### Domain algebras over algebraically closed fields -/

section IsAlgClosed

variable {k : Type u} {D : Type v} [Field k] [IsAlgClosed k]

section Domain

variable [Ring D] [IsDomain D] [Algebra k D]

/-- A domain algebra over an algebraically closed field `k` that is integral over `k` is `k`
itself, as an isomorphism of algebras.

Mathlib proves that the algebra map from an algebraically closed field to such an algebra is
bijective; this packages that bijection as an algebra equivalence. -/
theorem nonempty_algEquiv_self_of_isIntegral [Algebra.IsIntegral k D] : Nonempty (D ≃ₐ[k] k) :=
  ⟨(AlgEquiv.ofBijective (Algebra.ofId k D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

end Domain

/-- A finite-dimensional division algebra over an algebraically closed field is the field itself,
as an isomorphism of algebras. Finite dimensionality supplies integrality, so this is the
special case of `nonempty_algEquiv_self_of_isIntegral` that the semisimple-algebra development
uses. -/
theorem nonempty_algEquiv_self_of_finiteDimensional_divisionRing [DivisionRing D] [Algebra k D]
    [FiniteDimensional k D] : Nonempty (D ≃ₐ[k] k) :=
  nonempty_algEquiv_self_of_isIntegral

end IsAlgClosed

/-! ### Endomorphisms of a simple module over an algebraically closed field -/

section SimpleEnd

variable {k : Type u} {A : Type v} {S : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]

/-- **Schur's lemma over an algebraically closed field.** The endomorphism ring of a
finite-dimensional simple module over a `k`-algebra is the field `k` itself.

Mathlib's `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` proves that every such
endomorphism is a scalar; this packages that bijection as an algebra equivalence. Finite
dimensionality is needed: an infinite-dimensional simple module can have a larger division
endomorphism ring.

The equivalence involves no choices: it is the inverse of the structure map `k → End A S`, which
Schur's lemma proves bijective. Its inverse is therefore `algebraMap` on the nose, and the scalar
attached to an endomorphism is characterized by
`TauCeti.endAlgEquivSelfOfIsSimpleModule_smul`. -/
noncomputable def endAlgEquivSelfOfIsSimpleModule : Module.End A S ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A S))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)).symm

/-- The inverse of the Schur equivalence is the structure map of the endomorphism algebra. -/
@[simp]
theorem endAlgEquivSelfOfIsSimpleModule_symm_apply (c : k) :
    (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).symm c =
      algebraMap k (Module.End A S) c :=
  (rfl)

/-- The scalar attached to an endomorphism of a simple module is the scalar it acts by. -/
@[simp]
theorem endAlgEquivSelfOfIsSimpleModule_smul (f : Module.End A S) (s : S) :
    endAlgEquivSelfOfIsSimpleModule (k := k) f • s = f s := by
  conv_rhs =>
    rw [← (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).symm_apply_apply f]
  rw [endAlgEquivSelfOfIsSimpleModule_symm_apply, Module.algebraMap_end_apply]

/-- The existence statement of Schur's lemma over an algebraically closed field, for consumers
that only need to know that some algebra equivalence exists. -/
theorem nonempty_end_algEquiv_self_of_isSimpleModule : Nonempty (Module.End A S ≃ₐ[k] k) :=
  ⟨endAlgEquivSelfOfIsSimpleModule⟩

end SimpleEnd

/-! ### Schur's lemma in dimension form -/

section Vanishing

section Semiring

variable {k A S N : Type*} [CommSemiring k] [Nontrivial k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module A S] [IsSimpleModule A S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]

/-- **Schur's lemma, vanishing form, in dimensions.**  Between inequivalent simple modules the
hom space is trivial, hence of dimension zero.

Schur's lemma is normally read with a field of scalars, but this half of it does not need one.
The conclusion is a statement about the zero module, whose `Module.finrank` vanishes over any
nontrivial commutative semiring, and that is all `k` is asked to be here. So the result is
available wherever the simple modules live over an algebra, without first arranging a field to
measure the hom space in. -/
theorem finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    Module.finrank k (S →ₗ[A] N) = 0 := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.finrank_zero_of_subsingleton

end Semiring

variable {k A S N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module A S] [IsSimpleModule A S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]

/-- The hom space between inequivalent simple modules is finite-dimensional, being trivial. -/
theorem finiteDimensional_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    FiniteDimensional k (S →ₗ[A] N) := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.Finite.of_surjective (0 : k →ₗ[k] (S →ₗ[A] N)) fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end Vanishing

section SimpleTarget

variable {k A S N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [FiniteDimensional k S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]

/-- The hom space from a finite-dimensional module into a simple module is finite-dimensional
over any field. -/
theorem finiteDimensional_linearMap_of_isSimpleModule : FiniteDimensional k (S →ₗ[A] N) := by
  -- A nonzero map is surjective and makes the target finite-dimensional;
  -- otherwise the hom space is trivial.
  by_cases h : ∃ f : S →ₗ[A] N, f ≠ 0
  · obtain ⟨f, hf⟩ := h
    have : FiniteDimensional k N :=
      Module.Finite.of_surjective (f.restrictScalars k) (f.surjective_of_ne_zero hf)
    infer_instance
  · have : Subsingleton (S →ₗ[A] N) := ⟨fun f g ↦ by simp_all⟩
    infer_instance

end SimpleTarget

section SimpleSymmetry

variable {k A : Type*} [CommSemiring k] [Nontrivial k] [Ring A] [Algebra k A]

/-- Hom-space finrank is symmetric between simple modules over an algebra. -/
theorem finrank_linearMap_comm_of_isSimpleModule
    (S N : Type*) [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [IsSimpleModule A S] [IsSimpleModule A N] :
    Module.finrank k (S →ₗ[A] N) = Module.finrank k (N →ₗ[A] S) := by
  by_cases h : Nonempty (S ≃ₗ[A] N)
  · obtain ⟨e⟩ := h
    exact ((LinearEquiv.homCongrRight k e.symm).trans (LinearEquiv.congrLeft S k e)).finrank_eq
  · rw [finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (not_nonempty_iff.mp h),
      finrank_linearMap_eq_zero_of_isEmpty_linearEquiv
        ⟨fun e ↦ h ⟨e.symm⟩⟩]

end SimpleSymmetry

section SchurDimension

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [IsSimpleModule A N]

omit [IsSimpleModule A N] in
/-- **Schur's lemma over an algebraically closed field, in dimensions.**  Between equivalent
finite-dimensional simple modules the hom space is a line: every map is a scalar multiple of a
fixed isomorphism. -/
theorem _root_.LinearEquiv.finrank_linearMap_eq_one (e : S ≃ₗ[A] N) :
    Module.finrank k (S →ₗ[A] N) = 1 := by
  have hend : Module.finrank k (Module.End A S) = 1 := by
    rw [(endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  rw [← (LinearEquiv.homCongrRight k (S := S) e).finrank_eq]
  exact hend

end SchurDimension

end TauCeti
end
end TAF_LiteralSource_0391

section TAF_LiteralSource_0392
/- Original module: TauCeti.LinearAlgebra.TensorProduct.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor-product naturality, contractions and trace identities

This file records how tensor reassociation interacts with tensoring composite maps. It defines
contraction against a linear functional on the right factor, bundled as a linear map in the
functional, and records its behavior on pure tensors and under tensor-product maps.
Such contractions extract coordinates and test tensor identities, supporting componentwise
arguments about coactions and weight spaces. The file also proves the tensor identity that makes
the Casimir element of a trace commute with multiplication.

## Main declarations

* `LinearMap.assoc_rTensor_lTensor_comp`: reassociation commutes with tensoring a composite map.
* `LinearMap.lTensor_rTensor_comm`: tensoring maps on the two factors commutes elementwise.
* `LinearMap.injective_rTensor_congr`: injectivity of `f ⊗ 𝟙 M` is invariant under isomorphisms
  of `M`.
* `LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
* `LinearMap.tensorComponent_assoc_symm`: contraction commutes with reassociation.
* `LinearMap.comp_tensorComponent`: contraction commutes with a functional on the left.
* `LinearMap.tensorComponent_comp_tensorComponent`: successive contractions combine after
  reassociation.
* `LinearMap.rid_rTensor_apply`: naturality of the right tensor unitor.
* `LinearMap.sum_mul_tmul_eq_sum_tmul_mul`: the Casimir element of a trace commutes with
  multiplication.

## References

* L. Kadison, *New examples of Frobenius extensions*, University Lecture Series 14, AMS, 1999
  (dual bases of Frobenius algebras and extensions, and their Casimir elements).
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LinearMap

universe u v w x y

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

section Naturality

variable {P Q S T : Type*}
variable [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid S] [Module R S] [AddCommMonoid T] [Module R T]

/-- Reassociation commutes with tensoring a composite linear map and changing the last factor. -/
theorem assoc_rTensor_lTensor_comp (f : N →ₗ[R] P) (g : Q →ₗ[R] S)
    (ρ : M →ₗ[R] T ⊗[R] N) (t : M ⊗[R] Q) :
    TensorProduct.assoc R T P S ((f.lTensor T ∘ₗ ρ).rTensor S (g.lTensor M t)) =
      TensorProduct.map LinearMap.id (TensorProduct.map f g)
        (TensorProduct.assoc R T N Q (ρ.rTensor Q t)) := by
  simp only [lTensor_def, rTensor_map, comp_id]
  rw [← map_rTensor, ← TensorProduct.map_map_assoc]

/-- Tensoring maps on the two factors commutes, elementwise: `(𝟙 ⊗ g) ∘ (f ⊗ 𝟙)` and
`(f ⊗ 𝟙) ∘ (𝟙 ⊗ g)` agree on every element. -/
theorem lTensor_rTensor_comm (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    g.lTensor P (f.rTensor N x) = f.rTensor Q (g.lTensor M x) := by
  rw [← comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor, comp_apply]

/-- Injectivity of `f ⊗ 𝟙 M` only depends on `M` up to isomorphism. -/
theorem injective_rTensor_congr (f : N →ₗ[R] P) (e : M ≃ₗ[R] Q) :
    Function.Injective (f.rTensor M) ↔ Function.Injective (f.rTensor Q) := by
  have h : e.lTensor P ∘ f.rTensor M = f.rTensor Q ∘ e.lTensor N :=
    funext fun x ↦ lTensor_rTensor_comm f e.toLinearMap x
  rw [← EquivLike.comp_injective _ (e.lTensor P), h, EquivLike.injective_comp]

end Naturality

/-- Apply a linear functional to the right factor of a tensor, linearly in the functional. -/
noncomputable def tensorComponent : (N →ₗ[R] R) →ₗ[R] M ⊗[R] N →ₗ[R] M :=
  (LinearMap.compRight R (TensorProduct.rid R M).toLinearMap).comp (LinearMap.lTensorHom M)

/-- Contraction is the tensor product of the functional with the identity, followed by the
right tensor unitor. -/
theorem tensorComponent_def (phi : N →ₗ[R] R) :
    tensorComponent (M := M) phi = (TensorProduct.rid R M).toLinearMap ∘ₗ phi.lTensor M := (rfl)

/-- A right tensor component sends a pure tensor to the corresponding scalar multiple. -/
@[simp]
theorem tensorComponent_tmul (phi : N →ₗ[R] R) (m : M) (n : N) :
    tensorComponent (R := R) (M := M) phi (m ⊗ₜ[R] n) = phi n • m := by
  simp [tensorComponent]

/-- Taking a right tensor component commutes with a map on both tensor factors. -/
@[simp]
theorem tensorComponent_map {M' : Type x} {N' : Type y}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (phi : N' →ₗ[R] R) (f : M →ₗ[R] M') (g : N →ₗ[R] N') (t : M ⊗[R] N) :
    tensorComponent phi (TensorProduct.map f g t) =
      f (tensorComponent (phi.comp g) t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp

section

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Contraction of the last tensor factor commutes with reassociation. -/
@[simp]
theorem tensorComponent_assoc_symm (phi : P →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    LinearMap.tensorComponent phi ((TensorProduct.assoc R M N P).symm u) =
      (LinearMap.tensorComponent phi).lTensor M u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p =>
      simp only [TensorProduct.assoc_symm_tmul, LinearMap.tensorComponent_tmul,
        LinearMap.lTensor_tmul, TensorProduct.tmul_smul]

/-- Applying two tensor components successively is contraction by the composed functional
on the last two factors, after reassociation. -/
theorem tensorComponent_comp_tensorComponent (phi : N →ₗ[R] R) (psi : P →ₗ[R] R) :
    tensorComponent (M := M) phi ∘ₗ tensorComponent (M := M ⊗[R] N) psi =
      tensorComponent (M := M) (phi ∘ₗ tensorComponent psi) ∘ₗ
        (TensorProduct.assoc R M N P).toLinearMap := by
  refine TensorProduct.ext_threefold fun m n p ↦ ?_
  simp [smul_smul]

/-- Applying functionals to both factors is independent of the order of contraction. -/
theorem comp_tensorComponent (psi : M →ₗ[R] R) (phi : N →ₗ[R] R) :
    psi ∘ₗ LinearMap.tensorComponent phi =
      phi ∘ₗ (TensorProduct.lid R N).toLinearMap ∘ₗ psi.rTensor N := by
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.tensorComponent_tmul, map_smul,
    smul_eq_mul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    mul_comm]

end

/-- The right tensor unitor is natural with respect to a linear map in its left factor. -/
@[simp]
theorem rid_rTensor_apply (f : M →ₗ[R] N) (t : M ⊗[R] R) :
    TensorProduct.rid R N (rTensor R f t) = f (TensorProduct.rid R M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The Casimir element of a trace

Let `φ : A →ₗ[k] k` be a trace on a `k`-algebra `A`, so `φ (a * b) = φ (b * a)`, and let `x` and
`y` be finite families dual to each other for the pairing `(a, b) ↦ φ (a * b)`, in the sense that
every element expands in either family with coefficients read off by pairing against the other:

```text
a = ∑ i, φ (a * y i) • x i,        a = ∑ i, φ (x i * a) • y i.
```

For a finite free symmetric Frobenius algebra, a basis and its dual basis give such families;
the expansion identities also allow redundant families. The **Casimir element** `∑ i, x i ⊗ y i`
of `A ⊗[k] A` then commutes with `A` in the bimodule sense:

```text
∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a).
```

This is what makes `1 ↦ ∑ i, x i ⊗ y i` a map of `A`-bimodules `A → A ⊗[k] A`, the coevaluation of
a symmetric Frobenius algebra; for a Frobenius coalgebra in Mathlib's sense
(`Coalgebra.IsFrobenius`) with counit `φ`, the element is the comultiplication of `1`.

The tensor identity itself needs only a `k`-module `A` with an associative multiplication.
No multiplicative identity, distributivity, or compatibility with scalar multiplication is needed.

-/

section Casimir

variable {k A : Type*} [CommSemiring k] [AddCommMonoid A] [Semigroup A] [Module k A]

/-- **The Casimir element of a trace commutes with multiplication.** If `φ` is a trace on `A`
and the finite families `x` and `y` are dual for `(a, b) ↦ φ (a * b)`, then
`∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a)` for every `a : A`. -/
theorem sum_mul_tmul_eq_sum_tmul_mul {ι : Type*} [Fintype ι] (φ : A →ₗ[k] k)
    (hφ : ∀ a b : A, φ (a * b) = φ (b * a)) {x y : ι → A}
    (hx : ∀ a : A, ∑ i, φ (a * y i) • x i = a) (hy : ∀ a : A, ∑ i, φ (x i * a) • y i = a)
    (a : A) :
    ∑ i, (a * x i) ⊗ₜ[k] y i = ∑ i, x i ⊗ₜ[k] (y i * a) := by
  -- Expand each `a * x i` in the family `x`; the coefficients then match those of the expansion
  -- of `y j * a` in the family `y`, by the trace property.
  have expand (i : ι) :
      (a * x i) ⊗ₜ[k] y i = ∑ j, x j ⊗ₜ[k] (φ (x i * (y j * a)) • y i) := by
    conv_lhs => rw [← hx (a * x i)]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, mul_assoc, hφ, mul_assoc]
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.tmul_sum, hy]

end Casimir

end LinearMap
end
end TAF_LiteralSource_0392

section TAF_LiteralSource_0393
/- Original module: TauCeti.LinearAlgebra.TensorProduct.Basis -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor-product basis coordinates

This file records how contractions against one factor of a tensor product detect equality when
that factor is projective, and how coordinates in a basis of one factor commute with maps of the
other.
It also proves that the coordinates in bases obtained by scalar extension commute with a map of
the scalar-extension algebras, and that over a basis with at most one index a scalar extension
consists of pure tensors.

## Main declarations

* `TensorProduct.tensor_eq_of_forall_tensorComponent_eq`: contractions against a projective right
  factor detect equality.
* `Module.Basis.equivFinsuppOfBasisLeft_lTensor_apply` and
  `Module.Basis.lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft`: coordinates in a basis of
  the left factor commute with maps of the right factor, so such a map kills an element exactly
  when it kills every coordinate.
* `Module.Basis.map_baseChange_repr`: applying a scalar map to a coordinate in a base-changed
  basis agrees with first mapping the tensor and then taking its coordinate.
* `Module.Basis.eq_baseChange_repr_tmul_of_subsingleton`: over a basis with at most one index,
  every element of a scalar extension is the pure tensor of its unique coordinate with the
  corresponding basis vector.
* `Module.Basis.baseChange_toMatrix_baseChange`: change-of-basis matrices between base-changed
  bases are obtained by mapping entries.
* `Module.Basis.map_toMatrixAlgEquiv_baseChange`: matrices in base-changed bases commute with
  scalar maps when the represented endomorphisms are intertwined by tensor-product base change.
* `Module.Basis.toMatrix_baseChange_baseChange`: matrices of scalar-extended linear maps
  are obtained by mapping entries.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Equality of all contractions against the right factor detects equality in a tensor product
over a commutative semiring when the right factor is projective. -/
theorem tensor_eq_of_forall_tensorComponent_eq [Module.Projective R N] {x y : M ⊗[R] N}
    (h : ∀ φ : Module.Dual R N,
      _root_.LinearMap.tensorComponent (R := R) (M := M) φ x =
        _root_.LinearMap.tensorComponent (R := R) (M := M) φ y) :
    x = y := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R N)
  let b := Finsupp.basisSingleOne (R := R) (ι := N)
  have hmap : TensorProduct.map LinearMap.id s x = TensorProduct.map LinearMap.id s y := by
    apply (TensorProduct.equivFinsuppOfBasisRight b (M := M)).injective
    ext i
    have hcoord :
        _root_.LinearMap.tensorComponent (b.coord i) (TensorProduct.map LinearMap.id s x) =
        _root_.LinearMap.tensorComponent (b.coord i) (TensorProduct.map LinearMap.id s y) := by
      simpa only [_root_.LinearMap.tensorComponent_map, LinearMap.id_apply] using
        h ((b.coord i).comp s)
    simpa only [TensorProduct.equivFinsuppOfBasisRight_apply,
      _root_.LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe] using hcoord
  have := congrArg (TensorProduct.map LinearMap.id (Finsupp.linearCombination R id)) hmap
  simpa only [TensorProduct.map_map, LinearMap.id_comp, hs, TensorProduct.map_id,
    LinearMap.id_apply] using this

end TensorProduct

namespace Module.Basis

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

section EquivFinsuppOfBasisLeft

variable {ι : Type*} [DecidableEq ι] {P : Type*} [AddCommMonoid P] [Module R P]
variable (ℬ : Module.Basis ι R M)

/-- Coordinates in a basis of the left factor commute with maps of the right factor. -/
@[simp]
theorem equivFinsuppOfBasisLeft_lTensor_apply (g : N →ₗ[R] P) (x : M ⊗[R] N) (i : ι) :
    equivFinsuppOfBasisLeft ℬ (g.lTensor M x) i = g (equivFinsuppOfBasisLeft ℬ x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul m n => simp

/-- Over a basis of the left factor, a map of the right factor kills an element of the tensor
product exactly when it kills each of its coordinates. -/
theorem lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft (g : N →ₗ[R] P) (x : M ⊗[R] N) :
    g.lTensor M x = 0 ↔ ∀ i, g (equivFinsuppOfBasisLeft ℬ x i) = 0 := by
  rw [← (equivFinsuppOfBasisLeft ℬ).map_eq_zero_iff, Finsupp.ext_iff]
  simp

end EquivFinsuppOfBasisLeft

end Module.Basis

namespace Module.Basis

universe u v w x

variable {R : Type u} [CommSemiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {ι : Type*}

section Repr

variable {S : Type v} [Semiring S] [Algebra R S]
variable {T : Type w} [Semiring T] [Algebra R T]

/-- Coordinates in a base-changed basis are natural in the scalar-extension algebra. -/
@[simp] theorem map_baseChange_repr (b : Basis ι R M) (φ : S →ₗ[R] T)
    (z : S ⊗[R] M) (i : ι) :
    φ ((b.baseChange S).repr z i) =
      (b.baseChange T).repr
        (TensorProduct.map φ LinearMap.id z) i := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul s m => simp

/-- Over a basis with at most one index, every element of a scalar extension is the pure tensor
of its unique coordinate with the corresponding basis vector.  This isolates the tensor
bookkeeping needed to reduce statements about rank-at-most-one scalar extensions to scalar
multiples of a single vector. -/
theorem eq_baseChange_repr_tmul_of_subsingleton [Subsingleton ι] (b : Basis ι R M)
    (z : S ⊗[R] M) (i : ι) :
    z = (b.baseChange S).repr z i ⊗ₜ b i := by
  let _ : Fintype ι := Fintype.ofFinite ι
  conv_lhs => rw [← (b.baseChange S).sum_repr z]
  rw [Fintype.sum_subsingleton _ i, baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

end Repr

section Matrix

variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {T : Type w} [CommSemiring T] [Algebra R T]

/-- The change-of-basis matrix between two base-changed bases is the entrywise scalar extension
of the change-of-basis matrix between the original bases. -/
@[simp] theorem baseChange_toMatrix_baseChange {ι' : Type*} (b : Basis ι R M)
    (b' : Basis ι' R M) :
    (b.baseChange S).toMatrix (b'.baseChange S) = (b.toMatrix b').map (algebraMap R S) := by
  ext i j
  simp [toMatrix_apply, baseChange_apply, Algebra.smul_def]

variable [Fintype ι] [DecidableEq ι]

/-- The matrix of a scalar-extended linear map is the entrywise scalar extension of its
matrix in the original source and target bases. -/
@[simp] theorem toMatrix_baseChange_baseChange {κ N : Type*} [Finite κ]
    [AddCommMonoid N] [Module R N] (b : Basis ι R M) (c : Basis κ R N) (f : M →ₗ[R] N) :
    LinearMap.toMatrix (b.baseChange S) (c.baseChange S) (f.baseChange S) =
      (LinearMap.toMatrix b c f).map (algebraMap R S) := by
  ext i j
  simp [LinearMap.toMatrix_apply, baseChange_apply, Algebra.smul_def]

/-- Matrices in base-changed bases commute with a scalar map when the corresponding
endomorphisms are intertwined by tensor-product base change. -/
theorem map_toMatrixAlgEquiv_baseChange (b : Basis ι R M) (φ : S →ₐ[R] T)
    (f : S ⊗[R] M →ₗ[S] S ⊗[R] M) (g : T ⊗[R] M →ₗ[T] T ⊗[R] M)
    (h : ∀ z, TensorProduct.map φ.toLinearMap LinearMap.id (f z) =
      g (TensorProduct.map φ.toLinearMap LinearMap.id z)) :
    (LinearMap.toMatrixAlgEquiv (b.baseChange S) f).map φ =
      LinearMap.toMatrixAlgEquiv (b.baseChange T) g := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrixAlgEquiv_apply, ← AlgHom.toLinearMap_apply,
    map_baseChange_repr b φ.toLinearMap]
  apply congrArg (fun z => (b.baseChange T).repr z i)
  rw [h]
  simp only [baseChange_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    LinearMap.id_apply, map_one]

end Matrix

end Module.Basis
end
end TAF_LiteralSource_0393

section TAF_LiteralSource_0394
/- Original module: TauCeti.LinearAlgebra.TensorProduct.Separation -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/


/-!
# Separating tensors by linear maps

Families of linear maps detecting zero in the left factor also detect zero after tensoring
with a projective right factor over a commutative semiring. Products of separating families
of linear functionals likewise detect zero tensors by contraction in both factors.
These lemmas supply the shared separation step for rational-point separation and reducedness
of tensor products of algebras. Over a field, every module is projective.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Tensoring a family of linear maps detecting zero with a projective module preserves
zero detection. The maps may take values in any module. -/
theorem tensor_eq_zero_of_forall_rTensor_eq_zero
    {R M N P ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    [AddCommMonoid P] [Module R P]
    (f : ι → M →ₗ[R] P) (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (x : M ⊗[R] N) (hx : ∀ i, (f i).rTensor N x = 0) :
    x = 0 := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [map_zero]
  apply hf
  intro i
  simpa only [← LinearMap.rTensor_def, hx i, map_zero, LinearMap.comp_id] using
    (LinearMap.tensorComponent_map φ (f i) LinearMap.id x).symm

/-- Products of separating families of linear functionals detect zero tensors when the
right factor is projective. -/
theorem tensor_eq_zero_of_forall_lid_map_eq_zero
    {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    (f : ι → M →ₗ[R] R) (g : κ → N →ₗ[R] R)
    (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (hg : ∀ n, (∀ j, g j n = 0) → n = 0)
    (x : M ⊗[R] N)
    (hx : ∀ i j, TensorProduct.lid R R (TensorProduct.map (f i) (g j) x) = 0) :
    x = 0 := by
  apply tensor_eq_zero_of_forall_rTensor_eq_zero f hf x
  intro i
  apply (TensorProduct.lid R N).injective
  simp only [map_zero]
  apply hg
  intro j
  have hcomp : (g j).comp ((TensorProduct.lid R N).toLinearMap.comp
      (TensorProduct.map (f i) LinearMap.id)) =
      (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map (f i) (g j)) := by
    ext m n
    simp
  exact (DFunLike.congr_fun hcomp x).trans (hx i j)

end TauCeti
end
end TAF_LiteralSource_0394

section TAF_LiteralSource_0395
/- Original module: TauCeti.RepresentationTheory.Irreducible -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Criteria for irreducibility

This file collects criteria for recognising irreducible representations without inspecting their
subrepresentations one by one, together with existence, density, and Schur lemmas for
finite-dimensional representations.

A representation on a one-dimensional vector space is irreducible, whatever the group and however
it acts: a subrepresentation is in particular a subspace, and a line has only the two trivial
subspaces.  Nontriviality, the other half of irreducibility, is the same dimension count.  This is
how the smallest representations of a group are recognised as irreducible without knowing anything
about the group -- the trivial representation, a character, a sign.

The second criterion turns a lattice-theoretic statement about a fixed ambient representation into
a statement about a subrepresentation on its own: a subrepresentation that is an **atom** of the
lattice of subrepresentations carries an irreducible representation.  Irreducibility of a
subrepresentation `σ` of `ρ` is a statement about the subrepresentations of `σ.toRepresentation`,
one level down from `ρ`, whereas minimality is a statement inside the lattice attached to `ρ`; the
translation between them is the correspondence sending a subrepresentation of `σ.toRepresentation`
to its image in `ρ` under the inclusion of `σ.toSubmodule`.  In practice the atom form is the one
that gets proved -- one exhibits an invariant subspace of the ambient representation and shows it
has no proper nonzero invariant subspace -- and the irreducibility form is the one that gets used.

At the other extreme, a representation whose algebra map exhausts `End k V` is irreducible, because
a vector space is a simple module over its own endomorphism ring, so a nonzero vector can be carried
to any other.  This is the criterion a matrix block of a semisimple group algebra is recognised as
irreducible by.

## Main results

* `Representation.IsIrreducible.nontrivial`: an irreducible representation has a nonzero
  carrier.
* `Representation.IsIrreducible.finrank_pos`: a finite-dimensional irreducible
  representation has positive dimension.
* `Representation.IsIrreducible.natCast_finrank_ne_zero`: in characteristic zero that
  dimension is nonzero, hence invertible, in the base field.
* `Representation.isIrreducible_of_finrank_eq_one`: a line is irreducible.
* `Representation.isIrreducible_of_linearEquiv`: irreducibility transports along an
  equivariant linear equivalence.
* `Representation.isIrreducible_toRepresentation_of_isAtom`: an atom of the lattice of
  subrepresentations carries an irreducible representation.
* `Representation.isIrreducible_of_asAlgebraHom_surjective`: a representation whose
  algebra map exhausts the endomorphisms is irreducible.
* `Representation.isIrreducible_of_finrank_intertwiningMap_self_eq_one`: a semisimple
  representation whose equivariant endomorphisms are the scalars is irreducible.
* `Representation.IsIrreducible.eq_one_or_eq_neg_one_of_mul_self_eq_one`: Schur's lemma for an
  involutive equivariant endomorphism, over any field.
* `Representation.asAlgebraHom_surjective_of_isIrreducible`: over an algebraically closed
  field, every finite-dimensional irreducible representation exhausts the endomorphisms.
* `Representation.exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul`: consequently the
  monoid algebra, acting on the left factor of a nonzero tensor in `V ⊗ M`, reaches every
  `v ⊗ m` for one fixed nonzero `m`.
* `Representation.exists_isAtom_le`: every nonzero finite-dimensional subrepresentation
  contains an atom, so the atom criterion always has something to apply to.
* `Representation.exists_isAtom`: in particular a nonzero finite-dimensional
  representation has an atom.
* `Representation.exists_isIrreducible_subrepresentation`: consequently every nonzero
  finite-dimensional representation contains an irreducible subrepresentation.
* `Representation.IsIrreducible.exists_forall_apply_eq_smul`: Schur's lemma over an
  algebraically closed field, for an unbundled equivariant endomorphism.
* `Representation.IsIrreducible.exists_unit_smul_of_intertwines`: two equivariant isomorphisms
  out of an irreducible representation differ by a unit scalar.
-/

public section

open TauCeti
open scoped TensorProduct

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

open scoped MonoidAlgebra in
/-- **An irreducible representation has a nonzero carrier.** This is `IsSimpleModule.nontrivial`
for `ρ.asModule`, read back on `V` along `ρ.asModuleEquiv`; the Mathlib statement is not an
instance, so nothing supplies `Nontrivial V` without naming it. -/
theorem IsIrreducible.nontrivial {ρ : Representation k G V}
    (h : ρ.IsIrreducible) : Nontrivial V :=
  have _ : ρ.IsIrreducible := h
  have _ := IsSimpleModule.nontrivial k[G] ρ.asModule
  ρ.asModuleEquiv.symm.toEquiv.nontrivial

/-- **A finite-dimensional irreducible representation has positive dimension.** This is what makes
the degree of an irreducible character positive, and, cast into the base field by
`Representation.IsIrreducible.natCast_finrank_ne_zero`, what lets the orthogonality relations and
the integrated operator divide by that degree. -/
theorem IsIrreducible.finrank_pos [FiniteDimensional k V]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) : 0 < Module.finrank k V :=
  have := h.nontrivial
  Module.finrank_pos

/-- **The dimension of an irreducible representation is nonzero in the base field.** In
characteristic zero it is therefore invertible there: this is the scalar the orthogonality
relations and the integrated operator of an irreducible representation are normalised by. -/
theorem IsIrreducible.natCast_finrank_ne_zero [CharZero k]
    [FiniteDimensional k V] {ρ : Representation k G V} (h : ρ.IsIrreducible) :
    (Module.finrank k V : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr h.finrank_pos.ne'

/-- A representation on a one-dimensional vector space is irreducible. -/
theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V)
    (h : Module.finrank k V = 1) : ρ.IsIrreducible := by
  have : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  have : Nontrivial V := IsSimpleModule.nontrivial k V
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_top.symm)

/-- The trivial representation of a monoid on the base field is irreducible, being a line. -/
instance isIrreducible_trivial_self : (trivial k G k).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- **Irreducibility transports along an equivariant linear equivalence.** A linear equivalence
intertwining two representations matches their lattices of subrepresentations, by taking preimages
of invariant subspaces, so one is irreducible exactly when the other is.

Only one direction is stated; the reverse is this one applied to `e.symm`. -/
theorem isIrreducible_of_linearEquiv {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  have := h.nontrivial
  have : Nontrivial W := e.symm.toEquiv.nontrivial
  refine ⟨fun τ => ?_⟩
  -- pull `τ` back along `e` to a subrepresentation of `ρ`
  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.comap (e : V →ₗ[k] W)
      apply_mem_toSubmodule g v hv := by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [he]
        exact τ.apply_mem_toSubmodule g hv }
  have hmap : (τ'.toSubmodule).map (e : V →ₗ[k] W) = τ.toSubmodule :=
    Submodule.map_comap_eq_of_surjective e.surjective _
  refine (eq_bot_or_eq_top τ').imp (fun hτ => ?_) fun hτ => ?_
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_bot, Submodule.map_bot,
      Subrepresentation.toSubmodule_bot]
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_top, Submodule.map_top, LinearEquiv.range,
      Subrepresentation.toSubmodule_top]

/-- A subrepresentation that is an **atom** of the lattice of subrepresentations -- nonzero, with
no subrepresentation strictly between it and zero -- carries an irreducible representation.  The
translation is the correspondence between the subrepresentations of `σ.toRepresentation` and the
subrepresentations of `ρ` contained in `σ`, given by pushing forward along the inclusion. -/
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (h : IsAtom σ) : σ.toRepresentation.IsIrreducible := by
  rw [irreducible_iff_isSimpleModule_asModule,
    σ.asModuleEquivAsSubmodule.isSimpleModule_iff, Subrepresentation.isSimpleModule_asSubmodule_iff]
  exact h

/-- **A representation whose algebra map exhausts the endomorphisms is irreducible.** Every nonzero
vector then generates, because a vector space is a simple module over its endomorphism ring. -/
theorem isIrreducible_of_asAlgebraHom_surjective [Nontrivial V] (ρ : Representation k G V)
    (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨ρ.asModuleEquiv.toEquiv.nontrivial, fun x hx y => ?_⟩
  obtain ⟨T, hT⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End k V)
    (m := ρ.asModuleEquiv x) (by
      intro hz
      apply hx
      apply ρ.asModuleEquiv.injective
      simpa only [map_zero] using hz) (ρ.asModuleEquiv y)
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hT
  obtain ⟨r, rfl⟩ := h T
  refine ⟨r, ρ.asModuleEquiv.injective ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Representation.asModuleEquiv_map_smul, hT]

/-- **A semisimple representation whose intertwiners are the scalars is irreducible.** If every
subrepresentation has an invariant complement and the equivariant endomorphisms of `ρ` form a line,
then `ρ` is irreducible: an idempotent equivariant endomorphism is a scalar `c` with `c * c = c`,
hence `0` or `1`, so `ρ` is indecomposable (`isIndecomposableModule_of_forall_isIdempotentElem`),
and an indecomposable semisimple module is simple (`IsIndecomposableModule.isSimpleModule`).

Over a field in which the order of a finite group is invertible every representation is semisimple
(Maschke), so there this is the converse of Schur's lemma for an absolutely irreducible
representation. -/
theorem isIrreducible_of_finrank_intertwiningMap_self_eq_one {ρ : Representation k G V}
    [ρ.IsSemisimpleRepresentation] (h : Module.finrank k (IntertwiningMap ρ ρ) = 1) :
    ρ.IsIrreducible := by
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : Subsingleton (IntertwiningMap ρ ρ) :=
      ⟨fun f g => IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  have hid : (1 : IntertwiningMap ρ ρ) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact fun h0 => hv (by simpa using congrArg (fun f : IntertwiningMap ρ ρ => f v) h0)
  have : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  have : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  rw [irreducible_iff_isSimpleModule_asModule]
  -- an idempotent endomorphism is a scalar `c` with `c * c = c`, hence `0` or `1`
  refine (isIndecomposableModule_of_forall_isIdempotentElem fun f hf => ?_).isSimpleModule
  let e := IntertwiningMap.equivAlgEnd (ρ := ρ)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).mp h (e.symm f)
  have hf' : f = algebraMap k _ c := by
    rw [← e.apply_symm_apply f, ← hc, ← AlgEquiv.commutes e, IntertwiningMap.algebraMap_apply]
  have hcc : IsIdempotentElem c := by
    refine smul_left_injective k hid ?_
    simpa [hf', IsIdempotentElem, ← map_mul, mul_smul] using congrArg e.symm hf
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with rfl | rfl
  · exact Or.inl (by simp [hf'])
  · exact Or.inr (by simp [hf'])

/-- **An involutive equivariant endomorphism of an irreducible representation is `±1`.** By Schur's
lemma the equivariant endomorphisms of an irreducible representation form a division ring, in which
`f * f = 1` forces `f = 1` or `f = -1`. No algebraic closure or finite dimension is needed. -/
theorem IsIrreducible.eq_one_or_eq_neg_one_of_mul_self_eq_one {ρ : Representation k G V}
    (hρ : ρ.IsIrreducible) {f : IntertwiningMap ρ ρ} (hf : f * f = 1) : f = 1 ∨ f = -1 := by
  classical
  let := hρ
  let e := IntertwiningMap.equivAlgEnd (ρ := ρ)
  have he : e f * e f = 1 := by rw [← map_mul, hf, map_one]
  exact (mul_self_eq_one_iff.mp he).imp
    (fun h ↦ e.injective (by simpa using h)) fun h ↦ e.injective (by simpa using h)

open scoped MonoidAlgebra in
/-- **Burnside density theorem.** The monoid algebra of a finite-dimensional irreducible
representation over an algebraically closed field exhausts the full endomorphism algebra.

Jacobson density gives all endomorphisms linear over the representation's commuting endomorphism
ring. Schur's lemma identifies that ring with the base field, so these are exactly the
`k`-linear endomorphisms. -/
theorem asAlgebraHom_surjective_of_isIrreducible
    [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ρ.IsIrreducible) :
    Function.Surjective ρ.asAlgebraHom := by
  have : ρ.IsIrreducible := hρ
  have : IsSimpleModule k[G] ρ.asModule := inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  have : Nontrivial V := hρ.nontrivial
  have : Module.Finite (Module.End k[G] ρ.asModule) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k (Module.End k[G] ρ.asModule) ρ.asModule
  intro T
  let T' : Module.End (Module.End k[G] ρ.asModule) ρ.asModule :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x ↦ by
        -- `T` acts on `V`, while `f` acts on the definitionally equal type synonym
        -- `ρ.asModule`; exposing function application is required before Schur's scalar
        -- description is type-correct.
        change T (f x) = f (T x)
        rw [← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f x,
          ← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f (T x)]
        exact T.map_smul _ _ }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := k[G]) (M := ρ.asModule) T'
  refine ⟨a, LinearMap.ext fun x ↦ ?_⟩
  have hT' (y : ρ.asModule) : T' y = T y := rfl
  have hx := LinearMap.congr_fun ha (ρ.asModuleEquiv.symm x)
  rw [hT'] at hx
  have hx' := congrArg ρ.asModuleEquiv hx
  have hT_equiv : ρ.asModuleEquiv (T (ρ.asModuleEquiv.symm x)) = T x := rfl
  rw [hT_equiv] at hx'
  simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply,
    Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using hx'

open scoped MonoidAlgebra in
/-- **Burnside density on a tensor product.** Let `ρ` be a finite-dimensional irreducible
representation over an algebraically closed field and `M` any vector space. Acting on the left
factor of a nonzero `z ∈ V ⊗ M` by the monoid algebra reaches every pure tensor `v ⊗ m` with one
fixed nonzero `m`: there is `m ≠ 0` such that for each `v` some `r ∈ k[G]` has
`(ρ r ⊗ 1) z = v ⊗ m`. -/
theorem exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul
    [IsAlgClosed k] [FiniteDimensional k V] (ρ : Representation k G V) (hρ : ρ.IsIrreducible)
    {M : Type*} [AddCommGroup M] [Module k M] {z : V ⊗[k] M} (hz : z ≠ 0) :
    ∃ m : M, m ≠ 0 ∧ ∀ v : V, ∃ r : k[G], (ρ.asAlgebraHom r).rTensor M z = v ⊗ₜ m := by
  -- Some linear functional on `V` contracts `z` to a nonzero vector of `M`.
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k V, _root_.TensorProduct.lid k M (f.rTensor M z) ≠ 0 := by
    by_contra! H
    apply hz
    apply tensor_eq_zero_of_forall_rTensor_eq_zero (fun f : Module.Dual k V ↦ f)
      (fun v hv ↦ (Module.forall_dual_apply_eq_zero_iff k v).1 hv) z
    intro f
    apply (_root_.TensorProduct.lid k M).injective
    simpa only [map_zero] using H f
  refine ⟨_, hf, fun v ↦ ?_⟩
  -- By density the rank-one endomorphism `x ↦ f x • v` is the action of some `r`.
  obtain ⟨r, hr⟩ := asAlgebraHom_surjective_of_isIrreducible ρ hρ (f.smulRight v)
  have key (w : V ⊗[k] M) :
      (f.smulRight v).rTensor M w = v ⊗ₜ _root_.TensorProduct.lid k M (f.rTensor M w) := by
    induction w using _root_.TensorProduct.inductionOn with
    | tmul x m => simp [_root_.TensorProduct.smul_tmul]
    | add w w' hw hw' => simp only [map_add, hw, hw', _root_.TensorProduct.tmul_add]
  exact ⟨r, by rw [hr, key]⟩

/-! ### Atoms exist in finite dimensions -/

section DivisionRing

variable {k G V : Type*} [DivisionRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **Atoms exist.** Every nonzero finite-dimensional subrepresentation contains an atom of the
lattice of subrepresentations.

Finite-dimensionality is what makes a minimal nonzero subrepresentation exist, and only the
subrepresentation being minimised inside has to be finite-dimensional: the ambient representation
may be infinite-dimensional, the scalars need only be a division ring, and the acting monoid stays
arbitrary.  Over a field it combines with
`Representation.isIrreducible_toRepresentation_of_isAtom` to exhibit an irreducible
subrepresentation inside any nonzero one; that companion needs the field, because
`Representation.IsIrreducible` is defined only there. -/
theorem exists_isAtom_le {ρ : Representation k G V} {σ : Subrepresentation ρ}
    [FiniteDimensional k σ.toSubmodule] (hσ : σ ≠ ⊥) :
    ∃ τ : Subrepresentation ρ, τ ≤ σ ∧ IsAtom τ := by
  -- Among the nonzero subrepresentations contained in `σ`, pick one whose subspace has least
  -- dimension; the dimensions are natural numbers, so such a one exists.
  obtain ⟨τ, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT (fun τ : Subrepresentation ρ => τ ≠ ⊥ ∧ τ ≤ σ)
      (fun τ => Module.finrank k τ.toSubmodule) ⟨σ, hσ, le_rfl⟩
  obtain ⟨hτ, hτσ⟩ := hmin.1
  have : FiniteDimensional k τ.toSubmodule :=
    Submodule.finiteDimensional_of_le (Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ)
  -- Anything strictly inside `τ` is again inside `σ` and of strictly smaller dimension, so
  -- minimality forces it to be zero.
  refine ⟨τ, hτσ, hτ, fun υ hυ => ?_⟩
  by_contra hυ0
  exact hmin.not_prop_of_lt
    (Submodule.finrank_lt_finrank_of_lt (Subrepresentation.toSubmodule_lt_toSubmodule.mpr hυ))
    ⟨hυ0, hυ.le.trans hτσ⟩

/-- **A nonzero finite-dimensional representation has a minimal nonzero subrepresentation.**  This
is `Representation.exists_isAtom_le` applied to the whole space, which is nonzero exactly
because `V` is; the scalars need only be a division ring and the acting monoid stays arbitrary. -/
theorem exists_isAtom [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, IsAtom σ :=
  let ⟨σ, _, hσ⟩ := exists_isAtom_le top_ne_bot
  ⟨σ, hσ⟩

end DivisionRing

/-- **Schur's lemma, scalar form.** Over an algebraically closed field, a linear endomorphism of a
finite-dimensional irreducible representation commuting with the action is multiplication by a
scalar.  This is `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`
read pointwise on an unbundled endomorphism. -/
theorem IsIrreducible.exists_forall_apply_eq_smul [IsAlgClosed k] [FiniteDimensional k V]
    {ρ : Representation k G V} [ρ.IsIrreducible] (f : V →ₗ[k] V)
    (hf : ∀ g v, f (ρ g v) = ρ g (f v)) : ∃ c : k, ∀ v, f v = c • v := by
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective (f.intertwiningMap_of_isIntertwiningMap ρ ρ hf)
  refine ⟨c, fun v ↦ ?_⟩
  simpa [IntertwiningMap.algebraMap_apply] using (DFunLike.congr_fun hc v).symm

/-- **Two equivariant isomorphisms out of an irreducible representation differ by a unit
scalar.**  If `a b : V ≃ₗ[k] W` both carry the action `ρ` to the same `σ`, then `b⁻¹ ∘ a` is an
equivariant automorphism of `V`, hence a nonzero scalar by Schur's lemma
(`Representation.IsIrreducible.exists_forall_apply_eq_smul`). -/
theorem IsIrreducible.exists_unit_smul_of_intertwines [IsAlgClosed k] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] {ρ : Representation k G V} [hρ : ρ.IsIrreducible]
    {σ : Representation k G W} (a b : V ≃ₗ[k] W)
    (ha : ∀ g v, a (ρ g v) = σ g (a v)) (hb : ∀ g v, b (ρ g v) = σ g (b v)) :
    ∃ c : kˣ, ∀ v, a v = (c : k) • b v := by
  have : Nontrivial V := hρ.nontrivial
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_smul (ρ := ρ) (a.trans b.symm).toLinearMap
    fun g v ↦ b.injective (by simp [ha, hb])
  have hne : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv ((a.trans b.symm).injective (by simpa using hc v))
  refine ⟨Units.mk0 c hne, fun v ↦ ?_⟩
  simpa using congrArg b (hc v)

/-- **Every nonzero finite-dimensional representation contains an irreducible subrepresentation.**
Finite-dimensionality alone suffices; no semisimplicity is assumed.  This produces a single
irreducible subrepresentation, not a decomposition: a representation that is not semisimple need
not be the sum of its irreducible subrepresentations. -/
theorem exists_isIrreducible_subrepresentation [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, σ ≠ ⊥ ∧ σ.toRepresentation.IsIrreducible := by
  obtain ⟨σ, hσ⟩ := exists_isAtom ρ
  exact ⟨σ, hσ.1, isIrreducible_toRepresentation_of_isAtom hσ⟩

end Representation
end
end TAF_LiteralSource_0395

section TAF_LiteralSource_0396
/- Original module: TauCeti.RepresentationTheory.LinearCharacter.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# One-dimensional representations from linear characters

A **linear character** of a monoid `G` over a commutative semiring `k` is a multiplicative
character `χ : G →* kˣ`. It acts on the one-dimensional `k`-module `k` by scalar multiplication.
This file packages that action as `Representation.ofLinearCharacter χ`, bundles it as an object
`FDRep.ofLinearCharacter χ` of `FDRep k G`, and records the facts every consumer of a linear
character needs: over a field its character is `χ` and it is simple; over a commutative ring it
has rank one. Restriction along a homomorphism pulls `χ` back, and two of these representations
are isomorphic exactly when the two characters are equal.

The construction is the common core of the linear characters of the Borel subgroup and of
`GL₂`; keeping it here avoids separate scalar-action implementations for each group. It is also
the smallest nonzero representation over a field, and it is what the induction machinery is fed
in the classical worked examples: `Ind_H^G` of a linear character of a subgroup is a *monomial*
representation, and its irreducibility is what the Mackey criterion decides.

## Main definitions

* `Representation.ofLinearCharacter`: the one-dimensional representation associated to a
  unit-valued multiplicative character.
* `FDRep.ofLinearCharacter`: the same representation as an object of `FDRep k G`.

## Main results

* `Representation.ofLinearCharacter_apply`: the action is multiplication by the character value.
* `Representation.ofLinearCharacter_comp`: restriction of the representation is precomposition of
  the character.
* `Representation.ofLinearCharacter_injective`: the representation remembers its character.
* `Representation.ofLinearCharacter_one`: the trivial character carries the trivial
  representation.
* `Representation.char_ofLinearCharacter` and `FDRep.char_ofLinearCharacter`: the trace character
  is the original character, coerced into the coefficient field.
* `Representation.isIrreducible_ofLinearCharacter`: a line has no room for a proper nonzero
  subrepresentation.
* `Representation.IsIrreducible.nonempty_equiv_ofLinearCharacter_iff`: an irreducible
  representation is the line of `χ` exactly when each `g` acts by the scalar `χ g`.
* `FDRep.ofLinearCharacter_def`: the bundled representation is the unbundled one, bundled.
* `FDRep.finrank_ofLinearCharacter`: it is a line.
* `FDRep.simple_ofLinearCharacter`: it is a simple object of `FDRep k G`, being a line.
* `FDRep.actionRes_obj_ofLinearCharacter`: restricting along `f : S →* G` gives the
  one-dimensional representation of the pulled-back character `χ ∘ f`.
* `FDRep.nonempty_iso_ofLinearCharacter_iff`: two of these are isomorphic exactly when the two
  linear characters are equal.
* `FDRep.exists_character_eq_of_commute`: over an algebraically closed field, an irreducible
  representation whose operators commute pairwise has a linear character as its character.

## Implementation notes

Neither definition is exposed: consumers go through the lemmas rather than the body.
`FDRep.ofLinearCharacter_def` is the defining equation the dependent API is derived from, and with
Mathlib's `FDRep.of_ρ'` it recovers the action. Since both sides use the carrier `k`,
`FDRep.actionRes_obj_ofLinearCharacter` is an equality of objects; conjugation, restriction and
comparison of these objects are computed inside `G →* kˣ` through it and
`FDRep.nonempty_iso_ofLinearCharacter_iff`.
-/

public section

open CategoryTheory

universe u v

namespace Representation

variable {k : Type u} {G : Type v}

/-- **The one-dimensional representation associated to a multiplicative character.** An element
`g : G` acts on the line `k` by multiplication by the unit `χ g`. -/
def ofLinearCharacter [CommSemiring k] [Monoid G] (χ : G →* kˣ) : Representation k G k :=
  (Algebra.lsmul k k k).toMonoidHom.comp ((Units.coeHom k).comp χ)

/-- The representation associated to `χ` acts by multiplication by `χ`. -/
@[simp]
theorem ofLinearCharacter_apply [CommSemiring k] [Monoid G] (χ : G →* kˣ) (g : G) (x : k) :
    ofLinearCharacter χ g x = (χ g : k) * x :=
  (rfl)

/-- **Restricting a one-dimensional representation is precomposition of its character.** -/
@[simp]
theorem ofLinearCharacter_comp [CommSemiring k] [Monoid G] {H : Type*} [Monoid H]
    (χ : G →* kˣ) (f : H →* G) :
    (ofLinearCharacter χ).comp f = ofLinearCharacter (χ.comp f) := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro x
  rfl

/-- **The one-dimensional representation remembers its multiplicative character.** -/
theorem ofLinearCharacter_injective [CommSemiring k] [Monoid G] :
    Function.Injective (ofLinearCharacter : (G →* kˣ) → Representation k G k) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have := congrArg (fun ρ : Representation k G k => ρ g 1) h
  simpa using this

/-- **The trivial linear character carries the trivial representation.** This is the sanity check
that fixes the convention: `χ = 1` acts by the scalar `1`. -/
@[simp]
theorem ofLinearCharacter_one [CommSemiring k] [Monoid G] :
    ofLinearCharacter (1 : G →* kˣ) = Representation.trivial k G k :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by simp

/-- **The trace character of a one-dimensional representation is its multiplicative character.** -/
@[simp]
theorem char_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) (g : G) :
    (ofLinearCharacter χ).character g = (χ g : k) := by
  rw [character]
  have h : ofLinearCharacter χ g = LinearMap.id.smulRight (χ g : k) := by
    apply LinearMap.ext
    intro x
    simp [mul_comm]
  rw [h, LinearMap.trace_smulRight, LinearMap.id_apply]

/-- A one-dimensional representation is irreducible, having no room for a proper nonzero
subrepresentation. -/
instance isIrreducible_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    (ofLinearCharacter (k := k) χ).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- **An irreducible representation is the line of a linear character `χ` exactly when every `g`
acts by the scalar `χ g`.** If it does, a nonzero vector spans an equivariant copy of the line `k`,
and irreducibility makes this copy everything. -/
theorem IsIrreducible.nonempty_equiv_ofLinearCharacter_iff [Field k] [Monoid G] {V : Type*}
    [AddCommGroup V] [Module k V] {ρ : Representation k G V} (hρ : ρ.IsIrreducible)
    (χ : G →* kˣ) :
    Nonempty (ρ.Equiv (ofLinearCharacter χ)) ↔ ∀ g, ρ g = (χ g : k) • (1 : Module.End k V) := by
  refine ⟨fun ⟨e⟩ g ↦ LinearMap.ext fun v ↦ e.injective ?_, fun h ↦ ?_⟩
  · simpa using IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  let := hρ
  have := hρ.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- A nonzero vector spans an equivariant copy of the line, which Schur makes bijective.
  let f : IntertwiningMap (ofLinearCharacter χ) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c ↦ by
      simpa [h, mul_smul] using smul_comm (χ g : k) c v
  have hf : f ≠ 0 := fun h0 ↦ hv (by simpa [f] using DFunLike.congr_fun h0 1)
  exact ⟨(f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)).symm⟩

end Representation

namespace FDRep

variable {k : Type u} {G : Type v}

/-- **The one-dimensional representation carrying a linear character, as an object of
`FDRep k G`.** This is the shape induction consumes. -/
noncomputable def ofLinearCharacter [CommRing k] [Monoid G] (χ : G →* kˣ) : FDRep k G :=
  FDRep.of (Representation.ofLinearCharacter χ)

/-- **The bundled one-dimensional representation is the unbundled one, bundled.** This is the
defining equation of `FDRep.ofLinearCharacter`; with `FDRep.of_ρ'` it recovers the action, so
consumers never need to unfold the definition. -/
theorem ofLinearCharacter_def [CommRing k] [Monoid G] (χ : G →* kˣ) :
    ofLinearCharacter (k := k) χ = FDRep.of (Representation.ofLinearCharacter χ) :=
  (rfl)

/-- **Restricting a linear character along a homomorphism pulls the character back.** Both sides
are the line `k` with `s` acting by the scalar `χ (f s)`, so this is an equality of objects, not
merely an isomorphism; it is what lets conjugation and restriction of a one-dimensional
representation be computed inside `G →* kˣ`. -/
@[simp]
theorem actionRes_obj_ofLinearCharacter [CommRing k] [Monoid G] {S : Type*} [Monoid S]
    (f : S →* G) (χ : G →* kˣ) :
    (Action.res (FGModuleCat k) f).obj (ofLinearCharacter χ) = ofLinearCharacter (χ.comp f) :=
  (rfl)

/-- A linear character is carried by a line. -/
@[simp]
theorem finrank_ofLinearCharacter [CommRing k] [Monoid G] (χ : G →* kˣ) :
    Module.finrank k (ofLinearCharacter (k := k) χ) = 1 :=
  CommSemiring.finrank_self k

/-- **The character of `FDRep.ofLinearCharacter` is the linear character it was built from.** -/
@[simp]
theorem char_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) (g : G) :
    (ofLinearCharacter (k := k) χ).character g = (χ g : k) :=
  Representation.char_ofLinearCharacter χ g

/-- **The one-dimensional representation of a linear character is a simple object**, being a
line. -/
instance simple_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    Simple (ofLinearCharacter (k := k) χ) :=
  have : Representation.IsIrreducible (ofLinearCharacter (k := k) χ).ρ :=
    Representation.isIrreducible_ofLinearCharacter χ
  FDRep.simple_of_isIrreducible _

/-- **Two one-dimensional representations are isomorphic exactly when their linear characters
agree.** An isomorphism of lines is multiplication by the unit `f 1`, so equivariance reads
`χ g * f 1 = ψ g * f 1`, which that unit cancels from; conversely equal characters give literally
the same object. -/
@[simp]
theorem nonempty_iso_ofLinearCharacter_iff [CommRing k] [Monoid G] (χ ψ : G →* kˣ) :
    Nonempty (ofLinearCharacter (k := k) χ ≅ ofLinearCharacter ψ) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => MonoidHom.ext fun g => Units.ext ?_, fun h => ⟨h ▸ Iso.refl _⟩⟩
  rw [ofLinearCharacter_def, ofLinearCharacter_def] at e
  let f := isoToLinearEquiv e
  have hlin (c : k) : f c = c * f 1 := by simpa using f.map_smul c (1 : k)
  apply f.injective
  rw [hlin (χ g : k), hlin (ψ g : k)]
  have h := DFunLike.congr_fun (FDRep.Iso.conj_ρ e g) (f 1)
  simpa only [f, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
    of_ρ', Representation.ofLinearCharacter_apply, mul_one, hlin (χ g : k)] using h.symm

/-- **An irreducible representation whose operators commute has a linear character.**  Over an
algebraically closed field, if the operators of an irreducible representation `W` commute
pairwise, Schur's lemma makes each a scalar, so `W` is a line and its character is the linear
character of those scalars. -/
theorem exists_character_eq_of_commute [Field k] [IsAlgClosed k] [Group G] (W : FDRep k G)
    [Simple W] (hcomm : ∀ g h : G, Commute (W.ρ g) (W.ρ h)) :
    ∃ χ : G →* kˣ, W.character = fun g => (χ g : k) := by
  have hW := FDRep.isIrreducible_of_simple W
  have : Nontrivial W := hW.nontrivial
  choose c hc using fun g => hW.exists_forall_apply_eq_smul (W.ρ g) fun h v => by
    rw [← Module.End.mul_apply, (hcomm g h).eq, Module.End.mul_apply]
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hmul (g h : G) : c (g * h) = c g * c h := by
    refine smul_left_injective k hv ?_
    dsimp only
    rw [← hc, map_mul, Module.End.mul_apply, hc h, map_smul, hc g, smul_smul, mul_comm]
  have hone : c 1 = 1 := smul_left_injective k hv (by simp [← hc])
  -- The line through `v` is stable, hence everything: `W` is one-dimensional.
  let line : Subrepresentation W.ρ :=
    ⟨k ∙ v, fun g w hw => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hc, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hline : line = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top line).resolve_left fun h => hv <| by
    have hmem : v ∈ line.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact hmem
  have hfin : Module.finrank k W = 1 :=
    (finrank_eq_one_iff_of_nonzero v hv).mpr (congrArg Subrepresentation.toSubmodule hline)
  let χ : G →* k := { toFun := c, map_one' := hone, map_mul' := hmul }
  refine ⟨χ.toHomUnits, funext fun g => ?_⟩
  have hρ : W.ρ g = c g • LinearMap.id := LinearMap.ext (hc g)
  simp [χ, character, hρ, hfin]

end FDRep
end
end TAF_LiteralSource_0396

section TAF_LiteralSource_0397
/- Original module: TauCeti.RepresentationTheory.CharacterTwist -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Twisting a representation by a linear character

Tensoring a representation `ρ` with a one-dimensional representation does not change its carrier:
the line can be absorbed by `TensorProduct.lid`, leaving the same module with the action rescaled
by the character.  This file records that rescaled action directly as
`Representation.charTwist χ ρ`, `g ↦ χ g • ρ g` for a linear character `χ : G →* kˣ`, and proves
that it is the tensor product with `Representation.ofLinearCharacter χ`
(`Representation.tprodEquivCharTwist`).

Working with the twist rather than with the tensor product is what makes its basic theory
transparent.  Because every value of `χ` is a *unit*, a submodule is stable under `χ g • ρ g`
exactly when it is stable under `ρ g`, so the twist has literally the same subrepresentations
(`Representation.subrepresentationCharTwistOrderIso`) and is irreducible exactly when `ρ` is
(`Representation.isIrreducible_charTwist_iff`).  Neither statement is visible through the tensor
product without transporting along `TensorProduct.lid` first.

The twists form an action of the character group: twisting by `1` changes nothing and twisting
twice multiplies the characters.  The main consumer is the determinant twist of the general linear
group, where `χ = det ^ m` turns a polynomial representation into a rational one.

This is a module of its own rather than a section of
`TauCeti/RepresentationTheory/LinearCharacter/Basic.lean`, which it extends: the twist needs the
tensor product and the subrepresentation lattice. Consumers of the bare one-dimensional
representation need neither.

## Main definitions

* `Representation.charTwist`: the representation `g ↦ χ g • ρ g`.
* `Representation.subrepresentationCharTwistOrderIso`: the twist has the same lattice of
  subrepresentations as `ρ`, by the identity on carriers.
* `Representation.tprodEquivCharTwist` and
  `Representation.tprodOfLinearCharacterEquivCharTwist`: the tensor product of `ρ` with
  `ofLinearCharacter χ` **is** the twist, on either side, along `TensorProduct.lid` and
  `TensorProduct.rid`.

## Main results

* `Representation.charTwist_one` and `Representation.charTwist_charTwist`: twisting is an action of
  the character group `G →* kˣ`.
* `Representation.charTwist_trivial`: twisting the trivial representation of the line gives the
  one-dimensional representation of the character.
* `Representation.lid_ofLinearCharacter_tprod_apply` and
  `Representation.rid_tprod_ofLinearCharacter_apply`: `TensorProduct.lid` and `TensorProduct.rid`
  carry the action of `(ofLinearCharacter χ) ⊗ ρ` and of `ρ ⊗ (ofLinearCharacter χ)` to the action
  of `ρ` rescaled by `χ`.
* `Representation.isIrreducible_charTwist_iff`: **the twist of an irreducible representation is
  irreducible**, and conversely.
* `Representation.char_charTwist`: the trace character of the twist is `χ` times the character
  of `ρ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones.
-/

public section

open scoped TensorProduct

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}

section CommSemiring

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- **The twist of a representation by a linear character**: the same carrier, with `ρ g` rescaled
by the unit `χ g`.  It is the tensor product with the one-dimensional representation of `χ`
(`Representation.tprodEquivCharTwist`), with the line absorbed. -/
def charTwist (χ : G →* kˣ) (ρ : Representation k G V) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      smul_smul, mul_comm]

@[simp]
theorem charTwist_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) :
    charTwist χ ρ g = (χ g : k) • ρ g :=
  (rfl)

theorem charTwist_apply_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) (v : V) :
    charTwist χ ρ g v = (χ g : k) • ρ g v :=
  (rfl)

/-- Twisting by the trivial character changes nothing. -/
@[simp]
theorem charTwist_one (ρ : Representation k G V) : charTwist (1 : G →* kˣ) ρ = ρ :=
  MonoidHom.ext fun _ => by simp

/-- Twisting twice multiplies the characters: the twists are an action of `G →* kˣ`. -/
theorem charTwist_charTwist (χ ψ : G →* kˣ) (ρ : Representation k G V) :
    charTwist χ (charTwist ψ ρ) = charTwist (χ * ψ) ρ :=
  MonoidHom.ext fun g => LinearMap.ext fun v => by
    simp [mul_smul]

/-- Twisting the trivial representation of the coefficient line by `χ` gives the one-dimensional
representation of `χ`.  So the one-dimensional representations are the twists of the trivial one,
and `Representation.charTwist` extends `Representation.ofLinearCharacter`. -/
@[simp]
theorem charTwist_trivial (χ : G →* kˣ) :
    charTwist χ (trivial k G k) = ofLinearCharacter χ :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by
    simp [ofLinearCharacter_apply, smul_eq_mul]

/-- A submodule stable under `ρ` is stable under any twist of `ρ`. -/
theorem charTwist_apply_mem_of_apply_mem {χ : G →* kˣ} {ρ : Representation k G V}
    {p : Submodule k V} (hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p) (g : G) ⦃v : V⦄ (hv : v ∈ p) :
    charTwist χ ρ g v ∈ p :=
  p.smul_mem _ (hp g hv)

/-- Conversely a submodule stable under a twist of `ρ` is stable under `ρ`, the character values
being units. -/
theorem apply_mem_of_charTwist_apply_mem {χ : G →* kˣ} {ρ : Representation k G V}
    {p : Submodule k V} (hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → charTwist χ ρ g v ∈ p) (g : G) ⦃v : V⦄
    (hv : v ∈ p) : ρ g v ∈ p := by
  have h := p.smul_mem ((χ g)⁻¹ : kˣ) (hp g hv)
  rwa [charTwist_apply_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_smul] at h

variable (χ : G →* kˣ) (ρ : Representation k G V)

/-- **A twist has the same subrepresentations as the representation it twists**, by the identity on
carriers: the character values are units, so they scale a stable submodule into itself and back. -/
def subrepresentationCharTwistOrderIso : Subrepresentation (charTwist χ ρ) ≃o Subrepresentation ρ
    where
  toFun p := ⟨p.toSubmodule, apply_mem_of_charTwist_apply_mem p.apply_mem_toSubmodule⟩
  invFun p := ⟨p.toSubmodule, charTwist_apply_mem_of_apply_mem p.apply_mem_toSubmodule⟩
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem toSubmodule_subrepresentationCharTwistOrderIso (p : Subrepresentation (charTwist χ ρ)) :
    (subrepresentationCharTwistOrderIso χ ρ p).toSubmodule = p.toSubmodule :=
  (rfl)

@[simp]
theorem toSubmodule_subrepresentationCharTwistOrderIso_symm (p : Subrepresentation ρ) :
    ((subrepresentationCharTwistOrderIso χ ρ).symm p).toSubmodule = p.toSubmodule :=
  (rfl)

/-- **`TensorProduct.lid` carries the action of `(ofLinearCharacter χ) ⊗ ρ` to the action of `ρ`
rescaled by `χ`.**  This is the equivariance datum behind
`Representation.tprodEquivCharTwist`, recorded on elements so that it can be used without
unfolding that equivalence. -/
theorem lid_ofLinearCharacter_tprod_apply (g : G) (x : k ⊗[k] V) :
    _root_.TensorProduct.lid k V (((ofLinearCharacter χ).tprod ρ) g x)
      = (χ g : k) • ρ g (_root_.TensorProduct.lid k V x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | tmul c v =>
    simp only [tprod_apply, _root_.TensorProduct.map_tmul, ofLinearCharacter_apply,
      _root_.TensorProduct.lid_tmul, map_smul, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- **The tensor product with the one-dimensional representation of a character is the twist by
that character**, along `TensorProduct.lid`.  This is the identification that lets the twist be
read as the usual tensor product `χ ⊗ ρ`, and conversely lets a tensor product with a line be
computed on the original carrier. -/
noncomputable def tprodEquivCharTwist :
    ((ofLinearCharacter χ).tprod ρ).Equiv (charTwist χ ρ) :=
  .mk (_root_.TensorProduct.lid k V) fun g =>
    LinearMap.ext fun x => lid_ofLinearCharacter_tprod_apply χ ρ g x

@[simp]
theorem toLinearMap_tprodEquivCharTwist :
    (tprodEquivCharTwist χ ρ).toLinearMap = (_root_.TensorProduct.lid k V).toLinearMap :=
  (rfl)

@[simp]
theorem tprodEquivCharTwist_tmul (x : k) (v : V) :
    tprodEquivCharTwist χ ρ (x ⊗ₜ[k] v) = x • v :=
  (rfl)

/-- The inverse of `Representation.tprodEquivCharTwist` puts the line `1` in front. -/
@[simp]
theorem tprodEquivCharTwist_symm_apply (v : V) :
    (tprodEquivCharTwist χ ρ).symm v = (1 : k) ⊗ₜ[k] v :=
  (rfl)

/-- **`TensorProduct.rid` carries the action of `ρ ⊗ (ofLinearCharacter χ)` to the action of `ρ`
rescaled by `χ`.**  This is the mirror of `Representation.lid_ofLinearCharacter_tprod_apply` for a
line on the right, and the equivariance datum behind
`Representation.tprodOfLinearCharacterEquivCharTwist`. -/
theorem rid_tprod_ofLinearCharacter_apply (g : G) (x : V ⊗[k] k) :
    _root_.TensorProduct.rid k V ((ρ.tprod (ofLinearCharacter χ)) g x)
      = (χ g : k) • ρ g (_root_.TensorProduct.rid k V x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | tmul v c =>
    simp only [tprod_apply, _root_.TensorProduct.map_tmul, ofLinearCharacter_apply,
      _root_.TensorProduct.rid_tmul, map_smul, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- **The tensor product with the one-dimensional representation of a character on the right is
also the twist by that character**, along `TensorProduct.rid`: the mirror of
`Representation.tprodEquivCharTwist`, so that a consumer holding `ρ ⊗ χ` reaches the twist theory
without flipping the factors first. -/
noncomputable def tprodOfLinearCharacterEquivCharTwist :
    (ρ.tprod (ofLinearCharacter χ)).Equiv (charTwist χ ρ) :=
  .mk (_root_.TensorProduct.rid k V) fun g =>
    LinearMap.ext fun x => rid_tprod_ofLinearCharacter_apply χ ρ g x

@[simp]
theorem toLinearMap_tprodOfLinearCharacterEquivCharTwist :
    (tprodOfLinearCharacterEquivCharTwist χ ρ).toLinearMap
      = (_root_.TensorProduct.rid k V).toLinearMap :=
  (rfl)

@[simp]
theorem tprodOfLinearCharacterEquivCharTwist_tmul (v : V) (x : k) :
    tprodOfLinearCharacterEquivCharTwist χ ρ (v ⊗ₜ[k] x) = x • v :=
  (rfl)

/-- The inverse of `Representation.tprodOfLinearCharacterEquivCharTwist` tensors with `1` on the
right. -/
@[simp]
theorem tprodOfLinearCharacterEquivCharTwist_symm_apply (v : V) :
    (tprodOfLinearCharacterEquivCharTwist χ ρ).symm v = v ⊗ₜ[k] (1 : k) :=
  (rfl)

end CommSemiring

section Field

variable [Field k] [Monoid G] [AddCommGroup V] [Module k V] (χ : G →* kˣ)
  (ρ : Representation k G V)

/-- **A twist of an irreducible representation is irreducible**, and only a twist of an irreducible
one is: twisting by a character does not change the lattice of subrepresentations. -/
@[simp]
theorem isIrreducible_charTwist_iff : (charTwist χ ρ).IsIrreducible ↔ ρ.IsIrreducible :=
  OrderIso.isSimpleOrder_iff (subrepresentationCharTwistOrderIso χ ρ)

/-- The instance form of `Representation.isIrreducible_charTwist_iff`: a twist of an irreducible
representation is irreducible. -/
instance isIrreducible_charTwist [ρ.IsIrreducible] : (charTwist χ ρ).IsIrreducible :=
  (isIrreducible_charTwist_iff χ ρ).mpr ‹_›

/-- **The character of a twist is the pointwise product** of the twisting character with the
character of the representation. -/
@[simp]
theorem char_charTwist (g : G) :
    (charTwist χ ρ).character g = (χ g : k) * ρ.character g := by
  rw [character, character, charTwist_apply, map_smul, smul_eq_mul]

end Field

end Representation
end
end TAF_LiteralSource_0397

section TAF_LiteralSource_0398
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Determinant -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Determinant-power representations of the general linear group

This file packages the determinant and its integral powers as one-dimensional representations of
the general linear group. These are the rational characters used to form determinant twists of
polynomial representations.

## Main definitions

* `TauCeti.detPowerRep` is the representation on the scalar module with action by `det(g)^m`.
* `TauCeti.detRep` is the determinant representation, the case `m = 1`.
* `TauCeti.tprodDetPowerSLEquiv`: the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of
  `ρ`, along `TensorProduct.lid`.

## Main results

* `TauCeti.detPowerRep_def` is its defining equation, as the one-dimensional representation of the
  linear character `det ^ m`.
* `TauCeti.detPowerRep_comp_toGL`: every determinant power restricts to the trivial
  representation of the special linear subgroup, which is why **the determinant twist is invisible
  to `SL n k`** (`TauCeti.tprodDetPowerSLEquiv`).
-/

public section

open Matrix
open scoped TensorProduct

universe u v

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The one-dimensional representation of `GL n k` on which `g` acts by `det(g)^m`. This is the
representation carrying the linear character `det ^ m`. -/
def detPowerRep (m : ℤ) : Representation k (GL (Fin n) k) k :=
  Representation.ofLinearCharacter ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m)

/-- The defining equation of `TauCeti.detPowerRep`: it is the one-dimensional representation of
the linear character `det ^ m`.  The body is not exposed, so this is how a downstream module
applies the general theory of `Representation.ofLinearCharacter` and of its twists to it. -/
theorem detPowerRep_def (m : ℤ) :
    detPowerRep k n m =
      Representation.ofLinearCharacter ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m) :=
  (rfl)

/-- The determinant representation of `GL n k`. -/
abbrev detRep : Representation k (GL (Fin n) k) k := detPowerRep k n 1

/-- The determinant-power action is scalar multiplication by the indicated determinant power. -/
@[simp]
theorem detPowerRep_apply (m : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n m g x = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) * x :=
  Representation.ofLinearCharacter_apply _ g x

/-- The zero determinant power is the trivial representation. -/
@[simp]
theorem detPowerRep_zero : detPowerRep k n 0 = 1 := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  simp

/-- Adding exponents composes the corresponding determinant actions. -/
theorem detPowerRep_add_apply (m l : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n (m + l) g x = detPowerRep k n m g (detPowerRep k n l g x) := by
  simp only [detPowerRep_apply, _root_.zpow_add, Units.val_mul]
  rw [mul_assoc]

/-- Every determinant-power representation restricts to the trivial representation of `SL n k`. -/
@[simp]
theorem detPowerRep_comp_toGL (m : ℤ) : (detPowerRep k n m).comp Matrix.SpecialLinearGroup.toGL =
      Representation.trivial k (Matrix.SpecialLinearGroup (Fin n) k) k := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  -- Unfolding the two composed monoid homomorphisms exposes the scalar-action formula.
  change detPowerRep k n m (Matrix.SpecialLinearGroup.toGL g) x = x
  rw [detPowerRep_apply]
  simp

/-! ## The determinant twist on the special linear group -/

/-- **`TensorProduct.lid` carries the restricted action of `det^m ⊗ ρ` to the restricted action of
`ρ`**: the determinant is `1` on `SL n k`, so the twisting factor is `1`.  This is the
equivariance datum behind `TauCeti.tprodDetPowerSLEquiv`, recorded on elements so that it can be
used without unfolding that equivalence. -/
theorem lid_detPowerRep_tprod_toGL_apply {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) (g : Matrix.SpecialLinearGroup (Fin n) k)
    (x : k ⊗[k] V) :
    _root_.TensorProduct.lid k V
        (((detPowerRep k n m).tprod ρ) (Matrix.SpecialLinearGroup.toGL g) x)
      = ρ (Matrix.SpecialLinearGroup.toGL g) (_root_.TensorProduct.lid k V x) := by
  have hdet : (((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m)
      (Matrix.SpecialLinearGroup.toGL g) : kˣ) = 1 := by
    simp
  rw [detPowerRep_def, Representation.lid_ofLinearCharacter_tprod_apply, hdet, Units.val_one,
    one_smul]

/-- **The determinant twist is invisible to the special linear group**: for every representation
`ρ` of `GL n k`, the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of `ρ`, along
`TensorProduct.lid`.  This is the restricted counterpart of
`Representation.tprodEquivCharTwist`, where the twisting character `det ^ m` has become `1`. -/
noncomputable def tprodDetPowerSLEquiv {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) :
    Representation.Equiv
      (((detPowerRep k n m).tprod ρ).comp Matrix.SpecialLinearGroup.toGL)
      (ρ.comp Matrix.SpecialLinearGroup.toGL) :=
  .mk (_root_.TensorProduct.lid k V) fun g =>
    LinearMap.ext fun x => lid_detPowerRep_tprod_toGL_apply k n m ρ g x

@[simp]
theorem toLinearMap_tprodDetPowerSLEquiv {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) :
    (tprodDetPowerSLEquiv k n m ρ).toLinearMap =
      (_root_.TensorProduct.lid k V).toLinearMap :=
  (rfl)

@[simp]
theorem tprodDetPowerSLEquiv_tmul {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) (x : k) (v : V) :
    tprodDetPowerSLEquiv k n m ρ (x ⊗ₜ[k] v) = x • v :=
  (rfl)

/-- The determinant-power representation as a finite-dimensional representation. -/
noncomputable abbrev detPowerFDRep (m : ℤ) : FDRep k (GL (Fin n) k) :=
  FDRep.ofLinearCharacter (Matrix.GeneralLinearGroup.det ^ m)

/-- The determinant representation as a finite-dimensional representation. -/
noncomputable abbrev detFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (detRep k n)

end CommRing

section Field

variable [Field k]

/-- Negating the exponent makes the determinant scalar the inverse of the original power. -/
theorem detPowerRep_neg_apply (m : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n (-m) g x = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k)⁻¹ * x := by
  simp only [detPowerRep_apply, _root_.zpow_neg, Units.val_inv_eq_inv_val]

/-- The character of the determinant-power representation is the corresponding determinant power. -/
@[simp]
theorem char_detPowerRep (m : ℤ) (g : GL (Fin n) k) :
    (detPowerRep k n m).character g = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) := by
  exact Representation.char_ofLinearCharacter _ g

/-- The bundled determinant-power character is the corresponding determinant power.

This is deliberately not a `simp` lemma: `TauCeti.detPowerFDRep` is a reducible abbreviation for
`FDRep.ofLinearCharacter (det ^ m)`, so `FDRep.char_ofLinearCharacter` already reduces
its left-hand side. -/
theorem char_detPowerFDRep (m : ℤ) (g : GL (Fin n) k) :
    (detPowerFDRep k n m).character g = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) :=
  FDRep.char_ofLinearCharacter _ g

/-- The bundled determinant character is the determinant. -/
theorem char_detFDRep (g : GL (Fin n) k) :
    (detFDRep k n).character g = (Matrix.GeneralLinearGroup.det g : k) := by
  -- The determinant representation is the first determinant power, so its character is that of
  -- `FDRep.ofLinearCharacter (det ^ (1 : ℤ))`.
  have h : detFDRep k n = detPowerFDRep k n 1 := (FDRep.ofLinearCharacter_def _).symm
  rw [h, char_detPowerFDRep, zpow_one]

end Field

end TauCeti
end
end TAF_LiteralSource_0398

section TAF_LiteralSource_0399
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Exterior powers of the standard representation

This file specializes exterior powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure wedge.

In the top degree `d = n` the action collapses to a scalar: a matrix acts on `⋀[k]^n (Fin n → k)`
by its determinant, so that exterior power is the determinant representation.

## Main definitions

* `TauCeti.extPowerRep` is the exterior-power representation of `GL n k`.
* `TauCeti.extPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.topExtPowerEquivDet` identifies the top exterior power with the determinant
  representation, and `TauCeti.extPowerFDRepDetIso` is its bundled form.

## Main results

* `TauCeti.char_extPowerRep_diagonal` identifies the character on diagonal matrices with an
  elementary symmetric polynomial.
* `TauCeti.extPowerRep_self_apply` and `TauCeti.char_extPowerRep_self` compute the top-degree
  action and character as the determinant.

Vanishing of `⋀[k]^d (Fin n → k)`, and hence `extPowerRep k n d`, once `n < d` is given by
`exteriorPower.eq_zero_of_finrank_lt` in `TauCeti.LinearAlgebra.ExteriorPower.Basic`. The
degree-zero and degree-one identifications of `extPowerRep k n` are the generic
`(stdRep k n).exteriorPowerZeroEquiv` and `(stdRep k n).exteriorPowerOneEquiv`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open CategoryTheory
open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th exterior power of the standard representation of `GL n k`. -/
noncomputable abbrev extPowerRep :
    Representation k (GL (Fin n) k) (⋀[k]^d (Fin n → k)) :=
  (stdRep k n).exteriorPower d

/-- The exterior power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev extPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (extPowerRep k n d)

/-- In the top degree a matrix acts on the exterior power by multiplication by its determinant.

This is deliberately not a `simp` lemma: `Representation.exteriorPower_apply` and `stdRep_apply`
already rewrite the left-hand side to `exteriorPower.map n (Matrix.mulVecLin ↑g)`, so it is not in
`simp` normal form and the rewrite could never fire. The `simp`-normal statement is
`Module.Basis.map_exteriorPower_top_eq_det_smul`, applied here to `Pi.basisFun k (Fin n)`. -/
theorem extPowerRep_self_apply (g : GL (Fin n) k) :
    extPowerRep k n n g = Matrix.det (g : Matrix (Fin n) (Fin n) k) • LinearMap.id := by
  rw [Representation.exteriorPower_apply, stdRep_apply, ← Matrix.toLin'_apply',
    (Pi.basisFun k (Fin n)).map_exteriorPower_top_eq_det_smul, LinearMap.det_toLin']

/-- **The top exterior power of the standard representation is the determinant representation.**
The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
noncomputable def topExtPowerEquivDet : (extPowerRep k n n).Equiv (detRep k n) :=
  .mk ((Pi.basisFun k (Fin n)).exteriorPowerTopEquiv) fun g ↦ by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      extPowerRep_self_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul,
      smul_eq_mul, detPowerRep_apply, zpow_one, Matrix.GeneralLinearGroup.val_det_apply]

/-- The underlying linear equivalence of `TauCeti.topExtPowerEquivDet` is the top-degree
identification of the exterior power with the scalars. -/
@[simp]
theorem topExtPowerEquivDet_toLinearEquiv :
    (topExtPowerEquivDet k n).toLinearEquiv = (Pi.basisFun k (Fin n)).exteriorPowerTopEquiv :=
  (rfl)

/-- The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
@[simp]
theorem topExtPowerEquivDet_apply_ιMulti (v : Fin n → (Fin n → k)) :
    topExtPowerEquivDet k n (exteriorPower.ιMulti k n v) = (Matrix.of v).det := by
  rw [← Representation.Equiv.coe_toIntertwiningMap,
    ← Representation.Equiv.toLinearEquiv_apply, topExtPowerEquivDet_toLinearEquiv,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, Pi.basisFun_det_apply]

/-- The identification of the top exterior power with the determinant representation, bundled as
an isomorphism in `FDRep`. -/
noncomputable def extPowerFDRepDetIso : extPowerFDRep k n n ≅ detFDRep k n :=
  Action.mkIso (topExtPowerEquivDet k n).toLinearEquiv.toFGModuleCatIso fun g ↦ by
    apply FGModuleCat.hom_ext
    exact (topExtPowerEquivDet k n).isIntertwining' g

/-- The forward map of the bundled identification is the underlying representation
equivalence. -/
@[simp]
theorem extPowerFDRepDetIso_hom_hom : (extPowerFDRepDetIso k n).hom.hom =
      ConcreteCategory.ofHom (topExtPowerEquivDet k n).toLinearMap := by
  rw [extPowerFDRepDetIso]
  rfl

/-- The inverse map of the bundled identification is the inverse representation equivalence. -/
@[simp]
theorem extPowerFDRepDetIso_inv_hom : (extPowerFDRepDetIso k n).inv.hom =
      ConcreteCategory.ofHom (topExtPowerEquivDet k n).symm.toLinearMap := by
  rw [extPowerFDRepDetIso]
  rfl

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th exterior power on a diagonal matrix is the `d`th elementary
symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_extPowerRep_diagonal (t : Fin n → kˣ) : (extPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.esymm (Fin n) k d) := by
  rw [Representation.character, Representation.exteriorPower_apply]
  rw [(Pi.basisFun k (Fin n)).trace_map_exteriorPower_of_apply
    (stdRep k n (diagGL t)) (fun i => (t i : k)) d
    (stdRep_diagGL_apply_basisFun t)]
  simp only [MvPolynomial.esymm, MvPolynomial.eval_sum, MvPolynomial.eval_prod,
    MvPolynomial.eval_X]
  -- Both sides sum the same products over the `d`-element subsets of `Fin n`, indexed by
  -- `Set.powersetCard` on the left and by `Finset.powersetCard` on the right.
  exact (Finset.sum_subtype (Finset.powersetCard d Finset.univ)
    (fun _ => Finset.mem_powersetCard_univ) fun s => ∏ i ∈ s, (t i : k)).symm

/-- The character of the top exterior power of the standard representation is the determinant.

This is deliberately not a `simp` lemma: on a diagonal matrix its left-hand side is also matched by
`TauCeti.char_extPowerRep_diagonal`, whose elementary-symmetric right-hand side is a different
normal form. -/
theorem char_extPowerRep_self (g : GL (Fin n) k) :
    (extPowerRep k n n).character g = Matrix.det (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.char_iso (topExtPowerEquivDet k n), char_detPowerRep k n 1 g, zpow_one,
    Matrix.GeneralLinearGroup.val_det_apply]

end Field

end TauCeti
end
end TAF_LiteralSource_0399

section TAF_LiteralSource_0400
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Multilinear -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `MvPolynomial.eq_of_eval_eq_on_gl`, the Zariski density of the invertible matrices, together with
-- the `GL` notation and the coercion of an element of `GL m k` to a matrix.
-- `Matrix.single`, the matrix units in which the arguments are expanded.

/-!
# A multilinear form on matrices is determined on the diagonal by the invertible matrices

Let `Θ` be a multilinear form in `ι` matrix arguments over a commutative semiring `K`. Its
**diagonal** `Y ↦ Θ (Y, …, Y)` is a polynomial function of the entries of `Y`: expanding each
argument in the matrix units `Matrix.single i j 1` writes it as a sum, over the functions
`a : ι → m × n`, of the constant `Θ (fun i => single (a i).1 (a i).2 1)` times the monomial
`∏ᵢ Y (a i).1 (a i).2`. The matrices need not be square. That is
`MultilinearMap.exists_mvPolynomial_eval_eq_apply_const` below.

Over an *infinite* field the invertible square matrices are Zariski dense, so such a polynomial
function vanishes everywhere as soon as it vanishes on `GL m K`
(`MvPolynomial.eq_of_eval_eq_on_gl`). Hence a multilinear form whose diagonal kills every invertible
matrix has zero diagonal: `MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`.

This is the form in which density is used to pass from the invertible diagonal operators `g^{⊗ι}`
on a tensor power to all of them; the argument is stated here on matrices, where the ambient
polynomial ring `MvPolynomial (m × m) K` and the density statement live.

## Main results

* `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`: the diagonal of a multilinear form on
  (possibly rectangular) matrices is the evaluation of a polynomial in the matrix entries.
* `MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`: over an infinite field, a multilinear form
  on matrices whose diagonal vanishes on the invertible matrices has vanishing diagonal.
-/

public section

open Matrix MvPolynomial

namespace MultilinearMap

universe u v v' w

variable {ι : Type u} {m : Type v} {n : Type v'} {K : Type w} [Finite ι]

section CommSemiring

variable [Finite m] [Finite n] [CommSemiring K]

/-- **The diagonal of a multilinear form on matrices is a polynomial in the matrix entries.**
Expanding each of the `ι` arguments in the matrix units, the value `Θ (Y, …, Y)` is a sum of
constants times monomials `∏ᵢ Y (a i).1 (a i).2` indexed by the functions `a : ι → m × n`. -/
theorem exists_mvPolynomial_eval_eq_apply_const
    (Θ : MultilinearMap K (fun _ : ι => Matrix m n K) K) :
    ∃ P : MvPolynomial (m × n) K, ∀ Y : Matrix m n K,
      MvPolynomial.eval (fun p : m × n => Y p.1 p.2) P = Θ fun _ => Y := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype m
  cases nonempty_fintype n
  refine ⟨∑ a : ι → m × n, C (Θ fun i => single (a i).1 (a i).2 1) * ∏ i, X (a i), fun Y => ?_⟩
  have hY : ∑ p : m × n, Y p.1 p.2 • single p.1 p.2 (1 : K) = Y := by
    simp only [smul_single, smul_eq_mul, mul_one]
    rw [Fintype.sum_prod_type]
    exact (matrix_eq_sum_single Y).symm
  have hexp : (Θ fun _ => Y) =
      ∑ a : ι → m × n, (∏ i, Y (a i).1 (a i).2) * Θ fun i => single (a i).1 (a i).2 1 := by
    have hstep : (Θ fun _ : ι => ∑ p : m × n, Y p.1 p.2 • single p.1 p.2 (1 : K)) =
        ∑ a : ι → m × n, (∏ i, Y (a i).1 (a i).2) * Θ fun i => single (a i).1 (a i).2 1 := by
      rw [Θ.map_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Θ.map_smul_univ (fun i => Y (a i).1 (a i).2), smul_eq_mul]
    rwa [hY] at hstep
  rw [hexp]
  simp only [_root_.map_sum, _root_.map_mul, eval_C, _root_.map_prod, eval_X]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end CommSemiring

section Field

variable [Fintype m] [DecidableEq m] [Field K] [Infinite K]

/-- **A multilinear form on matrices whose diagonal vanishes on the invertible matrices has
vanishing diagonal.** The diagonal is a polynomial function of the matrix entries (the square case
of `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`), and over an infinite field the
invertible matrices are Zariski dense. -/
theorem apply_const_eq_zero_of_eq_zero_on_gl (Θ : MultilinearMap K (fun _ : ι => Matrix m m K) K)
    (h : ∀ g : GL m K, (Θ fun _ => (g : Matrix m m K)) = 0) (Y : Matrix m m K) :
    (Θ fun _ => Y) = 0 := by
  obtain ⟨P, hP⟩ := Θ.exists_mvPolynomial_eval_eq_apply_const
  have hzero : P = 0 := MvPolynomial.eq_of_eval_eq_on_gl fun g => by simp [hP, h g]
  rw [← hP Y, hzero, _root_.map_zero]

end Field

end MultilinearMap
end
end TAF_LiteralSource_0400

section TAF_LiteralSource_0401
/- Original module: TauCeti.LinearAlgebra.PiTensorProduct.GeneralLinear -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`, the detection of a subspace by the
-- functionals vanishing on it.
-- `Matrix.toLinAlgEquiv`, the algebra isomorphism between matrices and endomorphisms.
-- `PiTensorProduct.map` and `PiTensorProduct.mapMultilinear`, the diagonal operators.

/-!
# The diagonal operators of the invertible endomorphisms span all of them

A `V`-endomorphism `f` acts on the tensor power `⨂[K] (_ : ι), V` diagonally, by
`f^{⊗ι} = PiTensorProduct.map (fun _ ↦ f)`. These diagonal operators are not closed under addition,
so the span of the ones coming from *invertible* `f` is not visibly all of the span of them all.
Over an infinite field and for a finite-dimensional `V` the two spans nonetheless coincide
(`PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`), because the invertible
endomorphisms are Zariski dense. That is what lets the general linear group replace the whole
endomorphism algebra in Schur-Weyl duality, where the commutant of the symmetric-group action is
the span of the diagonal operators and one wants it to be the image of `K[GL(V)]`.

## The argument

A vector of a vector space lies in a subspace as soon as every functional vanishing on the subspace
kills it (`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`). So fix a functional `φ` on
`End (⨂[K] (_ : ι), V)` vanishing on the span of the invertible diagonal operators. Composing `φ`
with `PiTensorProduct.mapMultilinear`, which is multilinear in the family of endomorphisms, and with
the matrix-to-endomorphism isomorphism attached to a basis, produces a multilinear form `Θ` in `ι`
matrix arguments whose diagonal is `Θ (Y, …, Y) = φ (Y^{⊗ι})`. That diagonal vanishes on the
invertible matrices, hence identically, by
`MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`.

## Main results

* `PiTensorProduct.map_const_mem_span_range_map_const_units`: the diagonal operator of an
  endomorphism is a combination of the diagonal operators of the invertible ones.
* `PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`: consequently the two spans
  agree.
-/

public section

open Matrix

open scoped TensorProduct

namespace PiTensorProduct

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [Finite ι]

/-- **The diagonal operator of an endomorphism is a combination of the diagonal operators of the
invertible ones**, over an infinite field and for a finite-dimensional `V`. -/
theorem map_const_mem_span_range_map_const_units (f : V →ₗ[K] V) :
    map (fun _ : ι => f) ∈ Submodule.span K
      (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) := by
  classical
  cases nonempty_fintype ι
  set S := Submodule.span K
    (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) with _hSdef
  suffices h : ∀ φ : Module.Dual K ((⨂[K] _ : ι, V) →ₗ[K] (⨂[K] _ : ι, V)),
      (∀ y ∈ S, φ y = 0) → φ (map fun _ : ι => f) = 0 by
    exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp fun φ hφ =>
      h φ ((Submodule.mem_dualAnnihilator _).mp hφ)
  intro φ hφ
  set e := Module.finBasis K V with _
  set Θ : MultilinearMap K
      (fun _ : ι => Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) K :=
    (LinearMap.compMultilinearMap φ
      (mapMultilinear K (fun _ : ι => V) fun _ : ι => V)).compLinearMap
        fun _ => (Matrix.toLinAlgEquiv e).toLinearMap with hΘdef
  have hΘ : ∀ X, (Θ fun _ => X) = φ (map fun _ : ι => Matrix.toLinAlgEquiv e X) := fun _ => by
    simp only [hΘdef, MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply,
      mapMultilinear_apply, AlgEquiv.toLinearMap_apply]
  have hgl : ∀ g : GL (Fin (Module.finrank K V)) K,
      (Θ fun _ => (g : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K)) = 0 := by
    intro g
    rw [hΘ]
    obtain ⟨u, hu⟩ := g.isUnit.map (Matrix.toLinAlgEquiv e)
    exact hφ _ (Submodule.subset_span ⟨u, congrArg _ (funext fun _ => hu)⟩)
  have hf := Θ.apply_const_eq_zero_of_eq_zero_on_gl hgl (LinearMap.toMatrixAlgEquiv e f)
  rwa [hΘ, Matrix.toLinAlgEquiv_toMatrixAlgEquiv] at hf

/-- **The diagonal operators of the invertible endomorphisms span the same subspace as all the
diagonal operators**, over an infinite field and for a finite-dimensional `V`. -/
theorem span_range_map_const_units_eq_span_range_map_const :
    Submodule.span K (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) =
      Submodule.span K (Set.range fun f : V →ₗ[K] V => map fun _ : ι => f) :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩; exact map_const_mem_span_range_map_const_units f))

end PiTensorProduct
end
end TAF_LiteralSource_0401

section TAF_LiteralSource_0402
/- Original module: TauCeti.LinearAlgebra.Matrix.KroneckerPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Kronecker powers of matrices

For a matrix `A` with rows indexed by `m`, columns indexed by `n` and a finite type `κ`, the
Kronecker power `Matrix.kroneckerPower κ A` is the matrix with rows indexed by `κ → m` and columns
indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`. It is the matrix of `A` acting in
every factor of the `κ`-indexed tensor power, in the monomial bases.

The Kronecker power is multiplicative and commutes with transposition, so if `Aᵀ * A = 1` then
the Kronecker power satisfies the same identity.

## Main definitions

* `Matrix.kroneckerPower`: the `κ`-indexed Kronecker power of a matrix.

## Main results

* `Matrix.kroneckerPower_mul`, `Matrix.kroneckerPower_one`, `Matrix.transpose_kroneckerPower`:
  the Kronecker power is multiplicative, sends `1` to `1` and commutes with transposition.
* `Matrix.transpose_kroneckerPower_mul_self`: the Kronecker power of a matrix with `Aᵀ * A = 1`
  satisfies the same identity.
-/

public section

namespace Matrix

variable {R : Type*} {l m n : Type*} (κ : Type*)

/-- The **Kronecker power** of a matrix `A : Matrix m n R`: the matrix with rows indexed by
`κ → m` and columns indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`, the matrix of
`A` acting in every factor of the `κ`-indexed tensor power. -/
def kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) : Matrix (κ → m) (κ → n) R :=
  Matrix.of fun v u => ∏ i, A (v i) (u i)

@[simp]
theorem kroneckerPower_apply [CommMonoid R] [Fintype κ] (A : Matrix m n R) (v : κ → m)
    (u : κ → n) :
    A.kroneckerPower κ v u = ∏ i, A (v i) (u i) :=
  (rfl)

variable {κ}

/-- The Kronecker power commutes with transposition. -/
@[simp]
theorem transpose_kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) :
    (A.kroneckerPower κ)ᵀ = Aᵀ.kroneckerPower κ :=
  (rfl)

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPower_one [CommMonoidWithZero R] [DecidableEq n] [Fintype κ] :
    (1 : Matrix n n R).kroneckerPower κ = 1 := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

/-- The Kronecker power is multiplicative: the `(v, u)` entry of `A^{⊗κ} * B^{⊗κ}` expands, by
distributing the product over the sums, into the product of the entries of `A * B`. -/
theorem kroneckerPower_mul [CommSemiring R] [Fintype m] [Fintype κ] [DecidableEq κ]
    (A : Matrix l m R) (B : Matrix m n R) :
    (A * B).kroneckerPower κ = A.kroneckerPower κ * B.kroneckerPower κ := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.mul_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- The Kronecker power of a matrix `A` with `Aᵀ * A = 1` satisfies the same identity. -/
theorem transpose_kroneckerPower_mul_self [CommSemiring R] [Fintype n] [DecidableEq n]
    [Fintype κ] [DecidableEq κ] {A : Matrix n n R} (hA : Aᵀ * A = 1) :
    (A.kroneckerPower κ)ᵀ * A.kroneckerPower κ = 1 := by
  rw [transpose_kroneckerPower, ← kroneckerPower_mul, hA, kroneckerPower_one]

end Matrix
end
end TAF_LiteralSource_0402

section TAF_LiteralSource_0403
/- Original module: TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Permuting tensor factors

This file defines the symmetric-group action on a power of a module by permuting its tensor
factors. Mathlib's `Representation.asAlgebraHom` then extends the action linearly to the group
algebra, which is the action used by Young symmetrizers.

The construction is the first target in Layer 2 of the
[classical-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md)
and the first construction in Layer 8 of the
[Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md).
It reuses `PiTensorProduct.reindex`; the convention is
`σ • (⨂ₜ i, m i) = ⨂ₜ i, m (σ⁻¹ i)`.

## Main definitions

* `PiTensorProduct.reindexRepresentation` is the permutation action for an arbitrary index type
  and module.
* `permTensorAction` specializes it to `(Fin n → R)^{⊗d}`.
* `permTensorActionAlgHom` is its `Representation.asAlgebraHom` extension to `R[S_d]`.
* `TauCeti.tensorPowerBasis` is the monomial basis of `(Rⁿ)^{⊗d}`, on which the action is a
  reindexing.

## Main results

* `TauCeti.finrank_tensorPower` is the dimension count `dim (Rⁿ)^{⊗d} = nᵈ` that the monomial
  basis supplies.
* `Matrix.piTensorProductMap_tensorPowerBasis` and
  `Matrix.toMatrix_piTensorProductMap_tensorPowerBasis`: in the monomial basis, a matrix `A` acting
  in every tensor factor has the Kronecker power `Matrix.kroneckerPower (Fin d) A` as its matrix.
* `PiTensorProduct.map_reindex_range_reindexRepresentation_asAlgebraHom` transports the image of
  a group-algebra element along any equivalence of tensor-factor index types.
-/

public section

open scoped TensorProduct

universe u v w

namespace PiTensorProduct

variable (R : Type u) (M : Type v) (ι : Type w)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The representation of the permutation group of `ι` on the `ι`-indexed tensor power,
acting by reindexing the tensor factors. -/
noncomputable def reindexRepresentation :
    Representation R (Equiv.Perm ι) (⨂[R] _ : ι, M) where
  toFun σ := (reindex R (fun _ : ι => M) σ).toLinearMap
  map_one' := by
    simpa only [Equiv.Perm.one_def, Module.End.one_eq_id,
      LinearEquiv.refl_toLinearMap] using
      congrArg LinearEquiv.toLinearMap
        (reindex_refl (R := R) (s := fun _ : ι => M))
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap]
    simpa only [Equiv.Perm.mul_def] using
      (reindex_reindex (R := R) (s := fun _ : ι => M) τ σ x).symm

/-- The permutation representation acts by `PiTensorProduct.reindex`. -/
@[simp]
theorem reindexRepresentation_apply (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ = (reindex R (fun _ : ι => M) σ).toLinearMap :=
  (rfl)

/-- Permuting factors commutes with applying the same linear map in every tensor factor. -/
theorem commute_reindexRepresentation_map (σ : Equiv.Perm ι) (f : M →ₗ[R] M) :
    Commute (reindexRepresentation R M ι σ) (map fun _ : ι => f) := by
  apply LinearMap.ext
  intro x
  simpa only [Module.End.mul_apply, reindexRepresentation_apply,
    LinearEquiv.coe_toLinearMap] using
    (map_reindex (f := fun _ : ι => f) σ x).symm

/-- Every element of the group algebra commutes with applying the same linear map in every
tensor factor. -/
theorem commute_reindexRepresentation_asAlgebraHom_map
    (a : MonoidAlgebra R (Equiv.Perm ι)) (f : M →ₗ[R] M) :
    Commute ((reindexRepresentation R M ι).asAlgebraHom a) (map fun _ : ι => f) := by
  induction a using MonoidAlgebra.induction_on with
  | of σ =>
    simpa only [Representation.asAlgebraHom_of] using commute_reindexRepresentation_map R M ι σ f
  | add a b ha hb => simpa only [map_add] using ha.add_left hb
  | smul r a ha => simpa only [map_smul] using ha.smul_left r

/-- The group-algebra action on a pure tensor is the corresponding finite linear combination
of reindexed pure tensors. -/
theorem reindexRepresentation_asAlgebraHom_apply_tprod
    (a : MonoidAlgebra R (Equiv.Perm ι)) (m : ι → M) :
    (reindexRepresentation R M ι).asAlgebraHom a (tprod R m) =
      a.coeff.sum fun σ r => r • tprod R (fun i => m (σ.symm i)) := by
  classical
  simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]

/-- Relabeling tensor factors along an equivalence transports the image of a group-algebra
element onto the image of its transport to the permutation group of the new index type. -/
theorem map_reindex_range_reindexRepresentation_asAlgebraHom {κ : Type*} (e : ι ≃ κ)
    (a : MonoidAlgebra R (Equiv.Perm ι)) :
    (LinearMap.range ((reindexRepresentation R M ι).asAlgebraHom a)).map
        (reindex R (fun _ => M) e : (⨂[R] _ : ι, M) →ₗ[R] (⨂[R] _ : κ, M)) =
      LinearMap.range ((reindexRepresentation R M κ).asAlgebraHom
        (MonoidAlgebra.domCongr R R e.permCongrHom a)) := by
  have h :
      (reindex R (fun _ => M) e).toLinearMap ∘ₗ
          (reindexRepresentation R M ι).asAlgebraHom a =
        (reindexRepresentation R M κ).asAlgebraHom
            (MonoidAlgebra.domCongr R R e.permCongrHom a) ∘ₗ
          (reindex R (fun _ => M) e).toLinearMap := by
    induction a using MonoidAlgebra.induction_on with
    | of σ =>
      ext f
      simp [MonoidAlgebra.of_apply, Equiv.permCongrHom_coe, Equiv.permCongr_def,
        ← Equiv.trans_assoc]
    | add a b ha hb => simp [ha, hb, LinearMap.comp_add, LinearMap.add_comp]
    | smul r a ha => simp [ha, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [← LinearMap.range_comp, h]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)

end PiTensorProduct

namespace TauCeti

variable (R : Type u) (n d : ℕ)
variable [CommSemiring R]

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` by permutation of tensor factors. -/
noncomputable def permTensorAction :
    Representation R (Equiv.Perm (Fin d)) (⨂[R] _ : Fin d, Fin n → R) :=
  PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d)

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` is the reindexing representation for the
index type `Fin d`. -/
theorem permTensorAction_def :
    permTensorAction R n d = PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d) :=
  (rfl)

/-- A permutation acts on `(Fin n → R)^{⊗d}` by `PiTensorProduct.reindex`. -/
@[simp]
theorem permTensorAction_apply (σ : Equiv.Perm (Fin d)) :
    permTensorAction R n d σ =
      (PiTensorProduct.reindex R (fun _ : Fin d => Fin n → R) σ).toLinearMap :=
  (rfl)

/-- The group-algebra action of `R[S_d]` on `(Fin n → R)^{⊗d}` induced by factor
permutations. -/
noncomputable def permTensorActionAlgHom :
    MonoidAlgebra R (Equiv.Perm (Fin d)) →ₐ[R]
      Module.End R (⨂[R] _ : Fin d, Fin n → R) :=
  (permTensorAction R n d).asAlgebraHom

/-- The group-algebra action of `R[S_d]` is the linear extension of `permTensorAction`. -/
theorem permTensorActionAlgHom_def :
    permTensorActionAlgHom R n d = (permTensorAction R n d).asAlgebraHom :=
  (rfl)

/-- A single permutation, viewed in the group algebra, acts by `permTensorAction`. -/
theorem permTensorActionAlgHom_of (σ : Equiv.Perm (Fin d)) :
    permTensorActionAlgHom R n d (MonoidAlgebra.of R (Equiv.Perm (Fin d)) σ) =
      permTensorAction R n d σ := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_of]

/-- The group-algebra action of `a ∈ R[S_d]` is the coefficient-weighted sum of the permutation
actions. -/
theorem permTensorActionAlgHom_eq_sum (a : MonoidAlgebra R (Equiv.Perm (Fin d))) :
    permTensorActionAlgHom R n d a = ∑ σ, a.coeff σ • permTensorAction R n d σ := by
  simp [permTensorActionAlgHom_def, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype]

/-- The group-algebra action on a pure tensor of `(Fin n → R)^{⊗d}` is the corresponding finite
linear combination of reindexed pure tensors. -/
@[simp]
theorem permTensorActionAlgHom_apply_tprod (a : MonoidAlgebra R (Equiv.Perm (Fin d)))
    (m : Fin d → (Fin n → R)) :
    permTensorActionAlgHom R n d a (PiTensorProduct.tprod R m) =
      a.coeff.sum fun σ r => r • PiTensorProduct.tprod R fun i => m (σ.symm i) := by
  rw [permTensorActionAlgHom_def, permTensorAction_def]
  exact PiTensorProduct.reindexRepresentation_asAlgebraHom_apply_tprod R (Fin n → R) (Fin d) a m

/-- Relabeling the tensor factors along `finCongr h`, for `h : m = d`, transports the image of
`a ∈ R[S_m]` onto the image of its transport to `R[S_d]`. -/
theorem map_reindex_range_permTensorAction_asAlgebraHom {m : ℕ} (h : m = d)
    (a : MonoidAlgebra R (Equiv.Perm (Fin m))) :
    (LinearMap.range ((permTensorAction R n m).asAlgebraHom a)).map
        (PiTensorProduct.reindex R (fun _ => Fin n → R) (finCongr h) :
          (⨂[R] _ : Fin m, Fin n → R) →ₗ[R] (⨂[R] _ : Fin d, Fin n → R)) =
      LinearMap.range ((permTensorAction R n d).asAlgebraHom
        (MonoidAlgebra.domCongr R R (finCongr h).permCongrHom a)) := by
  simpa only [permTensorAction_def] using
    PiTensorProduct.map_reindex_range_reindexRepresentation_asAlgebraHom R (Fin n → R) (Fin m)
      (finCongr h) a

/-- The monomial basis of `(Rⁿ)^{⊗d}`: the basis vector at `f : Fin d → Fin n` is the pure tensor
whose `i`-th factor is the `f i`-th standard basis vector of `Rⁿ`. -/
noncomputable def tensorPowerBasis :
    Module.Basis (Fin d → Fin n) R (⨂[R] _ : Fin d, Fin n → R) :=
  Basis.piTensorProduct fun _ => Pi.basisFun R (Fin n)

/-- The monomial basis is the tensor product of the standard bases.  The definition is not
exposed, so this is its defining equation, used to compare it with the `Basis.piTensorProduct`
spelling of the weight theory. -/
theorem tensorPowerBasis_def :
    tensorPowerBasis R n d = Basis.piTensorProduct fun _ : Fin d => Pi.basisFun R (Fin n) :=
  (rfl)

@[simp]
theorem tensorPowerBasis_apply (f : Fin d → Fin n) :
    tensorPowerBasis R n d f = PiTensorProduct.tprod R fun i => Pi.single (f i) (1 : R) := by
  classical
  rw [tensorPowerBasis, Basis.piTensorProduct_apply]
  simp

/-- **The dimension of `(Rⁿ)^{⊗d}` is `nᵈ`**, read off the monomial basis
`TauCeti.tensorPowerBasis`, whose index type is `Fin d → Fin n`. -/
theorem finrank_tensorPower [StrongRankCondition R] :
    Module.finrank R (⨂[R] _ : Fin d, Fin n → R) = n ^ d := by
  rw [Module.finrank_eq_card_basis (tensorPowerBasis R n d), Fintype.card_fun]
  simp

/-- **A matrix acting diagonally on the monomial basis of `(Rⁿ)^{⊗d}`.** Applying `A` in every
tensor factor sends the basis tensor `e_u` to `∑ v, (∏ i, A (v i) (u i)) • e_v`, so its matrix in
the monomial basis is the Kronecker power of `A`. -/
theorem _root_.Matrix.piTensorProductMap_tensorPowerBasis {R : Type u} [CommSemiring R] {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (u : Fin d → Fin n) :
    PiTensorProduct.map (fun _ : Fin d => A.mulVecLin) (tensorPowerBasis R n d u) =
      ∑ v, A.kroneckerPower (Fin d) v u • tensorPowerBasis R n d v := by
  have hcol : ∀ i, A.mulVecLin (Pi.single (u i) (1 : R)) =
      ∑ c, A c (u i) • Pi.single c (1 : R) := fun i => by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, ← (Pi.basisFun R (Fin n)).sum_repr
      (A.col (u i))]
    simp [Matrix.col_apply]
  simp only [tensorPowerBasis_apply, PiTensorProduct.map_tprod, hcol,
    MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
  simp

/-- **The matrix of `A^{⊗d}` in the monomial basis is the Kronecker power of `A`.** The matrix of
`A` acting in every tensor factor of `(Rⁿ)^{⊗d}`, in the basis `TauCeti.tensorPowerBasis`, is
`Matrix.kroneckerPower (Fin d) A`. -/
theorem _root_.Matrix.toMatrix_piTensorProductMap_tensorPowerBasis {R : Type u} [CommSemiring R]
    {n d : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.toMatrix (tensorPowerBasis R n d) (tensorPowerBasis R n d)
        (PiTensorProduct.map fun _ : Fin d => A.mulVecLin) =
      A.kroneckerPower (Fin d) := by
  ext v u
  rw [LinearMap.toMatrix_apply, A.piTensorProductMap_tensorPowerBasis u, map_sum]
  simp [Finsupp.single_apply, -tensorPowerBasis_apply]

-- These two derived normal forms remain explicit rewrite lemmas: `simpNF` detects each as already
-- provable from the underlying tensor-action rules, so adding them to the simp set is redundant.
/-- A permutation acts on the monomial basis of `(Rⁿ)^{⊗d}` by precomposing the index function
with its inverse. -/
theorem permTensorAction_tensorPowerBasis (σ : Equiv.Perm (Fin d)) (f : Fin d → Fin n) :
    permTensorAction R n d σ (tensorPowerBasis R n d f) =
      tensorPowerBasis R n d fun i => f (σ.symm i) := by
  simp

/-- A group-algebra basis element acts on a monomial basis vector by precomposition and
scaling. -/
theorem permTensorActionAlgHom_single_tensorPowerBasis (ρ : Equiv.Perm (Fin d)) (r : R)
    (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d (MonoidAlgebra.single ρ r) (tensorPowerBasis R n d f) =
      r • tensorPowerBasis R n d fun i => f (ρ.symm i) := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_single, LinearMap.smul_apply,
    permTensorAction_tensorPowerBasis]

/-- The group-algebra action on a monomial basis vector is the coefficient-weighted sum of the
precomposed monomial basis vectors. -/
theorem permTensorActionAlgHom_apply_tensorPowerBasis
    (a : MonoidAlgebra R (Equiv.Perm (Fin d))) (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d a (tensorPowerBasis R n d f) =
      ∑ σ ∈ a.coeff.support,
        a.coeff σ • tensorPowerBasis R n d fun i => f (σ.symm i) := by
  rw [tensorPowerBasis_apply, permTensorActionAlgHom_apply_tprod, Finsupp.sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [tensorPowerBasis_apply]

end TauCeti
end
end TAF_LiteralSource_0403

section TAF_LiteralSource_0404
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.TensorPower -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor powers of the standard representation

This file specializes the diagonal tensor-power construction to the standard representation of
the general linear group. It supplies the tensor powers that underpin the Weyl construction for
polynomial representations, together with the description of their monoid-algebra image over an
infinite field.

## Main results

* `TauCeti.tensorPowerRep` is the `d`-fold tensor power of `stdRep`.
* `TauCeti.tensorPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.commute_permTensorAction_tensorPowerRep` proves that the general-linear and
  symmetric-group actions commute, and `TauCeti.commute_permTensorActionAlgHom_tensorPowerRep`
  extends that to the whole group algebra `k[S_d]`.
* `TauCeti.permTensorPowerRep` combines the two commuting actions into one representation of
  `S_d × GL n k`, and `TauCeti.range_asAlgebraHom_permTensorAction_le_comap` says that the image of
  any element of `k[S_d]`, such as a Young symmetrizer, is a `GL n k`-subrepresentation.
* `TauCeti.trace_permTensorAction_conj_mul_tensorPowerRep`: for any `g ∈ GL n k`, the trace of a
  permutation of the tensor factors composed with `g^{⊗d}` is a class function of the permutation.
* `TauCeti.tensorPowerPermIntertwiningMap` packages `g^{⊗d}` as an intertwining map of the
  symmetric-group action, and `TauCeti.tensorPowerIntertwiningRep` is the resulting action of
  `GL n k` on the `S_d`-intertwining maps into the tensor power, by composition.
* `TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const` identifies the
  image of `k[GLₙ]` with the span of all diagonal tensor operators over an infinite field.
-/

public section

open Matrix
open scoped TensorProduct

open PiTensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The diagonal action of `GL n k` on the `d`-fold tensor power of its standard representation. -/
noncomputable abbrev tensorPowerRep :
    Representation k (GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (stdRep k n).tensorPower d

/-- The tensor power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev tensorPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (tensorPowerRep k n d)

/-- The actions of `GL n k` and the symmetric group on the tensor power commute.

This is the commuting-actions half of Schur--Weyl duality; it makes no double-centralizer claim. -/
theorem commute_permTensorAction_tensorPowerRep (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    Commute (permTensorAction k n d σ) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_map k (Fin n → k) (Fin d) σ (stdRep k n g)

variable {k n d} in
/-- **The trace of a permutation of the tensor factors composed with `g^{⊗d}` is a class function
of the permutation**, because the two actions commute. -/
theorem trace_permTensorAction_conj_mul_tensorPowerRep (σ τ : Equiv.Perm (Fin d))
    (g : GL (Fin n) k) :
    LinearMap.trace k _ (permTensorAction k n d (τ * σ * τ⁻¹) * tensorPowerRep k n d g) =
      LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g) := by
  set P := permTensorAction k n d
  set G := tensorPowerRep k n d g
  have hc : P τ⁻¹ * G = G * P τ⁻¹ := (commute_permTensorAction_tensorPowerRep k n d τ⁻¹ g).eq
  have hinv : P τ⁻¹ * P τ = 1 := by rw [← map_mul P, inv_mul_cancel, map_one]
  calc LinearMap.trace k _ (P (τ * σ * τ⁻¹) * G)
      _ = LinearMap.trace k _ (P τ * (P σ * G * P τ⁻¹)) := by
        rw [map_mul P, map_mul P, mul_assoc, hc]
        simp only [mul_assoc]
      _ = LinearMap.trace k _ (P σ * G * (P τ⁻¹ * P τ)) := by
        rw [LinearMap.trace_mul_comm, mul_assoc]
      _ = LinearMap.trace k _ (P σ * G) := by rw [hinv, mul_one]

/-- The whole group algebra `k[S_d]` commutes with the general-linear action on the tensor power,
so a Young symmetrizer cuts out a `GL n k`-subrepresentation. -/
theorem commute_permTensorActionAlgHom_tensorPowerRep
    (a : MonoidAlgebra k (Equiv.Perm (Fin d))) (g : GL (Fin n) k) :
    Commute (permTensorActionAlgHom k n d a) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorActionAlgHom_def,
    permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_asAlgebraHom_map k (Fin n → k) (Fin d) a
    (stdRep k n g)

/-- **The image of an element of `k[S_d]` in `(kⁿ)^{⊗d}` is stable under `GL n k`**, because the
two actions commute.  In particular a Young symmetrizer cuts out a subrepresentation. -/
theorem range_asAlgebraHom_permTensorAction_le_comap (a : MonoidAlgebra k (Equiv.Perm (Fin d)))
    (g : GL (Fin n) k) :
    LinearMap.range ((permTensorAction k n d).asAlgebraHom a) ≤
      (LinearMap.range ((permTensorAction k n d).asAlgebraHom a)).comap
        (tensorPowerRep k n d g) := by
  rintro _ ⟨x, rfl⟩
  have h := commute_permTensorActionAlgHom_tensorPowerRep k n d a g
  rw [permTensorActionAlgHom_def] at h
  exact ⟨tensorPowerRep k n d g x, LinearMap.congr_fun h.eq x⟩

/-- **The joint action of `S_d × GL n k` on `(kⁿ)^{⊗d}`**: a pair `(σ, g)` acts by permuting the
tensor factors by `σ` after applying `g` in every factor.  It is a representation of the product
group because the two actions commute. -/
noncomputable def permTensorPowerRep :
    Representation k (Equiv.Perm (Fin d) × GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (permTensorAction k n d).noncommCoprod (tensorPowerRep k n d)
    (commute_permTensorAction_tensorPowerRep k n d)

/-- The pair `(σ, g)` acts on `(kⁿ)^{⊗d}` as `σ ∘ g^{⊗d}`. -/
@[simp]
theorem permTensorPowerRep_apply (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    permTensorPowerRep k n d (σ, g) = permTensorAction k n d σ * tensorPowerRep k n d g :=
  (rfl)

/-- The operator `g^{⊗d}` on `(kⁿ)^{⊗d}` as an intertwining map of the symmetric-group action:
the diagonal action of `GL n k` commutes with permuting the tensor factors. -/
noncomputable def tensorPowerPermIntertwiningMap (g : GL (Fin n) k) :
    Representation.IntertwiningMap (permTensorAction k n d) (permTensorAction k n d) where
  toLinearMap := tensorPowerRep k n d g
  isIntertwining' σ := (commute_permTensorAction_tensorPowerRep k n d σ g).eq.symm

@[simp]
theorem tensorPowerPermIntertwiningMap_apply (g : GL (Fin n) k) (x : ⨂[k]^d (Fin n → k)) :
    tensorPowerPermIntertwiningMap k n d g x = tensorPowerRep k n d g x :=
  (rfl)

variable {k n d} in
/-- The representation of `GL n k` on the `S_d`-intertwining maps from `ρ` into `(kⁿ)^{⊗d}`, by
composition with `g^{⊗d}`. In a split semisimple setting, when `ρ` is irreducible, this is the
multiplicity space of `ρ` in the tensor power, with its residual action of the general linear
group. -/
noncomputable def tensorPowerIntertwiningRep {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k (Equiv.Perm (Fin d)) W) :
    Representation k (GL (Fin n) k)
      (Representation.IntertwiningMap ρ (permTensorAction k n d)) where
  toFun g := Representation.IntertwiningMap.llcomp ρ _ _ (tensorPowerPermIntertwiningMap k n d g)
  map_one' := by
    ext f x
    simp only [← Representation.IntertwiningMap.comp_def,
      Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
      tensorPowerPermIntertwiningMap_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    ext f x
    simp only [← Representation.IntertwiningMap.comp_def,
      Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
      tensorPowerPermIntertwiningMap_apply, map_mul, Module.End.mul_apply]

variable {k n d} in
@[simp]
theorem tensorPowerIntertwiningRep_apply_apply {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k (Equiv.Perm (Fin d)) W) (g : GL (Fin n) k)
    (f : Representation.IntertwiningMap ρ (permTensorAction k n d)) (w : W) :
    tensorPowerIntertwiningRep ρ g f w = tensorPowerRep k n d g (f w) :=
  (rfl)

end CommRing

section InfiniteField

variable [Field k] [Infinite k]

/-- **The general linear group spans the same operators on `(kⁿ)^{⊗d}` as the whole endomorphism
algebra of `kⁿ`**: the span of the diagonal operators `g^{⊗d}` for `g` invertible is the span of all
the diagonal operators `f^{⊗d}`. This is the Zariski density of the invertible endomorphisms of
`kⁿ`, and it needs the field to be infinite. -/
theorem span_range_tensorPowerRep_eq_span_range_map_const :
    Submodule.span k (Set.range (tensorPowerRep k n d)) =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        PiTensorProduct.map fun _ : Fin d => f) := by
  have hrange : Set.range (tensorPowerRep k n d) =
      Set.range fun u : ((Fin n → k) →ₗ[k] Fin n → k)ˣ =>
        PiTensorProduct.map fun _ : Fin d => (u : (Fin n → k) →ₗ[k] Fin n → k) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨Matrix.GeneralLinearGroup.toLin g, ?_⟩
      rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
    · rintro ⟨u, rfl⟩
      obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.toLin.surjective u
      refine ⟨g, ?_⟩
      rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
  rw [hrange, PiTensorProduct.span_range_map_const_units_eq_span_range_map_const]

/-- **The image of the monoid algebra `k[GLₙ]` in `End ((kⁿ)^{⊗d})` is the span of all the
diagonal operators `f^{⊗d}`**, with `f` ranging over every endomorphism of `kⁿ` and not only the
invertible ones. -/
theorem toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const :
    Subalgebra.toSubmodule (tensorPowerRep k n d).asAlgebraHom.range =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        PiTensorProduct.map fun _ : Fin d => f) := by
  rw [Representation.toSubmodule_range_asAlgebraHom,
    span_range_tensorPowerRep_eq_span_range_map_const]

end InfiniteField

section Field

variable [Field k]

/-- The character of the tensor power is the corresponding power of the standard character.

This is intentionally not a simp lemma: `Representation.char_tensorPower` and `char_stdRep`
already normalize its left-hand side, so registering this specialization would violate `simpNF`. -/
theorem char_tensorPowerRep (g : GL (Fin n) k) : (tensorPowerRep k n d).character g =
      Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ d := by
  rw [Representation.char_tensorPower, char_stdRep]

/-- The character of the bundled tensor power is the corresponding power of the matrix trace. -/
@[simp]
theorem char_tensorPowerFDRep (g : GL (Fin n) k) : (tensorPowerFDRep k n d).character g =
      Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ d := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_tensorPowerRep k n d g

end Field

end TauCeti
end
end TAF_LiteralSource_0404

section TAF_LiteralSource_0405
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Rational -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- The two subalgebras of functions on `GL n k` the definitions below are stated against; this
-- module also supplies `MvPolynomial.eval`, in which their coordinate form is written.
-- The subalgebra-generic behaviour of matrix coefficients under change of basis, quotients,
-- tensor products and tensor powers; this module also supplies `Basis.piTensorProduct`, the basis
-- the tensor-power results below are stated against.

/-!
# Rational and polynomial representations of the general linear group

A representation of `GL n ℂ` is **polynomial** when, in some basis of the carrier, every matrix
entry of `ρ g` is a polynomial in the entries `gᵢⱼ`, and **rational** when every entry is such a
polynomial divided by a power of `det g`.  The distinction is the one that separates the
representations arising inside tensor powers of the standard representation from those needing a
determinant twist: `TauCeti.stdRep` and its tensor, symmetric and exterior powers are polynomial, as
is `det ^ m` for `m ≥ 0`, whereas `det ^ (-1)` is rational.

The two definitions quantify existentially over a basis, and the content of this file is that this
costs nothing: the condition holds in *one* basis exactly when it holds in *every* basis
(`TauCeti.isRationalRep_iff_forall_mem_rationalFunctions` and its polynomial companion), because a
change of basis rewrites each entry as a fixed linear combination of the old entries, with
coefficients independent of `g`.  So the existential form is a genuinely basis-independent property
of `ρ`, and the coordinate-entry form is available against whatever basis a computation has in hand.

The bookkeeping is carried by two algebras of functions on the group rather than by the
representations.  `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` collects the
`f : GL (Fin n) k → k` that evaluate some polynomial in the matrix entries, and
`TauCeti.Matrix.GeneralLinearGroup.rationalFunctions k n` those `f` for which some determinant power
`det ^ m` makes `det ^ m * f` polynomial.  Both are `k`-subalgebras of the functions on the group,
and closure under sums, products and scalars is what reduces every argument below to a single entry
computation: the change-of-basis formula is a sum of scalar multiples, the entries of a tensor
product are products of entries, and a determinant power is one generator.  Those entry computations
are themselves subalgebra-generic, and live in `TauCeti.RepresentationTheory.MatrixCoefficients`.

The two function algebras carry an arbitrary base ring, but the two *representation-level* notions
are stated over `ℂ`. The restriction is not cosmetic: over a finite
field `k` the group `GL n k` is a finite set and every function on it is the evaluation of a
polynomial in the matrix entries, so `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` is
then the whole function algebra and every finite-dimensional representation would count as
polynomial.  The coordinate-entry condition is faithful to the intended notion only over an infinite
field; here the base field is `ℂ`.

That the negative determinant powers are rational is
`TauCeti.Matrix.GeneralLinearGroup.det_zpow_mem_rationalFunctions`.  Whether a *given*
representation fails to be polynomial is a separate question, not addressed here; so is complete
reducibility of rational representations, which requires the theory of reductive groups.

## Main definitions

* `TauCeti.IsPolynomialRep`, `TauCeti.IsRationalRep`: a representation is polynomial, respectively
  rational, in coordinates.

## Main results

* `TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions` and
  `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`: **basis independence**, the entry
  condition against an arbitrary basis characterises the property.
* `TauCeti.IsRationalRep.dual_apply_mem_rationalFunctions`: the matrix coefficients
  `g ↦ f (ρ g w)` of a rational representation are rational functions, and
  `TauCeti.isRationalRep_iff_forall_dual_apply_mem_rationalFunctions`: this characterises
  rationality of a finite-dimensional representation.
* `TauCeti.IsRationalRep.directSum`: a finite direct sum of rational representations is rational.
* `TauCeti.IsPolynomialRep.isRationalRep`: a polynomial representation is rational.
* `TauCeti.isPolynomialRep_stdRep`: the standard representation is polynomial.
* `TauCeti.isRationalRep_detPowerRep` and `TauCeti.isPolynomialRep_detPowerRep_of_nonneg`:
  `det ^ m` is rational, and polynomial when `0 ≤ m`.
* `TauCeti.IsPolynomialRep.tprod` and `TauCeti.IsRationalRep.tprod`: both properties pass to tensor
  products.
* `TauCeti.IsPolynomialRep.of_surjective` and `TauCeti.IsRationalRep.of_surjective`: both
  properties pass to quotients.
* `TauCeti.IsPolynomialRep.tensorPower`, `TauCeti.IsPolynomialRep.symmetricPower` and
  `TauCeti.IsPolynomialRep.exteriorPower`, together with `TauCeti.IsRationalRep.tensorPower`,
  `TauCeti.IsRationalRep.symmetricPower` and `TauCeti.IsRationalRep.exteriorPower`: both properties
  pass to the functorial powers, whence `TauCeti.isPolynomialRep_tensorPowerRep`,
  `TauCeti.isPolynomialRep_symPowerRep` and `TauCeti.isPolynomialRep_extPowerRep` for the standard
  representation.

-/

public section

open Matrix MvPolynomial TauCeti.Matrix.GeneralLinearGroup

universe u v w x y z

namespace TauCeti

/-! ### Rationality and polynomiality of a representation -/

section Defs

variable {n : ℕ} {W : Type v} [AddCommMonoid W] [Module ℂ W]

/-- **A polynomial representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g`.  The carrier is forced to be finite-dimensional, since
no basis indexed by `Fin (Module.finrank ℂ W)` exists otherwise
(`TauCeti.IsPolynomialRep.finite`).  The condition does not depend on the basis: see
`TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions`.

The base field is `ℂ` rather than a general field because the coordinate-entry
condition is faithful only over an infinite field: over a finite `k` the group `GL n k` is finite,
so every function on it — hence every matrix entry of every representation — is polynomial in the
entries of `g`. -/
def IsPolynomialRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
    ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsPolynomialRep`, as a lemma. -/
theorem isPolynomialRep_iff (ρ : Representation ℂ (GL (Fin n) ℂ) W) :
    IsPolynomialRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
      ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ g) i j
          = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

/-- **A rational representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g` divided by a fixed power of `det g`.  The carrier is
forced to be finite-dimensional (`TauCeti.IsRationalRep.finite`), and the condition does not depend
on the basis: see `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`.  The base field is `ℂ`
for the reason recorded on `TauCeti.IsPolynomialRep`. -/
def IsRationalRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
    (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ *
          MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsRationalRep`, as a lemma. -/
theorem isRationalRep_iff (ρ : Representation ℂ (GL (Fin n) ℂ) W) :
    IsRationalRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
      (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ g) i j
          = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ *
            MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- The carrier of a polynomial representation is finite-dimensional. -/
theorem IsPolynomialRep.finite (h : IsPolynomialRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

/-- The carrier of a rational representation is finite-dimensional. -/
theorem IsRationalRep.finite (h : IsRationalRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

end Defs

section BasisIndependence

variable {n : ℕ} {W : Type v} [AddCommMonoid W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **Polynomiality is basis independent.**  A representation is polynomial exactly when, against
*any* chosen basis, each matrix entry is a polynomial function of the entries of `g`. -/
theorem isPolynomialRep_iff_forall_mem_polynomialFunctions {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsPolynomialRep ρ ↔
      ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ polynomialFunctions ℂ n := by
  have hcard : Module.finrank ℂ W = Fintype.card ι := Module.finrank_eq_card_basis b
  constructor
  · rintro ⟨b₀, P, hP⟩
    exact fun i j => Representation.toMatrix_mem_of_toMatrix_mem (polynomialFunctions ℂ n) b₀ b ρ
      (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ polynomialFunctions ℂ n :=
      fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    choose P hP using fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) =>
      mem_polynomialFunctions.mp (hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), fun g i j => hP (i, j) g⟩

/-- **Rationality is basis independent.**  A representation is rational exactly when, against *any*
chosen basis, each matrix entry is a rational function of the entries of `g`. -/
theorem isRationalRep_iff_forall_mem_rationalFunctions {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsRationalRep ρ ↔
      ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ rationalFunctions ℂ n := by
  have hcard : Module.finrank ℂ W = Fintype.card ι := Module.finrank_eq_card_basis b
  constructor
  · rintro ⟨b₀, P, m, hP⟩
    refine fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b₀ b ρ (fun p l => ?_) i j
    exact mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ rationalFunctions ℂ n :=
      fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    obtain ⟨P, m, hPm⟩ := exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions
      (f := fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) => fun g =>
        LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) q.1 q.2)
      (fun q => hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), m, fun g i j => hPm (i, j) g⟩

/-- A polynomial representation is rational. -/
theorem IsPolynomialRep.isRationalRep (h : IsPolynomialRep ρ) : IsRationalRep ρ := by
  obtain ⟨b, P, hP⟩ := h
  exact (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j =>
    polynomialFunctions_le_rationalFunctions
      (mem_polynomialFunctions.mpr ⟨P i j, fun g => hP g i j⟩)

/-- **A quotient of a polynomial representation is polynomial.**  This is the form in which the
functorial powers below inherit polynomiality from the tensor power. -/
theorem IsPolynomialRep.of_surjective {V : Type y} [AddCommMonoid V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsPolynomialRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsPolynomialRep σ := by
  -- `Module.finBasis` needs an additive group; over the field `ℂ` one is recovered from the module
  -- structure, with negation `(-1) • ·`, extending the given `AddCommMonoid`.
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isPolynomialRep_iff_forall_mem_polynomialFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    Representation.toMatrix_mem_of_toMatrix_mem_of_surjective (polynomialFunctions ℂ n) b
      (Module.finBasis ℂ V) f hf
      (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j

/-- **A quotient of a rational representation is rational.** -/
theorem IsRationalRep.of_surjective {V : Type y} [AddCommMonoid V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsRationalRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsRationalRep σ := by
  -- `Module.finBasis` needs an additive group; over the field `ℂ` one is recovered from the module
  -- structure, with negation `(-1) • ·`, extending the given `AddCommMonoid`.
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, m, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isRationalRep_iff_forall_mem_rationalFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    Representation.toMatrix_mem_of_toMatrix_mem_of_surjective (rationalFunctions ℂ n) b
      (Module.finBasis ℂ V) f hf
      (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

end BasisIndependence

/-! ### Matrix coefficients of a rational representation -/

section MatrixCoefficients

variable {n : ℕ} {W : Type v} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **The matrix coefficients of a rational representation are rational functions.** For a linear
functional `f` and a vector `w`, the function `g ↦ f (ρ g w)` is a polynomial in the entries of
`g` divided by a power of `det g`. -/
theorem IsRationalRep.dual_apply_mem_rationalFunctions (h : IsRationalRep ρ)
    (f : Module.Dual ℂ W) (w : W) : (fun g => f (ρ g w)) ∈ rationalFunctions ℂ n := by
  have := h.finite
  let b := Module.finBasis ℂ W
  have hb := (isRationalRep_iff_forall_mem_rationalFunctions b).mp h
  have heq : (fun g => f (ρ g w)) = ∑ i, ∑ j, (b.repr w j * f (b i)) •
      fun g => LinearMap.toMatrix b b (ρ g) i j := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← b.sum_repr (ρ g (b j))]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (hb i j) _

/-- **Rationality from matrix coefficients.** A finite-dimensional representation is rational
exactly when all its matrix coefficients `g ↦ f (ρ g w)` are rational functions. -/
theorem isRationalRep_iff_forall_dual_apply_mem_rationalFunctions [Module.Finite ℂ W] :
    IsRationalRep ρ ↔
      ∀ (f : Module.Dual ℂ W) (w : W), (fun g => f (ρ g w)) ∈ rationalFunctions ℂ n := by
  refine ⟨fun h => h.dual_apply_mem_rationalFunctions, fun h => ?_⟩
  let b := Module.finBasis ℂ W
  refine (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j => ?_
  simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply] using h (b.coord i) (b j)

/-- **A finite direct sum of rational representations is rational.** A matrix coefficient of the
direct sum is a sum of matrix coefficients of the summands. -/
theorem IsRationalRep.directSum {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {σ : ∀ i, Representation ℂ (GL (Fin n) ℂ) (V i)} (h : ∀ i, IsRationalRep (σ i)) :
    IsRationalRep (Representation.directSum σ) := by
  classical
  have := Fintype.ofFinite ι
  have (i : ι) : Module.Finite ℂ (V i) := (h i).finite
  refine isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr fun f w => ?_
  have heq : (fun g => f (Representation.directSum σ g w)) =
      ∑ i, fun g => (f ∘ₗ DirectSum.lof ℂ ι V i) (σ i g (w i)) := by
    funext g
    conv_lhs => rw [← DirectSum.sum_univ_of w]
    simp [Representation.directSum_apply, ← DirectSum.lof_eq_of ℂ]
  rw [heq]
  exact Subalgebra.sum_mem _ fun i _ => (h i).dual_apply_mem_rationalFunctions _ _

end MatrixCoefficients

/-! ### The basic examples -/

section Examples

variable (n : ℕ)

/-- **The standard representation is polynomial**: in the standard basis its matrix is `g`
itself. -/
@[simp]
theorem isPolynomialRep_stdRep : IsPolynomialRep (stdRep ℂ n) := by
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Pi.basisFun ℂ (Fin n))).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (stdRep ℂ n g) i j)
      = fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j := by
    funext g
    simp [Matrix.mulVec_single]
  rw [hentry]
  exact entry_mem_polynomialFunctions i j

variable {n}

/-- **The determinant powers are rational representations.** -/
@[simp]
theorem isRationalRep_detPowerRep (m : ℤ) : IsRationalRep (detPowerRep ℂ n m) := by
  refine (isRationalRep_iff_forall_mem_rationalFunctions
    (Module.Basis.singleton Unit ℂ)).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Module.Basis.singleton Unit ℂ) (Module.Basis.singleton Unit ℂ)
        (detPowerRep ℂ n m g) i j)
      = fun g : GL (Fin n) ℂ => ((Matrix.GeneralLinearGroup.det g ^ m : ℂˣ) : ℂ) := by
    funext g
    rw [LinearMap.toMatrix_singleton]
    simp
  rw [hentry]
  exact det_zpow_mem_rationalFunctions m

/-- **The nonnegative determinant powers are polynomial representations.** -/
@[simp]
theorem isPolynomialRep_detPowerRep_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    IsPolynomialRep (detPowerRep ℂ n m) := by
  lift m to ℕ using hm
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Module.Basis.singleton Unit ℂ)).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Module.Basis.singleton Unit ℂ) (Module.Basis.singleton Unit ℂ)
        (detPowerRep ℂ n (m : ℤ) g) i j)
      = fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det ^ m := by
    funext g
    rw [LinearMap.toMatrix_singleton]
    simp [zpow_natCast, Units.val_pow_eq_pow_val]
  rw [hentry]
  exact pow_mem det_mem_polynomialFunctions m

end Examples

section TensorProduct

variable {n : ℕ}
variable {W : Type v} [AddCommMonoid W] [Module ℂ W]
  {W' : Type x} [AddCommMonoid W'] [Module ℂ W']
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W} {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- **A tensor product of polynomial representations is polynomial.** -/
theorem IsPolynomialRep.tprod (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ) :
    IsPolynomialRep (ρ.tprod σ) := by
  -- `Representation.toMatrix_tprod_mem` is stated for additive groups; over the field `ℂ` they are
  -- recovered from the module structures, with negation `(-1) • ·`, extending the given monoids.
  let _ : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let _ : AddCommGroup W' := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, hP⟩ := hρ
  obtain ⟨c, Q, hQ⟩ := hσ
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions (b.tensorProduct c)).mpr fun i j => ?_
  exact Representation.toMatrix_tprod_mem _ b c
    (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩)
    (fun p l => mem_polynomialFunctions.mpr ⟨Q p l, fun g => hQ g p l⟩) i j

/-- **A tensor product of rational representations is rational.** -/
theorem IsRationalRep.tprod (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    IsRationalRep (ρ.tprod σ) := by
  -- `Representation.toMatrix_tprod_mem` is stated for additive groups; over the field `ℂ` they are
  -- recovered from the module structures, with negation `(-1) • ·`, extending the given monoids.
  let _ : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let _ : AddCommGroup W' := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, mP, hP⟩ := hρ
  obtain ⟨c, Q, mQ, hQ⟩ := hσ
  refine (isRationalRep_iff_forall_mem_rationalFunctions (b.tensorProduct c)).mpr fun i j => ?_
  exact Representation.toMatrix_tprod_mem _ b c
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, mP, fun g => hP g p l⟩)
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨Q p l, mQ, fun g => hQ g p l⟩) i j

end TensorProduct

/-! ### The functorial powers -/

section FunctorialPowers

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **A tensor power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.tensorPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.tensorPower d) := by
  obtain ⟨b, P, hP⟩ := h
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Basis.piTensorProduct fun _ : Fin d => b)).mpr fun i j => ?_
  exact Representation.toMatrix_tensorPower_mem _ b
    (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j

/-- **A tensor power of a rational representation is rational.** -/
theorem IsRationalRep.tensorPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.tensorPower d) := by
  obtain ⟨b, P, m, hP⟩ := h
  refine (isRationalRep_iff_forall_mem_rationalFunctions
    (Basis.piTensorProduct fun _ : Fin d => b)).mpr fun i j => ?_
  exact Representation.toMatrix_tensorPower_mem _ b
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

/-- The canonical map onto the symmetric power, as a surjective intertwining map out of the tensor
power.  It is what makes the symmetric power inherit polynomiality and rationality. -/
private noncomputable def symmetricPowerIntertwiningMap (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Representation.IntertwiningMap (ρ.tensorPower d) (ρ.symmetricPower d) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (SymmetricPower.mk ℂ (Fin d) W) fun g x => by
    simp

private theorem symmetricPowerIntertwiningMap_surjective (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Function.Surjective (symmetricPowerIntertwiningMap ρ d) :=
  LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin d) W)

/-- The canonical map onto the exterior power, as a surjective intertwining map out of the tensor
power.  It is what makes the exterior power inherit polynomiality and rationality. -/
private noncomputable def exteriorPowerIntertwiningMap (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Representation.IntertwiningMap (ρ.tensorPower d) (ρ.exteriorPower d) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (exteriorPower.fromTensorPower ℂ W d)
    fun g x => by
      simpa using (LinearMap.congr_fun (exteriorPower.map_comp_fromTensorPower d (ρ g)) x).symm

private theorem exteriorPowerIntertwiningMap_surjective (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Function.Surjective (exteriorPowerIntertwiningMap ρ d) :=
  exteriorPower.fromTensorPower_surjective d

/-- **A symmetric power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.symmetricPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.symmetricPower d) :=
  (h.tensorPower d).of_surjective (symmetricPowerIntertwiningMap ρ d)
    (symmetricPowerIntertwiningMap_surjective ρ d)

/-- **A symmetric power of a rational representation is rational.** -/
theorem IsRationalRep.symmetricPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.symmetricPower d) :=
  (h.tensorPower d).of_surjective (symmetricPowerIntertwiningMap ρ d)
    (symmetricPowerIntertwiningMap_surjective ρ d)

/-- **An exterior power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.exteriorPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.exteriorPower d) :=
  (h.tensorPower d).of_surjective (exteriorPowerIntertwiningMap ρ d)
    (exteriorPowerIntertwiningMap_surjective ρ d)

/-- **An exterior power of a rational representation is rational.** -/
theorem IsRationalRep.exteriorPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.exteriorPower d) :=
  (h.tensorPower d).of_surjective (exteriorPowerIntertwiningMap ρ d)
    (exteriorPowerIntertwiningMap_surjective ρ d)

variable (n d : ℕ)

/-- **The tensor powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_tensorPowerRep : IsPolynomialRep (tensorPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).tensorPower d

/-- **The symmetric powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_symPowerRep : IsPolynomialRep (symPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).symmetricPower d

/-- **The exterior powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_extPowerRep : IsPolynomialRep (extPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).exteriorPower d

end FunctorialPowers

end TauCeti
end
end TAF_LiteralSource_0405

section TAF_LiteralSource_0406
/- Original module: TauCeti.Analysis.InnerProductSpace.Positive.Definite -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# A positive-definite form is the standard one in suitable coordinates

Let `S` be a symmetric operator on a finite-dimensional inner product space `V` whose associated
Hermitian form `⟪S v, w⟫` is positive definite. This file produces a linear automorphism of `V`
along which that form pulls back to the inner product `V` already carries:

`TauCeti.exists_continuousLinearEquiv_inner_map_map` gives `e : V ≃L[𝕜] V` with
`⟪S (e x), e y⟫ = ⟪x, y⟫` for all `x` and `y`.

Equivalently `e` is an isometry from `(V, ⟪·,·⟫)` onto `(V, ⟪S ·, ·⟫)`, so its inverse is the
operator usually written `S ^ (1 / 2)`; the construction here avoids building an operator square
root by scaling an orthonormal eigenbasis of `S` instead. The eigenvalues of `S` are positive
because the form is definite, so dividing the `i`-th eigenvector by `√(λ i)` produces a basis that
is orthonormal *for the form*, and `e` is the map carrying the eigenbasis to it.

## Main statements

* `TauCeti.exists_continuousLinearEquiv_inner_map_map`: a positive-definite symmetric operator's
  form becomes the standard inner product after a change of coordinates.

Only the existence of `e` is exported, since it depends on a choice of eigenbasis. The operator is
taken continuous and the change of coordinates produced is a continuous linear equivalence; on a
finite-dimensional space that is no restriction either way, and it is the form the consumer both
supplies and wants.

The intended consumer is Weyl's unitarian trick: applied to the Gram operator of the Haar-averaged
inner product of a representation of a compact group, this is what turns the invariant form into
an honest unitary structure, in
`TauCeti/RepresentationTheory/Compact/UnitaryModel.lean`.
-/

public section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **A positive-definite form is standard in suitable coordinates.** If `S` is a symmetric
operator on a finite-dimensional inner product space whose form `⟪S ·, ·⟫` is positive definite,
then there is a continuous linear automorphism `e` with `⟪S (e x), e y⟫ = ⟪x, y⟫`.

The automorphism is the inverse of the square root of `S`, built without any operator functional
calculus: an orthonormal eigenbasis `b` of `S` has positive eigenvalues `λ i`, so the vectors
`(√(λ i))⁻¹ • b i` are orthonormal for the form `⟪S ·, ·⟫`, and `e` is the automorphism carrying
`b i` to them. -/
theorem exists_continuousLinearEquiv_inner_map_map (S : V →L[𝕜] V)
    (hsymm : (S : V →ₗ[𝕜] V).IsSymmetric) (hpos : ∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) :
    ∃ e : V ≃L[𝕜] V, ∀ x y : V, ⟪S (e x), e y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  set n := Module.finrank 𝕜 V with hn
  set b := hsymm.eigenvectorBasis hn.symm
  set lam := hsymm.eigenvalues hn.symm
  have hSb : ∀ i, S (b i) = (lam i : 𝕜) • b i := fun i ↦
    hsymm.apply_eigenvectorBasis hn.symm i
  have hbb : ∀ i j, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- The eigenvalues are positive: `⟪S (b i), b i⟫ = λ i` and the form is definite.
  have hlam : ∀ i, 0 < lam i := fun i ↦ by
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rw [hSb i, inner_smul_left, hbb i i] at h
    simpa using h
  -- Scaling the `i`-th eigenvector by `(√(λ i))⁻¹` makes the family orthonormal for the form.
  set w : Fin n → 𝕜 := fun i ↦ ((Real.sqrt (lam i))⁻¹ : ℝ) with hwdef
  have hw : ∀ i, IsUnit (w i) := fun i ↦ by
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hwdef, Real.sqrt_eq_zero', (hlam i).not_ge]
  set el : V ≃ₗ[𝕜] V := b.toBasis.equiv (b.toBasis.isUnitSMul hw) (Equiv.refl (Fin n)) with heldef
  set e : V ≃L[𝕜] V := el.toContinuousLinearEquiv with hedef
  have he' : ∀ i, e (b.toBasis i) = w i • b.toBasis i := fun i ↦ by
    simp only [hedef, heldef, LinearEquiv.coe_toContinuousLinearEquiv',
      Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.isUnitSMul_apply]
  have he : ∀ i, e (b i) = w i • b i := by simpa only [b.coe_toBasis] using he'
  have hkey : ∀ i j, ⟪S (e (b i)), e (b j)⟫_𝕜 = if i = j then 1 else 0 := fun i j ↦ by
    rw [he i, he j, map_smul, hSb i, smul_smul, inner_smul_left, inner_smul_right, hbb i j]
    rcases eq_or_ne i j with rfl | hij
    · have hr : ((Real.sqrt (lam i))⁻¹ * lam i * (Real.sqrt (lam i))⁻¹ : ℝ) = 1 := by
        have hne : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
        field_simp
        exact (Real.sq_sqrt (hlam i).le).symm
      rw [ite_eq_left rfl, mul_one, hwdef, ← RCLike.ofReal_mul, conj_ofReal, ← RCLike.ofReal_mul,
        hr, RCLike.ofReal_one]
    · simp [hij]
  -- Both sides are sesquilinear, so the basis computation determines them.
  refine ⟨e, fun x y ↦ ?_⟩
  rw [← b.sum_inner_mul_inner x y]
  conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hkey]
  simp [inner_conj_symm, mul_comm]

end TauCeti
end
end TAF_LiteralSource_0406

section TAF_LiteralSource_0407
/- Original module: TauCeti.RepresentationTheory.Compact.Haar -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance.

The Layer 0 design follows the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
and its accompanying `Suggested.lean`.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.
-/

public section

open MeasureTheory Set

namespace TauCeti

section LocallyCompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a nonempty locally compact group has nonzero total mass. -/
theorem haar_univ_ne_zero : (Measure.haar : Measure G) univ ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior (μ := Measure.haar) (by simp)).ne'

/-- Every probability Haar measure on a locally compact group is right-invariant. -/
theorem isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : (Measure.map (· * g) μ).IsHaarMeasure :=
      Measure.isHaarMeasure_map_mul_right μ g
    have : IsProbabilityMeasure (Measure.map (· * g) μ) :=
      inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Every probability Haar measure on a locally compact group is invariant under inversion. -/
theorem isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant :=
    isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) μ
  constructor
  let : μ.inv.IsHaarMeasure := {
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsMulLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }
  let : IsProbabilityMeasure μ.inv := by
    rw [Measure.inv_def]
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end LocallyCompactGroup

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a compact group has finite total mass. -/
theorem haar_univ_lt_top : (Measure.haar : Measure G) univ < ⊤ :=
  measure_lt_top _ _

private noncomputable def haarFinite : FiniteMeasure G :=
  ⟨Measure.haar, inferInstance⟩

/-- The finite measure used to normalize Haar measure has underlying measure `Measure.haar`. -/
private theorem haarFinite_toMeasure : (haarFinite G : Measure G) = Measure.haar := by
  ext s _
  rfl

private theorem haarFinite_ne_zero : haarFinite G ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff]
  apply ENNReal.coe_ne_zero.mp
  rw [FiniteMeasure.ennreal_mass, haarFinite_toMeasure]
  exact haar_univ_ne_zero G

/-- Haar probability measure on a compact topological group. -/
noncomputable def haarProb : Measure G :=
  (haarFinite G).normalize

/-- The definition of normalized Haar measure as a rescaling of Mathlib's Haar measure. -/
theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar :=
  by
    rw [haarProb,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero (haarFinite G) (haarFinite_ne_zero G)]
    rw [← haarFinite_toMeasure, ← FiniteMeasure.ennreal_mass, ← ENNReal.coe_inv]
    · rfl
    · exact (FiniteMeasure.mass_nonzero_iff (haarFinite G)).mpr (haarFinite_ne_zero G)

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) := by
  exact (haarFinite G).normalize.property

/-- Normalized Haar measure has total mass one.

Not a `simp` lemma: `simp` already closes this goal from the `IsProbabilityMeasure` instance
via `MeasureTheory.measure_univ`. -/
theorem haarProb_apply_univ : haarProb G univ = 1 :=
  measure_univ

instance isMulLeftInvariant_haarProb : (haarProb G).IsMulLeftInvariant := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))

/-- Normalized Haar measure is invariant under right multiplication. -/
instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant :=
  isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

/-- A probability Haar measure on a compact group is the normalized Haar measure. -/
theorem eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ = haarProb G :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactGroup

end TauCeti
end
end TAF_LiteralSource_0407

section TAF_LiteralSource_0408
/- Original module: TauCeti.RepresentationTheory.Compact.Averaging -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Averaging over compact groups

This file bundles integration against normalized Haar measure as a continuous linear map on
continuous vector-valued functions. It records the norm bound, constants, and invariance under left
and right translation needed for averaging representations.

The implementation reuses Mathlib's Bochner integral, its commutation with continuous linear maps,
and the generic left-, right-, and inversion-invariance lemmas for integrals on groups.

The construction is the averaging operator from Layer 0 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [NormedAddCommGroup V]

/-- A continuous vector-valued function on a compact group is Bochner integrable against
normalized Haar measure: it is continuous on the compact set `univ`, which carries finite
measure. -/
theorem integrable_continuousMap (f : C(G, V)) :
    Integrable f (haarProb G) := by
  simpa only [integrableOn_univ] using
    f.continuous.continuousOn.integrableOn_compact' (μ := haarProb G) isCompact_univ
      MeasurableSet.univ

section NormedFieldScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]

/-- Averaging a continuous vector-valued function against normalized Haar measure, as a
continuous linear map.

`V` is not assumed complete, so this is the Bochner integral's junk value `0` unless it is: the
definition and its linear structure need no completeness, and the lemmas below that talk about the
average's actual value (`haarAverage_const`, `norm_haarAverage_eq_one`, and everything reached
through `haarAverage_comp_comm`) ask for `[CompleteSpace V]` precisely because they do. -/
noncomputable def haarAverage : C(G, V) →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ g, f g ∂haarProb G
      map_add' := fun f h ↦ integral_add
        (integrable_continuousMap G f) (integrable_continuousMap G h)
      map_smul' := fun c f ↦ integral_smul c f }
    1 fun f ↦ by
      rw [one_mul]
      simpa using norm_integral_le_of_norm_le_const
        (μ := haarProb G) (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- The Haar average is the Bochner integral against normalized Haar measure.

Not a `simp` lemma: `haarAverage` is the normal form here, so that the constant, translation
and inversion lemmas below can be `simp` lemmas. Unfold explicitly with `rw`/`simp` when the
underlying integral is wanted. -/
theorem haarAverage_apply (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = ∫ g, f g ∂haarProb G :=
  (rfl)

/-- The operator norm of Haar averaging is at most one. -/
theorem norm_haarAverage_le_one :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Haar averaging is norm-nonincreasing for the uniform norm on continuous maps. -/
theorem norm_haarAverage_apply_le (f : C(G, V)) :
    ‖haarAverage G (𝕜 := 𝕜) f‖ ≤ ‖f‖ := by
  simpa using (haarAverage G (𝕜 := 𝕜) (V := V)).le_of_opNorm_le (norm_haarAverage_le_one G) f

/-- The Haar average of a constant function is that constant. -/
@[simp]
theorem haarAverage_const [CompleteSpace V] (v : V) :
    haarAverage G (𝕜 := 𝕜) (ContinuousMap.const G v) = v := by
  simp [haarAverage_apply]

/-- On a nonzero target, Haar averaging has operator norm one. -/
theorem norm_haarAverage_eq_one [Nontrivial V] [CompleteSpace V] :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ = 1 := by
  apply le_antisymm (norm_haarAverage_le_one G) _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hnorm : ‖ContinuousMap.const G v‖ = ‖v‖ := by
    rw [← (ContinuousMap.linearIsometryBoundedOfCompact G V 𝕜).norm_map]
    exact BoundedContinuousFunction.norm_const_eq v
  have h := (haarAverage G (𝕜 := 𝕜) (V := V)).ratio_le_opNorm
    (ContinuousMap.const G v)
  simpa [haarAverage_const, hnorm, norm_ne_zero_iff.mpr hv] using h

/-- Haar averaging is unchanged by left translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulLeft (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulLeft g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulLeft]
  exact integral_mul_left_eq_self f g

/-- Haar averaging is unchanged by right translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulRight (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulRight g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulRight]
  exact integral_mul_right_eq_self f g

/-- Haar averaging is unchanged by inversion of the argument. -/
@[simp]
theorem haarAverage_comp_inv (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) (f.comp (Homeomorph.inv G : C(G, G))) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_ofClass, Homeomorph.coe_inv]
  exact integral_inv_eq_self f (haarProb G)

end NormedFieldScalars

section RCLikeScalars

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

/-- Continuous linear maps commute with Haar averaging.

The scalars are assumed to be `RCLike` because Mathlib states
`ContinuousLinearMap.integral_comp_comm` under that hypothesis. -/
@[simp]
theorem _root_.ContinuousLinearMap.haarAverage_comp_comm {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedSpace 𝕜 W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace V] [CompleteSpace W]
    (L : V →L[𝕜] W) (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) ((L : C(V, W)).comp f) = L (haarAverage G (𝕜 := 𝕜) f) := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_ofClass]
  exact L.integral_comp_comm (integrable_continuousMap G f)

end RCLikeScalars

end CompactGroup

end TauCeti
end
end TAF_LiteralSource_0408

