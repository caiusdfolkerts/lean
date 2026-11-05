module

public import PaperVerification.AlternatingFormsOddTransport
public import PaperVerification.AlternatingFormsTopInterlacing
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.ExteriorPower
import Lean.Elab.Tactic.Omega

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
