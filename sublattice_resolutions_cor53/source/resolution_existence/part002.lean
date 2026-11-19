module
public import mixed_results.part001
public import shared_results.part014
public import graph_foundation.part012
public import graph_foundation.part004
public import Mathlib.LinearAlgebra.DirectSum.Basis

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialFineContraction -/
section

/-! # A fine homogeneous contraction of the literal monomial Koszul complex

The coefficient basis consists of every monomial in the actual ideal. Its
tensor product with the exterior basis has the fine degree given by the sum
of the coefficient exponent and the squarefree exterior exponent. Splitting
the kernel/image quotient in each fine and homological degree therefore
retains all fine shifts, including when different variables are subsequently
assigned different positive weights.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice.MonomialFineResolution
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open HomologicalPerturbation DirectSum
open scoped TensorProduct
attribute [local instance] Classical.propDecidable
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (B : Family V)

local notation "S" => MvPolynomial V K
local notation "M" => monomialIdeal K B

abbrev Index := {a : Exponent V // Contains B a} × Finset V

/-- The actual tensor Koszul module of the monomial ideal. -/
abbrev TensorModule := M ⊗[K] Simplicial.Ambient V K

def tensorBasis : Module.Basis (Index B) K (M ⊗[K] Simplicial.Ambient V K) :=
  (monomialBasis (k := K) B).tensorProduct Simplicial.basis

def fineDegree (a : Index B) : Exponent V := a.1.val+faceExponent a.2

def homological (a : Index B) : ℕ := a.2.card

def differential : Module.End K (M ⊗[K] Simplicial.Ambient V K) :=
  TensorExteriorKoszul.differential (K := K) («M» := M) (X : V → S)

@[simp] theorem tensorBasis_apply (a : {a : Exponent V // Contains B a}) (F : Finset V) :
    tensorBasis (K := K) B (a,F)=monomialBasis B a ⊗ₜ[K] Simplicial.basis F :=
  Module.Basis.tensorProduct_apply _ _ _ _

attribute [irreducible] tensorBasis

/-- The coordinate-to-tensor map preserves the complete fine degree. -/
theorem lift_fine_mem (α : Exponent V) (p : ℕ)
    (x : Set.powersetCard V p →₀ M)
    (hx : x ∈ homogeneousPiece (k := K) B α p) :
    TensorExteriorKoszul.lift (K := K) p x ∈
      BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B)
        (tensorBasis (K := K) B) (fineDegree B) (homological B) α p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [monomialCoefficientBasis_apply, TensorExteriorKoszul.lift_single,
        ← tensorBasis_apply (K := K) B i.2 i.1.val]
      exact Submodule.subset_span ⟨(i.2, i.1.val), Prod.ext hi i.1.property, rfl⟩
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- Fine homogeneity is transported from the literal coordinate differential. -/
theorem differential_basis_mem (a : {a : Exponent V // Contains B a})
    (F : Finset V) (p : ℕ) (hF : F.card = p+1) :
    differential (K := K) B (tensorBasis (K := K) B (a,F)) ∈
      BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B)
        (tensorBasis (K := K) B) (fineDegree B) (homological B)
        (fineDegree B (a,F)) p := by
  let i : MonomialIndex B (p+1) := ⟨⟨F,hF⟩,a⟩
  have hx : monomialCoefficientBasis (k := K) B (p+1) i ∈
      homogeneousPiece (k := K) B (fineDegree B (a,F)) (p+1) :=
    Grading.basis_mem_piece (monomialCoefficientBasis (k := K) B (p+1))
      monomialDegree i
  have h := monomialDifferential_homogeneous (k := K) B (fineDegree B (a,F)) p hx
  rw [monomialCoefficientBasis_apply] at h
  rw [tensorBasis_apply, differential,
    ← TensorExteriorKoszul.lift_single (K := K) (p+1)
      (⟨F,hF⟩ : Set.powersetCard V (p+1)) (monomialBasis (k := K) B a),
    TensorExteriorKoszul.differential_lift]
  exact lift_fine_mem (K := K) B (fineDegree B (a,F)) p _ h

theorem differential_lowers (α : Exponent V) (p : ℕ)
    (x : M ⊗[K] Simplicial.Ambient V K)
    (hx : x∈BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B)
      (homological B) α (p+1)) :
    differential (K := K) B x∈BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B)
      (homological B) α p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨a,F⟩,ha,rfl⟩ := hx
      have hα := congrArg Prod.fst ha
      have hp := congrArg Prod.snd ha
      change fineDegree B (a,F) = α at hα
      change F.card = p+1 at hp
      simpa only [hα] using differential_basis_mem B a F p hp
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem differential_zero (α : Exponent V) (x : M ⊗[K] Simplicial.Ambient V K)
    (hx : x∈BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B)
      (homological B) α 0) : differential (K := K) B x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨a,F⟩,ha,rfl⟩ := hx
      have hF : F=∅ := Finset.card_eq_zero.mp (congrArg Prod.snd ha)
      rw [tensorBasis_apply,differential,TensorExteriorKoszul.differential_tmul,hF]
      simp only [Simplicial.contraction_basis,Finset.notMem_empty,if_false,
        TensorProduct.tmul_zero,Finset.sum_const_zero]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

theorem differential_square : (differential (K := K) B).comp (differential (K := K) B)=0 :=
  TensorExteriorKoszul.differential_comp (X : V → S)

abbrev Strand (α : Exponent V) (p : ℕ) :=
  BasisMultigradedContraction.StrandHomology (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B)
    (homological B) (differential (K := K) B) (differential_square (K := K) B) (differential_lowers (K := K) B) α p

abbrev Homology := ⨁ α : Exponent V, ⨁ p : ℕ, Strand (K := K) B α p

theorem strandProjective (α : Exponent V) (p : ℕ) :
    Module.Projective K (Strand (K := K) B α p) := inferInstance

def contraction :=
  BasisMultigradedContraction.contraction (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B) (homological B)
    (differential (K := K) B) (differential_square (K := K) B) (differential_lowers (K := K) B) (fun _ _ => by infer_instance)

theorem contraction_d : (contraction (K := K) B).d=differential (K := K) B := by
  have h := BasisMultigradedContraction.contraction_d (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B) (homological B)
    (differential (K := K) B) (differential_square (K := K) B) (differential_lowers (K := K) B) (differential_zero (K := K) B)
    (fun _ _ => by infer_instance)
  exact h

theorem contraction_h_fine (α : Exponent V) (p : ℕ)
    (x : BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B)
      (fineDegree B) (homological B) α p) :
    (contraction (K := K) B).h x.val∈BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B)
      (fineDegree B) (homological B) α (p+1) := by
  have h := BasisMultigradedContraction.contraction_h_mem (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B) (homological B)
    (differential (K := K) B) (differential_square (K := K) B) (differential_lowers (K := K) B) (fun _ _ => by infer_instance) α p x
  exact h

theorem fineDegree_degree (a : Index B) :
    (fineDegree B a).degree=a.1.val.degree+a.2.card := by
  simp [fineDegree,faceExponent,map_sum,Finsupp.degree_single]

theorem contraction_h_nonincreasing :
    DegreeNonincreasing (PolynomialPerturbation.tensorBasis M (monomialBasis B))
      (PolynomialPerturbation.internalDegree (fun a : {a : Exponent V // Contains B a} =>
        a.val.degree)) (contraction (K := K) B).h := by
  have h := BasisMultigradedContraction.contraction_h_nonincreasing (R := K) («M» := TensorModule (K := K) B)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B) (fun _ _ => by infer_instance) Finsupp.degree
  have hdegree : (fun a : Index B => (fineDegree B a).degree) =
      PolynomialPerturbation.internalDegree
        (fun a : {a : Exponent V // Contains B a} => a.val.degree) := by
    funext a
    exact fineDegree_degree B a
  rw [hdegree] at h
  have hb : PolynomialPerturbation.tensorBasis (R := K) (V := V) M
      (monomialBasis (k := K) B) = tensorBasis (K := K) B := by
    unfold tensorBasis PolynomialPerturbation.tensorBasis
    rfl
  rw [hb]
  exact h

abbrev HomologyIndex := Σ α : Exponent V, Σ p : ℕ,
  Module.Free.ChooseBasisIndex K (Strand (K := K) B α p)

/-- The degreewise basis is named once so its induced module structures
are shared by the direct-sum constructor and its coordinate lemmas. -/
def chooseBasisFamily (α : Exponent V) (p : ℕ) :=
  Module.Free.chooseBasis K (Strand (K := K) B α p)

abbrev homologyBasis :=
  FourPapers.nestedDirectSumBasis (R := K) (chooseBasisFamily (K := K) B)

def freeBasis : Module.Basis (HomologyIndex (K := K) B) S (S ⊗[K] Homology (K := K) B) :=
  (homologyBasis (K := K) B).baseChange S

def freeModel : LinearDeformationRetract
    (R := S) («M» := PolynomialModuleResolution.Bar (R := K) (V := V) M)
    (H := S ⊗[K] Homology (K := K) B) := by
  let A := PolynomialPerturbation.transferred (R := K) (V := V) M
    (contraction (K := K) B) (contraction_d (K := K) B)
    (monomialBasis (k := K) B) (fun a => a.val.degree)
    (contraction_h_nonincreasing (K := K) B)
  exact A

/-- Every actual differential entry is minimal. Its fine shift is the
exponent label of the homology basis, retained by the contraction above. -/
theorem freeModel_minimal (i j : HomologyIndex (K := K) B) :
    (freeBasis (K := K) B).repr ((freeModel (K := K) B).targetD (freeBasis (K := K) B i)) j∈MvPolynomial.idealOfVars V K := by
  have h := PolynomialPerturbation.differential_entries_in_variableIdeal
    (R := K) (V := V) M (contraction (K := K) B)
    (contraction_d (K := K) B) (monomialBasis (k := K) B) (fun a => a.val.degree)
    (contraction_h_nonincreasing (K := K) B) (freeBasis (K := K) B) i j
  exact h

end FourPapers.Sublattice.MonomialFineResolution

end
end
end

end
