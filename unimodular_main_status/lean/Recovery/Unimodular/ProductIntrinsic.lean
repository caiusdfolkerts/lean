module

public import Recovery.Unimodular.ProductLattice
public import Recovery.Unimodular.ProductBasisPartition
public import TauCeti.Geometry.Toric.Algebraic.Lattice

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set TauCeti.Toric
open scoped BigOperators DirectSum

namespace Unimodular.ComponentLattice

variable {n : ℕ}

abbrev standardEmbedding (n : ℕ) : Lattice n →+ Ambient n :=
  (Int.castAddHom ℝ).compLeft (Fin n)

@[simp] theorem standardEmbedding_apply (x : Lattice n) :
    standardEmbedding n x = embed x := rfl

/-- Real membership of integral component combinations holds without any
unimodularity assumption. -/
theorem embed_mem_realSpan (U : Set (Lattice n)) (c : Components U)
    {x : Lattice n} (hx : x ∈ latticeSpan U c) : embed x ∈ realSpan U c := by
  have hle : latticeSpan U c ≤ ((realSpan U c).restrictScalars ℤ).comap
      (standardEmbedding n).toIntLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  exact hle hx

/-- The literal embedding of each intrinsic component sublattice in its
intrinsic real span. Its definition makes no basis choice. -/
def componentEmbedding (U : Set (Lattice n)) (c : Components U) :
    latticeSpan U c →+ realSpan U c where
  toFun x := ⟨embed x.val, embed_mem_realSpan U c x.property⟩
  map_zero' := Subtype.ext ((standardEmbedding n).map_zero)
  map_add' x y := Subtype.ext ((standardEmbedding n).map_add x.val y.val)

@[simp] theorem componentEmbedding_coe (U : Set (Lattice n)) (c : Components U)
    (x : latticeSpan U c) : (componentEmbedding U c x : Ambient n) = embed x.val := rfl

def realBasis (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℝ (Ambient n) :=
  (isIntegralLattice_intCast n).isBaseChange.basis b

@[simp] theorem realBasis_apply (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    realBasis b i = embed (b i) :=
  (isIntegralLattice_intCast n).isBaseChange.basis_apply b i

theorem lattice_internal {U : Set (Lattice n)} [DecidableEq (Components U)]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U) :
    DirectSum.IsInternal (latticeSpan U) := by
  have he : latticeSpan U = BasisPartition.block b (basisComponent b hb) :=
    funext (latticeSpan_eq_basis_span b hb)
  rw [he]
  exact BasisPartition.blocks_internal b (basisComponent b hb)

theorem real_internal {U : Set (Lattice n)} [DecidableEq (Components U)]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U) :
    DirectSum.IsInternal (realSpan U) := by
  have he : realSpan U = BasisPartition.block (realBasis b) (basisComponent b hb) := by
    funext c
    simpa only [BasisPartition.block, realBasis_apply] using realSpan_eq_basis_span b hb c
  rw [he]
  exact BasisPartition.blocks_internal (realBasis b) (basisComponent b hb)

/-- The two canonical internal direct sums follow from the original
unimodular spanning configuration, with no supplied decomposition. -/
theorem uniform_internal (U : Set (Lattice n)) [DecidableEq (Components U)]
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤) :
    DirectSum.IsInternal (latticeSpan U) ∧ DirectSum.IsInternal (realSpan U) := by
  obtain ⟨b, hb, _⟩ := LatticeHull.exists_lattice_basis_extension U hU hspan
    (fun i : Fin 0 => (Fin.elim0 i : U)) (linearIndependent_empty_type)
  exact ⟨lattice_internal b hb, real_internal b hb⟩

/-- Each canonical factor is a genuine finite free integral lattice with
the correct scalar extension; injectivity and spanning alone are not assumed
to imply this stronger statement. -/
theorem component_isIntegralLattice {U : Set (Lattice n)}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U)
    (c : Components U) : IsIntegralLattice (componentEmbedding U c) := by
  classical
  let I := {i : Fin n // basisComponent b hb i = c}
  have hz : Submodule.span ℤ (Set.range (fun i : I => b i.val)) = latticeSpan U c := by
    rw [latticeSpan_eq_basis_span b hb c]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(⟨i, hi⟩ : I), rfl⟩
  have hr : Submodule.span ℝ (Set.range (fun i : I => realBasis b i.val)) = realSpan U c := by
    rw [realSpan_eq_basis_span b hb c]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, (realBasis_apply b i.val).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(⟨i, hi⟩ : I), realBasis_apply b i⟩
  let bz : Module.Basis I ℤ (latticeSpan U c) :=
    (Module.Basis.span (b.linearIndependent.comp (fun i : I => i.val)
      Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ hz)
  let br : Module.Basis I ℝ (realSpan U c) :=
    (Module.Basis.span ((realBasis b).linearIndependent.comp (fun i : I => i.val)
      Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ hr)
  apply isIntegralLattice_of_basis bz br
  intro i
  apply Subtype.ext
  change embed (bz i : Lattice n) = (br i : Ambient n)
  simp only [bz, br, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply, Function.comp_apply, realBasis_apply]

section Finite

variable {U : Set (Lattice n)} [Fintype (Components U)] [DecidableEq (Components U)]
  (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U)

/-- Assemble integral component vectors by adding their original inclusions. -/
def integralAssembly : (∀ c, latticeSpan U c) ≃ₗ[ℤ] Lattice n :=
  BasisPartition.productEquiv (latticeSpan U) (lattice_internal b hb)

/-- Assemble real component vectors by adding their original inclusions. -/
def realAssembly : (∀ c, realSpan U c) ≃ₗ[ℝ] Ambient n :=
  BasisPartition.productEquiv (realSpan U) (real_internal b hb)

def integralDecomposition : Lattice n ≃ₗ[ℤ] (∀ c, latticeSpan U c) :=
  (integralAssembly b hb).symm

def realDecomposition : Ambient n ≃ₗ[ℝ] (∀ c, realSpan U c) :=
  (realAssembly b hb).symm

theorem integralAssembly_apply (x : ∀ c, latticeSpan U c) :
    integralAssembly b hb x = ∑ c, (x c : Lattice n) :=
  BasisPartition.productEquiv_apply _ _ _

theorem realAssembly_apply (x : ∀ c, realSpan U c) :
    realAssembly b hb x = ∑ c, (x c : Ambient n) :=
  BasisPartition.productEquiv_apply _ _ _

/-- Compatibility of the actual integral and real component decompositions. -/
theorem decomposition_compatible (x : Lattice n) :
    realDecomposition b hb (embed x) =
      fun c => componentEmbedding U c (integralDecomposition b hb x c) := by
  apply (realAssembly b hb).injective
  rw [show realAssembly b hb (realDecomposition b hb (embed x)) = embed x from
    (realAssembly b hb).apply_symm_apply _]
  rw [realAssembly_apply]
  have hx : ∑ c, (integralDecomposition b hb x c : Lattice n) = x := by
    rw [← integralAssembly_apply]
    exact (integralAssembly b hb).apply_symm_apply x
  calc
    embed x = embed (∑ c, (integralDecomposition b hb x c : Lattice n)) :=
      congrArg embed hx.symm
    _ = ∑ c, embed (integralDecomposition b hb x c : Lattice n) :=
      map_sum (standardEmbedding n) _ _
    _ = _ := rfl

theorem realDecomposition_of_mem {c : Components U} {x : Ambient n}
    (hx : x ∈ realSpan U c) : realDecomposition b hb x c = ⟨x, hx⟩ :=
  BasisPartition.productEquiv_symm_of_mem _ _ hx

theorem realDecomposition_of_mem_ne {c d : Components U} (hcd : c ≠ d)
    {x : Ambient n} (hx : x ∈ realSpan U c) : realDecomposition b hb x d = 0 :=
  BasisPartition.productEquiv_symm_of_mem_ne _ _ hcd hx

theorem ray_decomposition_zero (u : U) {d : Components U}
    (hd : MatroidComponents.component (represented U) u ≠ d) :
    realDecomposition b hb (embed u.val) d = 0 := by
  apply realDecomposition_of_mem_ne b hb hd
  exact Submodule.subset_span ⟨u, rfl, rfl⟩

end Finite
end Unimodular.ComponentLattice

#print axioms Unimodular.ComponentLattice.uniform_internal
#print axioms Unimodular.ComponentLattice.component_isIntegralLattice
#print axioms Unimodular.ComponentLattice.integralAssembly_apply
#print axioms Unimodular.ComponentLattice.realAssembly_apply
#print axioms Unimodular.ComponentLattice.decomposition_compatible
#print axioms Unimodular.ComponentLattice.ray_decomposition_zero
#check "UNIMODULAR_INTRINSIC_COMPONENT_SUM_EOF_V3"
