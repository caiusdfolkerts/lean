module
public import resolution_existence.part002
public import shared_results.part002
public import shared_results.part003
public import graph_foundation.part010
public import paper_results.part004

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialFineResolution -/
section

/-! # An actual minimal free resolution retaining fine homology labels

The homological projections come from the literal homology basis. They cut
the transferred polynomial differential into a chain complex, whose exactness
comes from the diagonal augmentation and its coefficient-linear contraction.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice.MonomialFineResolution
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial CategoryTheory
open DirectSum HomologicalPerturbation PolynomialModuleResolution
open scoped TensorProduct
attribute [local instance] Classical.propDecidable
section NestedCoordinates
variable {R Q P Γ : Type*} [CommRing R] [DecidableEq Q] [DecidableEq P]
  {H : Q → P → Type*} [∀ q p, AddCommGroup (H q p)] [∀ q p, Module R (H q p)]
  {T : Q → P → Type*}

/-- A complete direct-sum component has the degree assigned to its two
labels. The argument is proved before specializing the component modules. -/
theorem nestedLof_mem_piece (b : ∀ q p, Module.Basis (T q p) R (H q p))
    (g : Q → P → Γ) (q : Q) (p : P) (x : H q p) :
    DirectSum.lof R Q (fun q => ⨁ p, H q p) q
      (DirectSum.lof R P (H q) p x) ∈
        Grading.Piece (FourPapers.nestedDirectSumBasis b)
          (fun a => g a.1 a.2.1) (g q p) := by
  have hx : x ∈ Submodule.span R (Set.range (b q p)) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← FourPapers.nestedDirectSumBasis_apply b ⟨q, p, i⟩]
      exact Grading.basis_mem_piece (R := R) (FourPapers.nestedDirectSumBasis b)
        (fun a => g a.1 a.2.1) ⟨q, p, i⟩
  | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (Submodule.add_mem _ ihx ihy)
  | smul c x hx ih =>
      simpa only [map_smul] using (Submodule.smul_mem _ c ih)

end NestedCoordinates

section HomologyBasisMaps
variable {R M I Γ Δ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Module.Basis I R M) (degree : I → Γ) (homological : I → ℕ)
  (D : Module.End R M) (hD : D.comp D = 0)
  (hlower : ∀ q p x, x ∈ BasisMultigradedContraction.piece b degree homological q (p+1) →
    D x ∈ BasisMultigradedContraction.piece b degree homological q p)
  (hH : ∀ q p, Module.Projective R
    (BasisMultigradedContraction.StrandHomology b degree homological D hD hlower q p))
  {T : Γ → ℕ → Type*}
  (bh : ∀ q p, Module.Basis (T q p) R
    (BasisMultigradedContraction.StrandHomology b degree homological D hD hlower q p))
  (g : Γ × ℕ → Δ)

local notation "H₀" => BasisMultigradedContraction.GradedHomology b degree homological D hD hlower
local notation "C₀" => BasisMultigradedContraction.contraction b degree homological D hD hlower hH

/-- Degreewise representatives retain any regrading of their two labels. -/
theorem contraction_inclusion_basis_degree (a : Σ q, Σ p, T q p) :
    (C₀).inclusion (FourPapers.nestedDirectSumBasis bh a) ∈
      Grading.Piece b (fun i => g (degree i, homological i)) (g (a.1, a.2.1)) := by
  have hb := FourPapers.nestedDirectSumBasis_apply bh a
  have hi := BasisMultigradedContraction.contraction_inclusion_mem
    (R := R) (M := M) (I := I) (Γ := Γ) b degree homological D hD hlower hH
    a.1 a.2.1 (bh a.1 a.2.1 a.2.2)
  have hh := piece_regrade (R := R) (X := M) (I := I) b
    (fun i => (degree i, homological i)) (a.1, a.2.1) g hi
  exact (congrArg (fun x : H₀ => (C₀).inclusion x ∈
    Grading.Piece b (fun i => g (degree i, homological i)) (g (a.1, a.2.1))) hb).mpr hh

/-- The projection lands in the corresponding component of the homology basis. -/
theorem contraction_projection_basis_degree (i : I) :
    (C₀).projection (b i) ∈
      Grading.Piece (FourPapers.nestedDirectSumBasis bh)
        (fun a => g (a.1, a.2.1)) (g (degree i, homological i)) := by
  let x : BasisMultigradedContraction.piece b degree homological (degree i) (homological i) :=
    ⟨b i, Grading.basis_mem_piece (R := R) b (fun i => (degree i, homological i)) i⟩
  have hp := BasisMultigradedContraction.contraction_projection_piece
    (R := R) (M := M) (I := I) (Γ := Γ) b degree homological D hD hlower hH
    (degree i) (homological i) x
  apply (congrArg (fun y : H₀ =>
    y ∈ Grading.Piece (FourPapers.nestedDirectSumBasis bh)
      (fun a => g (a.1, a.2.1)) (g (degree i, homological i))) hp).mpr
  exact nestedLof_mem_piece (R := R) bh (fun q p => g (q,p)) (degree i) (homological i) _

/-- Homological projections commute with the inclusion before any concrete
polynomial ideal is substituted for the coefficient module. -/
theorem contraction_inclusion_projection (p : ℕ) :
    (C₀).inclusion.comp
        (Grading.projection (FourPapers.nestedDirectSumBasis bh) (fun a => a.2.1) p) =
      (Grading.projection b homological p).comp (C₀).inclusion := by
  exact FourPapers.shiftedProjection_commutes
    (FourPapers.nestedDirectSumBasis bh) b (fun a => a.2.1) homological
    id Function.injective_id (C₀).inclusion
    (contraction_inclusion_basis_degree b degree homological D hD hlower hH bh Prod.snd) p

/-- The projection onto literal homology also preserves homological degree. -/
theorem contraction_projection_projection (p : ℕ) :
    (C₀).projection.comp (Grading.projection b homological p) =
      (Grading.projection (FourPapers.nestedDirectSumBasis bh) (fun a => a.2.1) p).comp
        (C₀).projection := by
  exact FourPapers.shiftedProjection_commutes
    b (FourPapers.nestedDirectSumBasis bh) homological (fun a => a.2.1)
    id Function.injective_id (C₀).projection
    (contraction_projection_basis_degree b degree homological D hD hlower hH bh Prod.snd) p

end HomologyBasisMaps

section ChosenHomologyBasisMaps
variable {K M I Γ Δ : Type*} [Field K] [AddCommGroup M] [Module K M]
  (b : Module.Basis I K M) (degree : I → Γ) (homological : I → ℕ)
  (D : Module.End K M) (hD : D.comp D = 0)
  (hlower : ∀ q p x, x ∈ BasisMultigradedContraction.piece b degree homological q (p+1) →
    D x ∈ BasisMultigradedContraction.piece b degree homological q p)
  (g : Γ × ℕ → Δ)

/-- Choosing the field bases while the ambient module is still abstract
avoids changing its quotient-module presentation during specialization. -/
def chosen_inclusion_basis_degree :=
  contraction_inclusion_basis_degree (R := K) (M := M) (I := I) (Γ := Γ)
    b degree homological D hD hlower (fun _ _ => by infer_instance)
    (fun q p => Module.Free.chooseBasis K
      (BasisMultigradedContraction.StrandHomology b degree homological D hD hlower q p)) g

def chosen_projection_basis_degree :=
  contraction_projection_basis_degree (R := K) (M := M) (I := I) (Γ := Γ)
    b degree homological D hD hlower (fun _ _ => by infer_instance)
    (fun q p => Module.Free.chooseBasis K
      (BasisMultigradedContraction.StrandHomology b degree homological D hD hlower q p)) g

def chosen_inclusion_projection :=
  contraction_inclusion_projection (R := K) (M := M) (I := I) (Γ := Γ)
    b degree homological D hD hlower (fun _ _ => by infer_instance)
    (fun q p => Module.Free.chooseBasis K
      (BasisMultigradedContraction.StrandHomology b degree homological D hD hlower q p))

def chosen_projection_projection :=
  contraction_projection_projection (R := K) (M := M) (I := I) (Γ := Γ)
    b degree homological D hD hlower (fun _ _ => by infer_instance)
    (fun q p => Module.Free.chooseBasis K
      (BasisMultigradedContraction.StrandHomology b degree homological D hD hlower q p))

end ChosenHomologyBasisMaps

section BaseChangedProjection
variable {K A H I Γ : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup H] [Module K H]

/-- Homogeneous projection commutes with scalar extension. Proving this
before specializing the quotient module avoids repeated kernel conversion
of its concrete nested-direct-sum presentation. -/
theorem baseChangedBasis_projection (b : Module.Basis I K H) (degree : I → Γ) (q : Γ) :
    Grading.projection (b.baseChange A) degree q = (Grading.projection b degree q).baseChange A := by
  apply (b.baseChange A).ext
  intro i
  rw [Grading.projection_basis]
  simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Grading.projection_basis]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

end BaseChangedProjection

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V] (B : Family V)
local notation "S" => MvPolynomial V K
local notation "M" => monomialIdeal K B
local notation "C" => contraction (K := K) B

-- Keep the chosen basis as a named object during instance inference.
attribute [local irreducible] freeBasis

abbrev homologyLof (α : Exponent V) (p : ℕ) : Strand (K := K) B α p →ₗ[K] Homology (K := K) B :=
  (DirectSum.lof K (Exponent V) (fun α => ⨁ p,Strand (K := K) B α p) α).comp
    (DirectSum.lof K ℕ (Strand (K := K) B α) p)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 50000 in
/-- The generic coordinate formula specialized to the actual strand basis.
Its inferred statement keeps the already chosen module structures shared. -/
def homologyBasis_lof :=
  FourPapers.nestedDirectSumBasis_apply (R := K) (chooseBasisFamily (K := K) B)

/-- The actual homology component lies in its homological-degree piece. -/
def homologyLof_mem :=
  nestedLof_mem_piece (R := K) (chooseBasisFamily (K := K) B)
    (fun (_α : Exponent V) (p : ℕ) => p)

def tensorProjection (p : ℕ) : Module.End K (M ⊗[K] Simplicial.Ambient V K) :=
  Grading.projection (tensorBasis (K := K) B) (homological B) p

def homologyProjection (p : ℕ) : Module.End K (Homology (K := K) B) :=
  Grading.projection (homologyBasis (K := K) B) (fun a => a.2.1) p

set_option backward.isDefEq.respectTransparency true in
theorem homotopy_basis_mem (a : Index B) :
    (contraction (K := K) B).h (tensorBasis (K := K) B a)∈Grading.Piece (tensorBasis (K := K) B) (homological B) (homological B a+1) := by
  have hle : Grading.Piece (tensorBasis (K := K) B)
      (fun i : Index B => (fineDegree B i, homological B i))
      (fineDegree B a, homological B a+1) ≤
      Grading.Piece (tensorBasis (K := K) B) (homological B) (homological B a+1) := by
    apply Submodule.span_mono
    apply Set.image_mono
    intro i hi
    exact congrArg (Prod.snd : Exponent V × ℕ → ℕ) hi
  exact hle (contraction_h_fine (K := K) B (fineDegree B a) (homological B a)
    ⟨tensorBasis (K := K) B a, Grading.basis_mem_piece (R := K) (tensorBasis (K := K) B)
      (fun i => (fineDegree B i, homological B i)) a⟩)

set_option backward.isDefEq.respectTransparency true in
/-- The actual inclusion and projection retain homological degree. -/
def inclusion_basis_mem :=
  chosen_inclusion_basis_degree (K := K) («M» := TensorModule (K := K) B)
    (I := Index B) (Γ := Exponent V)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B) Prod.snd

set_option backward.isDefEq.respectTransparency true in
def projection_basis_mem :=
  chosen_projection_basis_degree (K := K) («M» := TensorModule (K := K) B)
    (I := Index B) (Γ := Exponent V)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B) Prod.snd

set_option backward.isDefEq.respectTransparency true in
theorem h_projection (p : ℕ) : (contraction (K := K) B).h*tensorProjection (K := K) B p=tensorProjection (K := K) B (p+1)*(contraction (K := K) B).h := by
  apply (tensorBasis (K := K) B).ext
  intro a
  change (contraction (K := K) B).h
      (Grading.projection (tensorBasis (K := K) B) (homological B) p
        (tensorBasis (K := K) B a)) =
    Grading.projection (tensorBasis (K := K) B) (homological B) (p+1)
      ((contraction (K := K) B).h (tensorBasis (K := K) B a))
  rw [Grading.projection_basis]
  by_cases ha : homological B a = p
  · rw [if_pos ha, ← ha]
    exact (Grading.projection_eq_self (homotopy_basis_mem (K := K) B a)).symm
  · rw [if_neg ha, map_zero]
    exact (Grading.projection_eq_zero
      (show p+1 ≠ homological B a+1 from fun h => ha (Nat.add_right_cancel h).symm)
      (homotopy_basis_mem (K := K) B a)).symm

theorem h_projection_zero : tensorProjection (K := K) B 0*(contraction (K := K) B).h=0 := by
  apply (tensorBasis (K := K) B).ext
  intro a
  exact Grading.projection_eq_zero (by omega) (homotopy_basis_mem (K := K) B a)

set_option backward.isDefEq.respectTransparency true in
/-- Specialize the abstract projection identity before reducing the concrete
homology module. Its inferred type is the exact commuting-map equality. -/
def inclusion_projection :=
  chosen_inclusion_projection (K := K) («M» := TensorModule (K := K) B)
    (I := Index B) (Γ := Exponent V)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B)

set_option backward.isDefEq.respectTransparency true in
def projection_projection :=
  chosen_projection_projection (K := K) («M» := TensorModule (K := K) B)
    (I := Index B) (Γ := Exponent V)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B)

theorem removeExterior_basis (v : V) (a : Index B) :
    removeExterior M v (tensorBasis (K := K) B a)=
      if v∈a.2 then TauCeti.ExteriorAlgebra.basisEraseSign v a.2 •
        tensorBasis (K := K) B (a.1,a.2.erase v) else 0 := by
  simp only [removeExterior,tensorBasis,Module.Basis.tensorProduct_apply',TensorProduct.map_tmul,
    LinearMap.id_apply,Simplicial.contraction_basis]
  by_cases hv : v ∈ a.2
  · simp only [if_pos hv, TensorProduct.tmul_smul]
    have he : @Finset.erase V (fun a b => LinearOrder.toDecidableEq a b) a.2 v =
        a.2.erase v := by
      ext w
      simp only [Finset.mem_erase]
    rw [he]
  · simp only [if_neg hv, TensorProduct.tmul_zero]

set_option backward.isDefEq.respectTransparency true in
theorem removeExterior_mem (v : V) (a : Index B) :
    removeExterior M v (tensorBasis (K := K) B a)∈
      Grading.Piece (tensorBasis (K := K) B) (homological B) (homological B a-1) := by
  rw [removeExterior_basis (K := K) B v a]
  split_ifs with hv
  · have hb := Grading.basis_mem_piece (R := K) (tensorBasis (K := K) B)
      (homological B) (a.1,a.2.erase v)
    have hb' : tensorBasis (K := K) B (a.1,a.2.erase v) ∈
        Grading.Piece (tensorBasis (K := K) B) (homological B) (homological B a-1) := by
      simpa only [homological, Finset.card_erase_of_mem hv] using hb
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K]
    exact Submodule.smul_mem _ _ hb'
  · exact Submodule.zero_mem _

theorem removeExterior_zero (v : V) (a : Index B) (ha : homological B a=0) :
    removeExterior M v (tensorBasis (K := K) B a)=0 := by
  rw [removeExterior_basis (K := K) B v a,show a.2=∅ from Finset.card_eq_zero.mp ha]
  simp only [Finset.notMem_empty,if_false]

theorem removeExterior_projection (v : V) (p : ℕ) :
    removeExterior M v*tensorProjection (K := K) B (p+1)=tensorProjection (K := K) B p*removeExterior M v := by
  have h := homogeneous_projection_lowering (R := K)
    («M» := TensorModule (K := K) B) (I := Index B) (tensorBasis (K := K) B) (homological B) (removeExterior M v)
    (removeExterior_mem (K := K) B v) (removeExterior_zero (K := K) B v) p
  exact h

theorem removeExterior_projection_zero (v : V) : removeExterior M v*tensorProjection (K := K) B 0=0 := by
  apply (tensorBasis (K := K) B).ext
  intro a
  simp only [Module.End.mul_apply,LinearMap.zero_apply,tensorProjection,Grading.projection_basis]
  split_ifs with ha
  · exact removeExterior_zero (K := K) B v a ha
  · exact map_zero _

def barProjection (p : ℕ) : Module.End S (Bar (R := K) (V := V) M) :=
  (tensorProjection (K := K) B p).baseChange S

def freeProjection (p : ℕ) : Module.End S (S ⊗[K] Homology (K := K) B) :=
  (homologyProjection (K := K) B p).baseChange S

/-- The generic scalar-extension identity specialized to the actual
homology basis; its inferred proof type retains the shared instances. -/
def freeBasis_projection :=
  baseChangedBasis_projection (A := S) (homologyBasis (K := K) B)
    (fun a => a.2.1)

set_option backward.isDefEq.respectTransparency true in
/-- The same scalar-extension identity in the named resolution coordinates. -/
theorem freeBasis_projection_eq (p : ℕ) :
    ProjectedFreeResolution.projection (freeBasis (K := K) B) (fun a => a.2.1) p =
      freeProjection (K := K) B p := by
  simpa only [ProjectedFreeResolution.projection, freeBasis, freeProjection,
    homologyProjection] using! (freeBasis_projection (K := K) B p)

abbrev extended := PolynomialPerturbation.extendedContraction M C

set_option backward.isDefEq.respectTransparency true in
theorem extended_h_projection (p : ℕ) :
    (extended (K := K) B).h*barProjection (K := K) B p=barProjection (K := K) B (p+1)*(extended (K := K) B).h := by
  change -((contraction (K := K) B).h.baseChange S)*(tensorProjection (K := K) B p).baseChange S=
    (tensorProjection (K := K) B (p+1)).baseChange S* -((contraction (K := K) B).h.baseChange S)
  change (-((contraction (K := K) B).h.baseChange S)).comp
    ((tensorProjection (K := K) B p).baseChange S) =
    ((tensorProjection (K := K) B (p+1)).baseChange S).comp
      (-((contraction (K := K) B).h.baseChange S))
  rw [LinearMap.neg_comp, LinearMap.comp_neg, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp]
  exact congrArg (fun t : Module.End K (TensorModule (K := K) B) => -(t.baseChange S))
    (h_projection (K := K) B p)

set_option backward.isDefEq.respectTransparency true in
theorem extended_h_projection_zero : barProjection (K := K) B 0*(extended (K := K) B).h=0 := by
  change (tensorProjection (K := K) B 0).baseChange S* -((contraction (K := K) B).h.baseChange S)=0
  change ((tensorProjection (K := K) B 0).baseChange S).comp
    (-((contraction (K := K) B).h.baseChange S)) = 0
  rw [LinearMap.comp_neg, ← LinearMap.baseChange_comp]
  change -((tensorProjection (K := K) B 0 * (contraction (K := K) B).h).baseChange S) = 0
  rw [h_projection_zero (K := K) B, LinearMap.baseChange_zero]
  exact neg_zero (G := Module.End S (Bar (R := K) (V := V) M))

theorem extended_inclusion_projection (p : ℕ) :
    (extended (K := K) B).inclusion.comp (freeProjection (K := K) B p)=
      (barProjection (K := K) B p).comp (extended (K := K) B).inclusion := by
  change ((contraction (K := K) B).inclusion.baseChange S).comp ((homologyProjection (K := K) B p).baseChange S)=
    ((tensorProjection (K := K) B p).baseChange S).comp ((contraction (K := K) B).inclusion.baseChange S)
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  apply congrArg (fun g : Homology (K := K) B →ₗ[K] TensorModule (K := K) B =>
    g.baseChange S)
  simpa only [contraction, homologyProjection, tensorProjection, homologyBasis,
    chooseBasisFamily] using! (inclusion_projection (K := K) B p)

theorem extended_projection_projection (p : ℕ) :
    (extended (K := K) B).projection.comp (barProjection (K := K) B p)=
      (freeProjection (K := K) B p).comp (extended (K := K) B).projection := by
  change ((contraction (K := K) B).projection.baseChange S).comp ((tensorProjection (K := K) B p).baseChange S)=
    ((homologyProjection (K := K) B p).baseChange S).comp ((contraction (K := K) B).projection.baseChange S)
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
  apply congrArg (fun g : TensorModule (K := K) B →ₗ[K] Homology (K := K) B =>
    g.baseChange S)
  simpa only [contraction, homologyProjection, tensorProjection, homologyBasis,
    chooseBasisFamily] using! (projection_projection (K := K) B p)

theorem external_projection (p : ℕ) :
    externalDifferential M*barProjection (K := K) B (p+1)=barProjection (K := K) B p*externalDifferential M := by
  rw [externalDifferential,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [smul_mul_assoc,mul_smul_comm]
  congr 1
  change (removeExterior M v).baseChange S*(tensorProjection (K := K) B (p+1)).baseChange S=
    (tensorProjection (K := K) B p).baseChange S*(removeExterior M v).baseChange S
  rw [←LinearMap.baseChange_mul,←LinearMap.baseChange_mul,removeExterior_projection (K := K) B v p]

theorem external_projection_zero : externalDifferential M*barProjection (K := K) B 0=0 := by
  rw [externalDifferential,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro v hv
  rw [smul_mul_assoc]
  change (X v : S) • ((removeExterior M v).baseChange S*(tensorProjection (K := K) B 0).baseChange S)=0
  rw [←LinearMap.baseChange_mul,removeExterior_projection_zero (K := K) B v,LinearMap.baseChange_zero,smul_zero]

abbrev perturbationUnit := (extended (K := K) B).leftPerturbationUnit
  ((PolynomialPerturbation.tensorBasis (R := K) (V := V) M
    (monomialBasis (k := K) B)).baseChange S)
  (PolynomialPerturbation.internalDegree (fun a : {a : Exponent V // Contains B a} => a.val.degree))
  (externalDifferential M) (PolynomialPerturbation.externalDifferential_decreases M (monomialBasis B)
    (fun a => a.val.degree)) (((contraction_h_nonincreasing (K := K) B).baseChange S).neg)

theorem freeModel_lowers (p : ℕ) :
    (freeModel (K := K) B).targetD.comp (freeProjection (K := K) B (p+1))=
      (freeProjection (K := K) B p).comp (freeModel (K := K) B).targetD :=
  (extended (K := K) B).transferredDifferential_lowers_degree (barProjection (K := K) B) (freeProjection (K := K) B)
    (externalDifferential M) (perturbationUnit (K := K) B) (LinearContraction.leftPerturbationUnit_val ..)
    (extended_h_projection (K := K) B) (external_projection (K := K) B) (extended_inclusion_projection (K := K) B)
    (extended_projection_projection (K := K) B) p

theorem freeModel_zero : (freeModel (K := K) B).targetD.comp (freeProjection (K := K) B 0)=0 :=
  (extended (K := K) B).transferredDifferential_zero_degree (barProjection (K := K) B) (freeProjection (K := K) B)
    (externalDifferential M) (perturbationUnit (K := K) B) (external_projection_zero (K := K) B)
    (extended_inclusion_projection (K := K) B)

theorem freeModel_inclusion_projection (p : ℕ) :
    (freeModel (K := K) B).inclusion.comp (freeProjection (K := K) B p)=
      (barProjection (K := K) B p).comp (freeModel (K := K) B).inclusion :=
  (extended (K := K) B).transferredInclusion_preserves_degree (barProjection (K := K) B) (freeProjection (K := K) B)
    (externalDifferential M) (perturbationUnit (K := K) B) (LinearContraction.leftPerturbationUnit_val ..)
    (extended_h_projection (K := K) B) (extended_h_projection_zero (K := K) B) (external_projection (K := K) B)
    (external_projection_zero (K := K) B) (extended_inclusion_projection (K := K) B) p

def augmentation : (S ⊗[K] Homology (K := K) B) →ₗ[S] M :=
  PolynomialPerturbation.augmentation M C (contraction_d (K := K) B) (monomialBasis B)
    (fun a => a.val.degree) (contraction_h_nonincreasing (K := K) B)

abbrev splitAugmentation :=
  PolynomialPerturbation.splitAugmentation M C (contraction_d (K := K) B) (monomialBasis B)
    (fun a => a.val.degree) (contraction_h_nonincreasing (K := K) B)

theorem barAugmentation_projection_zero :
    (PolynomialModuleResolution.augmentation M).comp (barProjection (K := K) B 0)=
      PolynomialModuleResolution.augmentation M := by
  apply ((tensorBasis (K := K) B).baseChange S).ext
  rintro ⟨a,F⟩
  simp only [LinearMap.comp_apply,Module.Basis.baseChange_apply,barProjection,
    LinearMap.baseChange_tmul,tensorProjection,Grading.projection_basis,homological]
  by_cases h : F.card=0
  · rw [if_pos h]
  · rw [if_neg h,TensorProduct.tmul_zero,map_zero]
    rw [tensorBasis_apply,PolynomialModuleResolution.augmentation_tmul_basis,
      if_neg (show F ≠ ∅ from fun he => h (Finset.card_eq_zero.mpr he))]

theorem augmentation_projection_zero : (augmentation (K := K) B).comp (freeProjection (K := K) B 0)=augmentation (K := K) B := by
  change ((PolynomialModuleResolution.augmentation M).comp (freeModel (K := K) B).inclusion).comp _=_
  rw [LinearMap.comp_assoc,freeModel_inclusion_projection (K := K) B 0,←LinearMap.comp_assoc,
    barAugmentation_projection_zero (K := K) B]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Transport the actual lowering equation to the named free-basis
projections before supplying it to the resolution constructor. -/
def freeModel_basis_lowers (p : ℕ) :=
  ((congrArg
    (fun P : Module.End S (S ⊗[K] Homology (K := K) B) =>
      (freeModel (K := K) B).targetD.comp P)
    (freeBasis_projection_eq (K := K) B (p+1))).trans
      (freeModel_lowers (K := K) B p)).trans
        (congrArg
          (fun P : Module.End S (S ⊗[K] Homology (K := K) B) =>
            P.comp (freeModel (K := K) B).targetD)
          (freeBasis_projection_eq (K := K) B p).symm)

set_option backward.isDefEq.respectTransparency true in
def freeModel_basis_zero :=
  (congrArg
    (fun P : Module.End S (S ⊗[K] Homology (K := K) B) =>
      (freeModel (K := K) B).targetD.comp P)
    (freeBasis_projection_eq (K := K) B 0)).trans (freeModel_zero (K := K) B)

set_option backward.isDefEq.respectTransparency true in
def augmentation_basis_zero :=
  (congrArg
    (fun P : Module.End S (S ⊗[K] Homology (K := K) B) =>
      (augmentation (K := K) B).comp P)
    (freeBasis_projection_eq (K := K) B 0)).trans (augmentation_projection_zero (K := K) B)

set_option backward.isDefEq.respectTransparency true in
/-- The source is an actual augmented free resolution of the literal
monomial ideal. Its free generators retain their fine homology labels. -/
def resolution : ProjectiveResolution (ModuleCat.of S M) :=
  ProjectedFreeResolution.resolution (R := K) («S» := MvPolynomial V K)
    (F := (MvPolynomial V K) ⊗[K] Homology (K := K) B)
    («M» := ↥(monomialIdeal K B)) (I := HomologyIndex (K := K) B)
    (freeBasis (K := K) B) (fun a => a.2.1)
    (freeModel (K := K) B).targetD (augmentation (K := K) B) (splitAugmentation (K := K) B) rfl
    (PolynomialPerturbation.splitAugmentation_projection M C (contraction_d (K := K) B)
      (monomialBasis B) (fun a => a.val.degree) (contraction_h_nonincreasing (K := K) B)) rfl
    (freeModel_basis_lowers (K := K) B) (freeModel_basis_zero (K := K) B)
    (augmentation_basis_zero (K := K) B)

end FourPapers.Sublattice.MonomialFineResolution

end
end
end

end
