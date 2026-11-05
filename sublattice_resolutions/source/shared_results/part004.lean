module
public import graph_foundation.part008
public import shared_results.part003

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientCategoricalHomology -/
section

/-! # Categorical homology and the explicit degree-wise quotient

The first comparison applies to every complex defined by homogeneous
submodules. The quotient Koszul specialization then identifies categorical
homology with the literal degree-wise cycle/boundary quotient, including
homological degree zero.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u v

section ComplexComparison
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (C : FourPapers.SubmoduleComplexData R M)

abbrev submoduleDegreeShortComplex (p : ℕ) : ShortComplex (ModuleCat.{v} R) :=
  C.complex.sc' (p+1) p p.pred

def submoduleComplexCyclesEquiv (p : ℕ) :
    LinearMap.ker (submoduleDegreeShortComplex C p).g.hom ≃ₗ[R]
      FourPapers.ProjectiveComplexSplitting.cycles (fun i => ↥(C.piece i))
        C.differential p where
  toFun x := ⟨x.val, by
    cases p with
    | zero => trivial
    | succ p =>
        change C.differential p x.val = 0
        apply Subtype.ext
        have hx := x.property
        change (C.complex.d (p+1) p).hom x.val = 0 at hx
        rw [FourPapers.SubmoduleComplexData.complex_d] at hx
        exact congrArg Subtype.val hx⟩
  invFun x := ⟨x.val, by
    cases p with
    | zero =>
        change (C.complex.d 0 0).hom x.val = 0
        rw [C.complex.shape 0 0 (by simp)]
        rfl
    | succ p =>
        change (C.complex.d (p+1) p).hom x.val = 0
        rw [FourPapers.SubmoduleComplexData.complex_d]
        exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma submoduleComplexCyclesEquiv_val (p : ℕ)
    (x : LinearMap.ker (submoduleDegreeShortComplex C p).g.hom) :
    (submoduleComplexCyclesEquiv C p x).val = x.val := rfl

lemma submoduleComplexCyclesEquiv_boundaries (p : ℕ) :
    (LinearMap.range (submoduleDegreeShortComplex C p).moduleCatToCycles).map
      (submoduleComplexCyclesEquiv C p).toLinearMap =
    FourPapers.ProjectiveComplexSplitting.boundaries (fun i => ↥(C.piece i)) C.differential
      C.differential_comp p := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change C.differential p y = (C.complex.d (p+1) p).hom y
    rw [FourPapers.SubmoduleComplexData.complex_d, ModuleCat.hom_ofHom]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(submoduleDegreeShortComplex C p).moduleCatToCycles y, ⟨y, rfl⟩, ?_⟩
    apply Subtype.ext
    change (C.complex.d (p+1) p).hom y = C.differential p y
    rw [FourPapers.SubmoduleComplexData.complex_d, ModuleCat.hom_ofHom]
    rfl

/-- The degree-zero kernel is the full chain group because its actual
outgoing differential is zero; the positive-degree kernels are unchanged. -/
def submoduleComplexHomologyEquiv (p : ℕ) :
    C.complex.homology p ≃ₗ[R]
      FourPapers.ProjectiveComplexSplitting.Homology (fun i => ↥(C.piece i)) C.differential
        C.differential_comp p :=
  ((C.complex.homologyIsoSc' (p+1) p p.pred (by simp) (by cases p <;> simp)) ≪≫
    (submoduleDegreeShortComplex C p).moduleCatHomologyIso).toLinearEquiv.trans
      (Submodule.Quotient.equiv _ _ (submoduleComplexCyclesEquiv C p)
        (submoduleComplexCyclesEquiv_boundaries C p))

end ComplexComparison

variable {k V : Type u} [CommRing k] [Fintype V] [LinearOrder V]

/-- Exact agreement between categorical fine Koszul homology and the
degree-wise quotient used in the integral graph recursion. -/
def quotientCategoricalDegreeHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B α).homology p ≃ₗ[k]
      ClosedGraphDegreeHomology (k := k) B α p :=
  (((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) p).mapIso
      (quotientTotalKoszulIso (k := k) B α).symm).toLinearEquiv.trans
        (submoduleComplexHomologyEquiv (quotientTotalData (k := k) B α) p)).trans
          (quotientPieceHomologyEquiv (k := k) B α p)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientDegreeHomologyInjection -/
section

/-! # Homogeneous homology embeds in total fine homology

These actual inclusion and projection maps are used by the graph integral
freeness and support arguments.  The quotient carriers used by the separate
Theorem 8.1 detector are defined in QuotientDegreeHomology.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

local instance closedGraphTotalCyclesAddCommGroup (B : Family V) (α : Exponent V) :
    AddCommGroup (LinearMap.ker (quotientTotalDifferential (k := k) B α)) :=
  Submodule.addCommGroup (R := k)
    (M := TotalFaceModule (k := k) (quotientKoszulFaces B α)) _

local instance closedGraphTotalCyclesModule (B : Family V) (α : Exponent V) :
    Module k (LinearMap.ker (quotientTotalDifferential (k := k) B α)) :=
  Submodule.module (R := k)
    (M := TotalFaceModule (k := k) (quotientKoszulFaces B α)) _

attribute [local irreducible] ClosedGraphDegreeHomology ClosedGraphFaceHomology

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
def closedGraphDegreeHomologyInclusion (B : Family V) (α : Exponent V) (p : ℕ) :
    @LinearMap k k inferInstance inferInstance (RingHom.id k)
      (ClosedGraphDegreeHomology (k := k) B α p) (ClosedGraphFaceHomology (k := k) B α)
      (closedGraphDegreeHomologyAddCommGroup (k := k) B α p).toAddCommMonoid
      (closedGraphFaceHomologyAddCommGroup (k := k) B α).toAddCommMonoid
      (closedGraphDegreeHomologyModule (k := k) B α p)
      (closedGraphFaceHomologyModule (k := k) B α) := by
  unfold ClosedGraphDegreeHomology ClosedGraphFaceHomology
  exact submoduleHomologyMap (K := k) (M := Simplicial.Ambient V k)
    (TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (quotientTotalDifferential (k := k) B α)
    (quotientTotalDifferential_comp (k := k) B α)
    (totalFacePiece (k := k) (quotientKoszulFaces B α) (p + 1))
    (ClosedGraphDegreeCycles (k := k) B α p)
    (closedGraphDegreeBoundary (k := k) B α p)
    (show ClosedGraphDegreeCycles (k := k) B α p ≤
      LinearMap.ker (quotientTotalDifferential (k := k) B α) from inf_le_left)
    (fun _ => rfl)

lemma quotientTotalDifferential_degree_projection (B : Family V) (α : Exponent V) (p : ℕ) :
    (quotientTotalDifferential (k := k) B α).comp
      (Grading.projection (totalFaceBasis (quotientKoszulFaces B α)) (fun F => F.val.card) (p + 1)) =
      (Grading.projection (totalFaceBasis (quotientKoszulFaces B α)) (fun F => F.val.card) p).comp
        (quotientTotalDifferential B α) := by
  let Q := quotientKoszulFaces B α
  let b := totalFaceBasis (k := k) Q
  let deg := fun F : {F // Q F} => F.val.card
  let D := quotientTotalDifferential (k := k) B α
  have hpiece : ∀ i, totalFacePiece (k := k) Q i = Grading.Piece b deg i :=
    fun i => totalFacePiece_eq_basis_span Q i
  have hb : ∀ F, b F ∈ totalFacePiece (k := k) Q (deg F) := by
    intro F
    rw [hpiece]
    exact Grading.basis_mem_piece b deg F
  have hzero : ∀ F, deg F = 0 → D (b F) = 0 := by
    intro F hF
    exact quotientTotalDifferential_zero_degree B α (b F) (hF ▸ hb F)
  have hlower : ∀ F, D (b F) ∈ Grading.Piece b deg (deg F - 1) := by
    intro F
    by_cases hF : deg F = 0
    · rw [hzero F hF]
      exact Submodule.zero_mem _
    · obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hF
      rw [hq, Nat.succ_sub_one, ← hpiece]
      exact quotientTotalDifferential_lowers B α q (b F)
        (by simpa only [hq, Nat.succ_eq_add_one] using hb F)
  exact homogeneous_projection_lowering b deg D hlower hzero p

/-- A homogeneous cycle that bounds in the total strand has a homogeneous
filling one degree higher. This proves injectivity of the degree-p homology
inclusion, including p=0. -/
theorem closedGraphDegreeHomologyInclusion_injective (B : Family V) (α : Exponent V) (p : ℕ) :
    Function.Injective (closedGraphDegreeHomologyInclusion (k := k) B α p) := by
  unfold closedGraphDegreeHomologyInclusion ClosedGraphDegreeHomology ClosedGraphFaceHomology
  dsimp only [id_eq]
  apply submoduleHomologyMap_injective
  intro z hz
  obtain ⟨a, ha0⟩ := hz
  let D := quotientTotalDifferential (k := k) B α
  let b := totalFaceBasis (k := k) (quotientKoszulFaces B α)
  let deg := fun F : {F // quotientKoszulFaces B α F} => F.val.card
  let a' := Grading.projection b deg (p + 1) a
  have ha' : a' ∈ totalFacePiece (quotientKoszulFaces B α) (p + 1) := by
    rw [totalFacePiece_eq_basis_span]
    exact Grading.projection_mem b deg (p + 1) a
  have hfill : D a' = z.val := by
    have hc := LinearMap.congr_fun (quotientTotalDifferential_degree_projection B α p) a
    change D a' = Grading.projection b deg p (D a) at hc
    rw [hc, ha0]
    apply Grading.projection_eq_self
    change z.val ∈ Grading.Piece
      (totalFaceBasis (k := k) (quotientKoszulFaces B α)) (fun F => F.val.card) p
    unfold Grading.Piece
    rw [← totalFacePiece_eq_basis_span]
    exact z.property.2
  exact ⟨⟨a', ha'⟩, Subtype.ext hfill⟩

section Integral
variable {W : Type} [Fintype W] [LinearOrder W]

/-- Fine total freeness implies freeness in each homological degree over the
integers. Finite generation comes from the finite face basis, and the proved
injection excludes torsion before the PID basis theorem is applied. -/
theorem closedGraphDegreeHomology_free_of_total (B : Family W) (α : Exponent W) (p : ℕ)
    (hfree : Module.Free ℤ (ClosedGraphFaceHomology (k := ℤ) B α)) :
    Module.Free ℤ (ClosedGraphDegreeHomology (k := ℤ) B α p) := by
  letI : Module.Free ℤ (ClosedGraphFaceHomology (k := ℤ) B α) := hfree
  letI : Module.Finite ℤ (TotalFaceModule (k := ℤ) (quotientKoszulFaces B α)) :=
    Module.Finite.of_basis (totalFaceBasis (k := ℤ) (quotientKoszulFaces B α))
  letI : Module.Finite ℤ (ClosedGraphDegreeHomology (k := ℤ) B α p) := by
    unfold ClosedGraphDegreeHomology
    infer_instance
  letI : Module.IsTorsionFree ℤ (ClosedGraphDegreeHomology (k := ℤ) B α p) :=
    Function.Injective.moduleIsTorsionFree (closedGraphDegreeHomologyInclusion B α p)
      (closedGraphDegreeHomologyInclusion_injective B α p)
      (fun r x => by
        simpa only [int_smul_eq_zsmul, LinearMap.toAddMonoidHom_coe] using
          (closedGraphDegreeHomologyInclusion (k := ℤ) B α p).toAddMonoidHom.map_zsmul r x)
  infer_instance

end Integral
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ProductGeometryPrelude -/
section

/- Exact tensor, exterior-product and normal-form weight dependencies for the
all-powers comparison.  Principal statements are assembled separately. -/

#print axioms FourPapers.Sublattice.finiteFaceTensorEquiv_actual_product
#print axioms FourPapers.Sublattice.crossingBlockTensorEquiv_is_chain
#print axioms FourPapers.Sublattice.idealPowerFaceMul_is_chain
#print axioms FourPapers.Sublattice.orderedProduct_weight_control

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ProductGeometryExtension -/
section

/-!
# Compatibility imports for the recovered ProductGeometryExtension development

The mathematical proofs live in their original modular sources. The saved
source comparison records the unchanged proof bodies and the independent
variable-universe generality retained by those original modules.
-/

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FaceTensorCycleSpanning -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Ring
variable [CommRing k]

lemma faceProjection_involute (P : Finset V → Prop) (x : Simplicial.Ambient V k) :
    faceProjection P (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (faceProjection P x) := by
  have hm : (faceProjection (k := k) P).comp CliffordAlgebra.involute.toLinearMap =
      CliffordAlgebra.involute.toLinearMap.comp (faceProjection P) := by
    apply Simplicial.basis.ext
    intro F
    change faceProjection P (CliffordAlgebra.involute (Simplicial.basis F)) =
      CliffordAlgebra.involute (faceProjection P (Simplicial.basis F))
    have hb : CliffordAlgebra.involute (Simplicial.basis (k := k) F) =
        (-1 : k)^F.card • Simplicial.basis F :=
      TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k V) F
    rw [hb, map_smul, faceProjection_basis]
    split_ifs <;> simp [hb]
  exact LinearMap.congr_fun hm x

lemma totalFaceInvolute_square (P : Finset V → Prop) :
    totalFaceInvolute (k := k) P * totalFaceInvolute P = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact CliffordAlgebra.involute_involute x.val

lemma totalFaceInvolute_eq_one_of_two_eq_zero (P : Finset V → Prop)
    (hchar : (2 : k) = 0) : totalFaceInvolute (k := k) P = 1 := by
  have htwo : (1 : k) + 1 = 0 := by simpa only [one_add_one_eq_two] using hchar
  have hn : (-1 : k) = 1 := by
    calc (-1 : k) = -1 + ((1 : k) + 1) := by rw [htwo, add_zero]
      _ = 1 := by abel
  apply (totalFaceBasis P).ext
  intro F
  apply Subtype.ext
  change CliffordAlgebra.involute ((totalFaceBasis (k := k) P F).val) =
    (totalFaceBasis P F).val
  rw [totalFaceBasis_val, Simplicial.basis, TauCeti.ExteriorAlgebra.involute_basis]
  simp [hn]

lemma projectedTotalDifferential_anticommute (P : Finset V → Prop) :
    projectedTotalDifferential (k := k) P * totalFaceInvolute P =
      -(totalFaceInvolute P * projectedTotalDifferential P) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change faceProjection P (Simplicial.boundary (CliffordAlgebra.involute x.val)) =
    -CliffordAlgebra.involute (faceProjection P (Simplicial.boundary x.val))
  have hi : CliffordAlgebra.involute (Simplicial.boundary x.val) =
      -Simplicial.boundary (CliffordAlgebra.involute x.val) :=
    CliffordAlgebra.involute_contractLeft _ _
  calc faceProjection P (Simplicial.boundary (CliffordAlgebra.involute x.val)) =
      faceProjection P (-CliffordAlgebra.involute (Simplicial.boundary x.val)) := by
        rw [hi, neg_neg]
    _ = _ := by rw [map_neg, faceProjection_involute]

lemma faceProjection_preserves_degree (P Q : Finset V → Prop) (j : ℕ)
    {x : Simplicial.Ambient V k} (hx : x ∈ Simplicial.Chains Q j) :
    faceProjection P x ∈ Simplicial.Chains P j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, ⟨hF, hcard⟩, rfl⟩ := hx
    rw [faceProjection_basis]
    split_ifs with h
    · exact Simplicial.basis_mem h hcard
    · exact Submodule.zero_mem _
  | zero => simpa using Submodule.zero_mem (Simplicial.Chains (k := k) P j)
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma projectedTotalDifferential_zero_piece (P : Finset V → Prop)
    (x : TotalFaceModule (k := k) P) (hx : x ∈ totalFacePiece P 0) :
    projectedTotalDifferential P x = 0 := by
  apply Subtype.ext
  change faceProjection P (Simplicial.boundary x.val) = 0
  have hz : Simplicial.boundary x.val = 0 :=
    Simplicial.boundary_zero_degree_zero
      (show x.val ∈ Simplicial.Chains (k := k) P 0 from hx)
  rw [hz, map_zero]

lemma projectedTotalDifferential_lowers_piece (P : Finset V → Prop) (j : ℕ)
    (x : TotalFaceModule (k := k) P) (hx : x ∈ totalFacePiece P (j + 1)) :
    projectedTotalDifferential P x ∈ totalFacePiece P j := by
  change faceProjection P (Simplicial.boundary x.val) ∈ Simplicial.Chains P j
  apply faceProjection_preserves_degree P (fun _ => True) j
  apply Simplicial.boundary_mem (fun _ _ _ _ => trivial)
  exact Simplicial.chains_mono (fun _ _ => trivial) (j + 1)
    (show x.val ∈ Simplicial.Chains P (j + 1) from hx)

lemma tensorDegreePiece_eq_facePiece (P : Finset V → Prop) (j : ℕ) :
    TensorCycleSpanning.degreePiece (totalFaceBasis (k := k) P) (fun s => s.val.card) j =
      totalFacePiece P j := (totalFacePiece_eq_basis_span P j).symm

end Ring

variable [Field k]

/-- The actual signed exterior face tensor complex has its cycles spanned modulo
boundaries by literal pure tensors of cycles. Its parity conditions, including
characteristic two, are proved here rather than assumed. The square-zero premise
only states that the indicated projected face modules are chain complexes. -/
theorem finiteFaceTensorCycles {m : ℕ} (P : Fin m → Finset V → Prop)
    (hdd : ∀ p, projectedTotalDifferential (k := k) (P p) *
      projectedTotalDifferential (P p) = 0) :
    LinearMap.ker (finiteFaceTensorDifferential (k := k) P) =
      Submodule.span k {z | ∃ x : ∀ p, TotalFaceModule (k := k) (P p),
        (∀ p, projectedTotalDifferential (P p) (x p) = 0) ∧
          PiTensorProduct.tprod k x = z} ⊔
      LinearMap.range (finiteFaceTensorDifferential P) := by
  exact TensorCycleSpanning.ker_differential_eq_span_cycles_sup_range
    (fun p => projectedTotalDifferential (P p)) (fun p => totalFaceInvolute (P p))
    hdd (fun p => totalFaceInvolute_square (P p))
    (fun p => projectedTotalDifferential_anticommute (P p))
    (fun h p => totalFaceInvolute_eq_one_of_two_eq_zero (P p) h)

/-- The strengthened actual tensor theorem uses homogeneous factor cycles.
Every grading and parity hypothesis is discharged from the exterior basis. -/
theorem finiteFaceTensorHomogeneousCycles {m : ℕ} (P : Fin m → Finset V → Prop)
    (hdd : ∀ p, projectedTotalDifferential (k := k) (P p) *
      projectedTotalDifferential (P p) = 0) :
    LinearMap.ker (finiteFaceTensorDifferential (k := k) P) =
      Submodule.span k {z | ∃ x : ∀ p, TotalFaceModule (k := k) (P p),
        (∀ p, projectedTotalDifferential (P p) (x p) = 0 ∧
          ∃ j, x p ∈ totalFacePiece (P p) j) ∧ PiTensorProduct.tprod k x = z} ⊔
      LinearMap.range (finiteFaceTensorDifferential P) := by
  have h := TensorCycleSpanning.ker_differential_eq_span_homogeneous_cycles_sup_range
    (fun p => totalFaceBasis (k := k) (P p)) (fun _ s => s.val.card)
    (fun p => projectedTotalDifferential (P p)) (fun p => totalFaceInvolute (P p))
    hdd (fun p => totalFaceInvolute_square (P p))
    (fun p => projectedTotalDifferential_anticommute (P p))
    (fun h p => totalFaceInvolute_eq_one_of_two_eq_zero (P p) h)
    (fun p x hx => projectedTotalDifferential_zero_piece (P p) x
      ((tensorDegreePiece_eq_facePiece (k := k) (P p) 0) ▸ hx))
    (fun p j x hx => (tensorDegreePiece_eq_facePiece (k := k) (P p) j).symm ▸
      projectedTotalDifferential_lowers_piece (P p) j x
        ((tensorDegreePiece_eq_facePiece (k := k) (P p) (j + 1)) ▸ hx))
  have hd : TensorCycleSpanning.differential
      (fun p => projectedTotalDifferential (k := k) (P p))
      (fun p => totalFaceInvolute (P p)) = finiteFaceTensorDifferential P := rfl
  rw [hd] at h
  simpa only [tensorDegreePiece_eq_facePiece] using h

/-- For genuine homogeneous quotient Koszul face complexes the remaining
square-zero condition is discharged by the previously checked actual boundary. -/
theorem quotientFaceTensorCycles {m : ℕ}
    (B : Fin m → Family V) (α : Fin m → Exponent V) :
    LinearMap.ker (finiteFaceTensorDifferential (k := k)
      (fun p => quotientKoszulFaces (B p) (α p))) =
      Submodule.span k {z | ∃ x : ∀ p, TotalFaceModule (k := k)
          (quotientKoszulFaces (B p) (α p)),
        (∀ p, projectedTotalDifferential (quotientKoszulFaces (B p) (α p)) (x p) = 0) ∧
          PiTensorProduct.tprod k x = z} ⊔
      LinearMap.range (finiteFaceTensorDifferential
        (fun p => quotientKoszulFaces (B p) (α p))) := by
  apply finiteFaceTensorCycles
  intro p
  rw [← quotientTotalDifferential_eq_projected]
  exact quotientTotalDifferential_comp (B p) (α p)

theorem quotientFaceTensorHomogeneousCycles {m : ℕ}
    (B : Fin m → Family V) (α : Fin m → Exponent V) :
    LinearMap.ker (finiteFaceTensorDifferential (k := k)
      (fun p => quotientKoszulFaces (B p) (α p))) =
      Submodule.span k {z | ∃ x : ∀ p, TotalFaceModule (k := k)
          (quotientKoszulFaces (B p) (α p)),
        (∀ p, projectedTotalDifferential (quotientKoszulFaces (B p) (α p)) (x p) = 0 ∧
          ∃ j, x p ∈ totalFacePiece (quotientKoszulFaces (B p) (α p)) j) ∧
          PiTensorProduct.tprod k x = z} ⊔
      LinearMap.range (finiteFaceTensorDifferential
        (fun p => quotientKoszulFaces (B p) (α p))) := by
  apply finiteFaceTensorHomogeneousCycles
  intro p
  rw [← quotientTotalDifferential_eq_projected]
  exact quotientTotalDifferential_comp (B p) (α p)

/-- Transfer the cycle-spanning theorem through the checked literal exterior
product isomorphism. By `finiteFaceTensorEquiv_actual_product`, the representatives
in the displayed span are exactly ordered products of the factor cycles. -/
theorem separatedFaceCycles {m : ℕ} (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀ p q, p ≠ q → ∀ x, S p x → ¬S q x)
    (hP : ∀ p F, P p F → ∀ x ∈ F, S p x)
    (hdd : ∀ p, projectedTotalDifferential (k := k) (P p) *
      projectedTotalDifferential (P p) = 0) :
    LinearMap.ker (projectedTotalDifferential (k := k) (separatedFamilyFaces S P)) =
      Submodule.span k {z | ∃ x : ∀ p, TotalFaceModule (k := k) (P p),
        (∀ p, projectedTotalDifferential (P p) (x p) = 0) ∧
          finiteFaceTensorEquiv S P hS hP (PiTensorProduct.tprod k x) = z} ⊔
      LinearMap.range (projectedTotalDifferential (separatedFamilyFaces S P)) := by
  let e := finiteFaceTensorEquiv (k := k) S P hS hP
  let d := finiteFaceTensorDifferential (k := k) P
  let D := projectedTotalDifferential (k := k) (separatedFamilyFaces S P)
  have hc (x) : D (e x) = e (d x) :=
    LinearMap.congr_fun (finiteFaceTensorEquiv_is_chain S P hS hP) x
  have hk : (LinearMap.ker d).map e.toLinearMap = LinearMap.ker D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change D (e x) = 0
      rw [hc, show d x = 0 from hx, map_zero]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change d (e.symm y) = 0
      apply e.injective
      rw [map_zero, ← hc, e.apply_symm_apply]
      exact hy
  have hr : (LinearMap.range d).map e.toLinearMap = LinearMap.range D := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, hc x⟩
    · rintro ⟨z, rfl⟩
      refine ⟨d (e.symm z), ⟨e.symm z, rfl⟩, ?_⟩
      change e (d (e.symm z)) = D z
      rw [← hc, e.apply_symm_apply]
  have heq := congrArg (Submodule.map e.toLinearMap) (finiteFaceTensorCycles P hdd)
  change (LinearMap.ker d).map e.toLinearMap = _ at heq
  rw [hk, Submodule.map_sup, Submodule.map_span, hr] at heq
  convert heq using 2
  apply congrArg (Submodule.span k)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨PiTensorProduct.tprod k x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientFaceTensorCycles
#print axioms FourPapers.Sublattice.quotientFaceTensorHomogeneousCycles
#print axioms FourPapers.Sublattice.separatedFaceCycles


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PowerCycleProducts -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u

section Products
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma boundary_list_product_eq_zero (xs : List (Simplicial.Ambient V k))
    (hx : ∀ x ∈ xs, Simplicial.boundary x = 0) :
    Simplicial.boundary xs.prod = 0 := by
  induction xs with
  | nil => exact CliffordAlgebra.contractLeft_one _ _
  | cons x xs ih =>
    have h1 : Simplicial.boundary x = 0 := hx x (List.mem_cons_self ..)
    have h2 : Simplicial.boundary xs.prod = 0 :=
      ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    change Simplicial.boundary (x * xs.prod) = 0
    rw [CliffordAlgebra.contractLeft_mul, h1, h2, zero_mul, mul_zero, add_zero]

end Products

variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The actual fine-degree strand of the Koszul complex of the ordinary power.
This abbreviation only suppresses the previously established monomial face model. -/
abbrev PowerFaceModule (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :=
  TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)

abbrev powerFaceDifferential (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Module.End k (PowerFaceModule (E := E) (k := k) m α) :=
  idealTotalDifferential (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)

/-- Literal exterior products of `m` cycles from the first ordinary power,
with their actual fine degrees adding to the specified degree. -/
def firstPowerProductCycles (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Set (PowerFaceModule (E := E) (k := k) m α) :=
  {z | ∃ β : Fin m → Exponent (FiniteVariable.{u} n),
    ∃ x : ∀ p, PowerFaceModule (E := E) (k := k) 1 (β p),
      (∑ p, β p) = α ∧
      (∀ p, powerFaceDifferential 1 (β p) (x p) = 0) ∧
      z.val = (List.ofFn (fun p => (x p).val)).prod}

def productCycleBoundarySpan (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Submodule k (PowerFaceModule (E := E) (k := k) m α) :=
  Submodule.span k (firstPowerProductCycles m α) ⊔ LinearMap.range (powerFaceDifferential m α)

lemma productCycleBoundarySpan_le_cycles (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    productCycleBoundarySpan (E := E) (k := k) m α ≤ LinearMap.ker (powerFaceDifferential m α) := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro z ⟨β, x, hβ, hx, hz⟩
    change powerFaceDifferential m α z = 0
    apply Subtype.ext
    change Simplicial.boundary z.val = 0
    rw [hz]
    apply boundary_list_product_eq_zero
    intro y hy
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hy
    exact congrArg Subtype.val (hx p)
  · rintro z ⟨y, rfl⟩
    change powerFaceDifferential m α (powerFaceDifferential m α y) = 0
    apply Subtype.ext
    exact Simplicial.boundary_boundary y.val

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.productCycleBoundarySpan_le_cycles

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PowerCycleGeneration -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma chainTotalEquiv_ordinary_differential (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (x : ChainTotalModule n E m α k) :
    chainTotalEquiv hE m α k (chainTotalOrdinaryDifferential hE m α k x) =
      powerFaceDifferential m α (chainTotalEquiv hE m α k x) := by
  simp only [chainTotalOrdinaryDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

lemma coveredBlockLift_cycle_generated (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (w : AdmissibleChain n E m α)
    (hw : CrossingCovered w.val (α - finiteChainShift n w.val))
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)))
    (hx : quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val) x = 0) :
    chainTotalEquiv hE m α k (coveredBlockLift hE w hw x) ∈
      productCycleBoundarySpan m α := by
  let v := α - finiteChainShift n w.val
  let P := crossingBlockFaces w.val v
  let β := crossingBlockFineDegree w.val v
  let e := crossingBlockTensorEquiv (k := k) hE w.val v hw
  let c : PowerFaceModule (E := E) (k := k) m (∑ p, β p) ≃ₗ[k]
      PowerFaceModule (E := E) (k := k) m α :=
    facePredicateEquiv _ _ (fun F => by rw [crossingFineDegree_admissible w hw])
  let L := c.toLinearMap.comp (crossingLiftTensorProduct (k := k) hE w.val v)
  have hL (y) : powerFaceDifferential m α (L y) = L (finiteFaceTensorDifferential P y) := by
    apply Subtype.ext
    simp only [powerFaceDifferential, idealTotalDifferential_val, L, c,
      LinearMap.comp_apply, LinearEquiv.coe_coe, facePredicateEquiv_val]
    exact congrArg Subtype.val
      (LinearMap.congr_fun (crossingLiftTensorProduct_is_chain (k := k) hE w.val v) y)
  have hy : e.symm x ∈ LinearMap.ker (finiteFaceTensorDifferential P) := by
    change finiteFaceTensorDifferential P (e.symm x) = 0
    apply e.injective
    rw [map_zero]
    have he := LinearMap.congr_fun (crossingBlockTensorEquiv_is_chain (k := k)
      hE w.val v hw) (e.symm x)
    have hx' : quotientTotalDifferential (finiteChainCoefficientFamily n w.val) v x = 0 := hx
    simp only [e, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at he
    exact he.symm.trans hx'
  have hcycles := quotientFaceTensorCycles (k := k)
    (fun p => finitePredecessorFamily n E (w.val.val p).val)
    (fun p => finiteBlockDegree w.val p v)
  change LinearMap.ker (finiteFaceTensorDifferential P) = _ at hcycles
  rw [hcycles] at hy
  have hspan : Submodule.span k {z | ∃ y : ∀ p, TotalFaceModule (k := k) (P p),
      (∀ p, projectedTotalDifferential (P p) (y p) = 0) ∧ PiTensorProduct.tprod k y = z} ≤
      (productCycleBoundarySpan (E := E) (k := k) m α).comap L := by
    apply Submodule.span_le.mpr
    rintro z ⟨y, hy, rfl⟩
    apply Submodule.mem_sup_left
    apply Submodule.subset_span
    refine ⟨β, (fun p => crossingBlockLift (k := k) hE w.val v p (y p)),
      crossingFineDegree_admissible w hw, ?_, ?_⟩
    · intro p
      rw [crossingBlockLift_differential, hy p, map_zero]
    · change (crossingLiftTensorProduct hE w.val v (PiTensorProduct.tprod k y)).val = _
      simp only [crossingLiftTensorProduct, LinearMap.comp_apply, PiTensorProduct.map_tprod,
        idealPowerOrderedProduct_tprod_val]
  have hrange : LinearMap.range (finiteFaceTensorDifferential P) ≤
      (productCycleBoundarySpan (E := E) (k := k) m α).comap L := by
    rintro z ⟨y, rfl⟩
    apply Submodule.mem_sup_right
    exact ⟨L y, hL y⟩
  have hmem := (sup_le hspan hrange) hy
  change L (e.symm x) ∈ productCycleBoundarySpan m α at hmem
  simpa only [coveredBlockLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, crossingWholeLift, L, c, e] using hmem

lemma uncoveredBlockLift_cycle_boundary (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (w : AdmissibleChain n E m α)
    (hw : ¬CrossingCovered w.val (α - finiteChainShift n w.val))
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)))
    (hx : quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val) x = 0) :
    chainTotalEquiv hE m α k (uncoveredBlockLift hE w hw x) ∈
      LinearMap.range (powerFaceDifferential m α) := by
  let H := uncoveredBlockHomotopy (k := k) hE w hw
  let s := DFinsupp.lsingle (R := k) (M := fun z : AdmissibleChain n E m α =>
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n z.val)
      (α - finiteChainShift n z.val))) w
  refine ⟨chainTotalEquiv hE m α k (s (H x)), ?_⟩
  rw [←chainTotalEquiv_ordinary_differential]
  apply congrArg (chainTotalEquiv hE m α k)
  simp only [uncoveredBlockLift, contractibleBlockLift, LinearMap.add_apply,
    LinearMap.comp_apply, hx, map_zero, add_zero]
  rfl

lemma allPowerBlockLift_cycle_generated (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (w : AdmissibleChain n E m α)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)))
    (hx : quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val) x = 0) :
    chainTotalEquiv hE m α k (allPowerBlockLift hE w x) ∈
      productCycleBoundarySpan m α := by
  unfold allPowerBlockLift
  split_ifs with hw
  · exact coveredBlockLift_cycle_generated hE w hw x hx
  · exact Submodule.mem_sup_right (uncoveredBlockLift_cycle_boundary hE w hw x hx)

lemma allPowerChange_cycle_generated (hE : finiteLatticeClosed n E)
    {m : ℕ} {α : Exponent (FiniteVariable.{u} n)} (x : ChainTotalModule n E m α k)
    (hx : chainTotalSpecialDifferential n E m α k x = 0) :
    chainTotalEquiv hE m α k (allPowerChange hE m α x) ∈ productCycleBoundarySpan m α := by
  let L := (chainTotalEquiv hE m α k).toLinearMap
  have he : L.comp (allPowerChange hE m α) =
      DFinsupp.lsum k (fun w => L.comp (allPowerBlockLift hE w)) := by
    apply DFinsupp.lhom_ext
    intro w y
    simp only [LinearMap.comp_apply, allPowerChange, DFinsupp.lsum_single]
  change (L.comp (allPowerChange hE m α)) x ∈ _
  rw [he, DFinsupp.lsum_apply_apply]
  apply Submodule.dfinsuppSumAddHom_mem
  intro w _
  apply allPowerBlockLift_cycle_generated hE w (x w)
  exact congrArg (fun y : ChainTotalModule n E m α k => y w) hx

/-- Every cycle in every positive ordinary power is, modulo actual boundaries,
a linear combination of literal products of first-power cycles. All fine
degrees and all homological degrees are included. -/
theorem powerFaceCycles_generated (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) :
    LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α) =
      Submodule.span k (firstPowerProductCycles m α) ⊔
        LinearMap.range (powerFaceDifferential m α) := by
  apply le_antisymm
  · intro z hz
    change z ∈ productCycleBoundarySpan m α
    obtain ⟨e, he, hchain⟩ := allPowerTotalChainEquiv_exists (k := k) hE m hm α
    let t := chainTotalEquiv hE m α k
    let x := e.symm (t.symm z)
    have hx : chainTotalSpecialDifferential n E m α k x = 0 := by
      apply e.injective
      rw [map_zero]
      have hc := LinearMap.congr_fun hchain x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
      rw [←hc]
      apply t.injective
      rw [map_zero, chainTotalEquiv_ordinary_differential]
      simpa only [x, t, LinearEquiv.apply_symm_apply] using
        (show powerFaceDifferential m α z = 0 from hz)
    have hmem := allPowerChange_cycle_generated hE x hx
    rw [←he] at hmem
    simpa only [LinearEquiv.coe_coe, x, LinearEquiv.apply_symm_apply, t] using hmem
  · exact productCycleBoundarySpan_le_cycles m α

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.powerFaceCycles_generated
#print axioms FourPapers.Sublattice.coveredBlockLift_cycle_generated
#print axioms FourPapers.Sublattice.uncoveredBlockLift_cycle_boundary


end
end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.Buchberger -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Buchberger's criterion

Let `m` be a monomial order on `σ →₀ ℕ` and let `G` be a set of multivariate polynomials whose
nonzero members have unit leading coefficients, for instance any set of polynomials over a field.
Buchberger's criterion says that `G` is a Gröbner basis of the ideal it generates if and only if
`0` is a remainder of every S-polynomial `m.sPolynomial g₁ g₂` with `g₁, g₂ ∈ G` on division by `G`.
This turns the infinitely many conditions in the definition of a Gröbner basis into finitely many
checks when `G` is finite, and is the key step in the correctness of Buchberger's algorithm.

## Main results

* `MonomialOrder.IsGroebnerBasis.isRemainder_sPolynomial_zero`: the S-polynomials of a Gröbner
  basis have remainder `0`.
* `MonomialOrder.isGroebnerBasis_span_of_isRemainder_sPolynomial_zero`: **Buchberger's criterion**,
  if every S-polynomial of `G` has remainder `0` on division by `G`, then `G` is a Gröbner basis of
  `Ideal.span G`.
* `MonomialOrder.isGroebnerBasis_span_iff_isRemainder_sPolynomial_zero` and
  `MonomialOrder.isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero`: the resulting
  characterizations of Gröbner bases.

## Implementation notes

A remainder `0` of `f` on division by `G` is a *standard representation* `f = ∑ q_b * b` with
every `q_b * b` of degree at most that of `f`. The proof works with the `R`-span of the products
`X^a * b`, `b ∈ G`, whose degree `a + deg b` lies below a bound `d`. Products of degree exactly
`d` with `b ≠ 0` differ, after normalizing their leading coefficients, by monomial multiples of
S-polynomials, and these have representations of degree `< d` by hypothesis. So a representation
of degree at most `d` of a polynomial whose coefficient at `d` vanishes can be replaced by one of
degree `< d`, and well-founded induction on `d` shows that every element of `Ideal.span G` has a
standard representation. Its leading monomial is then divisible by the leading monomial of an
element of `G`.

The theorems hold over any commutative ring, assuming only that the nonzero members of `G` have
unit leading coefficients; over a field this is `MonomialOrder.isUnit_leadingCoeff`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Theorem 6
  (Buchberger's criterion) and Lemma 5 (cancellation of leading terms by S-polynomials).
-/

section
namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} {m : MonomialOrder σ} [CommRing R] {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

variable (m) in
/-- The `R`-span of the products `X^a * b` with `b ∈ G` whose degree `a + deg b`, read in `m.syn`,
lies in `s`. For `s = Set.Iic d` it consists of the polynomials having a representation
`∑ q_b * b` by `G` with `deg q_b + deg b ≤ d` for every `b`. -/
private noncomputable def degreeSpan (G : Set (MvPolynomial σ R)) (s : Set m.syn) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {p | ∃ b ∈ G, ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ p = monomial a 1 * b}

private theorem monomial_one_mul_mem_degreeSpan {s : Set m.syn} {b : MvPolynomial σ R}
    (hb : b ∈ G) {a : σ →₀ ℕ} (has : m.toSyn (a + m.degree b) ∈ s) :
    monomial a 1 * b ∈ degreeSpan m G s :=
  Submodule.subset_span ⟨b, hb, a, has, rfl⟩

private theorem degreeSpan_mono {s t : Set m.syn} (hst : s ⊆ t) :
    degreeSpan m G s ≤ degreeSpan m G t :=
  Submodule.span_mono fun _ ⟨b, hb, a, has, hp⟩ ↦ ⟨b, hb, a, hst has, hp⟩

private theorem mem_degreeSpan_self {b : MvPolynomial σ R} (hb : b ∈ G) :
    b ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree b))) := by
  simpa using monomial_one_mul_mem_degreeSpan (s := Set.Iic _) hb (a := 0) (by simp)

private theorem monomial_mul_mem_degreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ degreeSpan m G (Set.Iic d)) (c : σ →₀ ℕ) (r : R) :
    monomial c r * p ∈ degreeSpan m G (Set.Iic (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have hcab : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, monomial_mul_monomial, mul_one]
    rw [hcab]
    refine Submodule.smul_mem _ _ (monomial_one_mul_mem_degreeSpan hb ?_)
    rw [Set.mem_Iic, add_assoc, map_add]
    gcongr
    exact had
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

private theorem mul_mem_degreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ degreeSpan m G (Set.Iic d)) (q : MvPolynomial σ R) :
    q * p ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree q) + d)) := by
  have hq : q * p = ∑ c ∈ q.support, monomial c (q.coeff c) * p := by
    rw [← Finset.sum_mul, ← q.as_sum]
  rw [hq]
  refine Submodule.sum_mem _ fun c hc ↦ degreeSpan_mono ?_ (monomial_mul_mem_degreeSpan hp c _)
  exact Set.Iic_subset_Iic.2 (by gcongr; exact m.le_degree hc)

/-- A polynomial with remainder `0` on division by `G` has a representation by `G` of degree at
most its own degree. -/
private theorem IsRemainder.mem_degreeSpan {f : MvPolynomial σ R} (h : m.IsRemainder f G 0) :
    f ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree f))) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  generalize hV : degreeSpan m G (Set.Iic (m.toSyn (m.degree f))) = V
  rw [hfg, add_zero, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun b _ ↦ ?_
  rcases eq_or_ne (g b) 0 with hg | hg
  · simp [hg]
  rcases eq_or_ne (b : MvPolynomial σ R) 0 with hb | hb
  · simp [hb]
  rw [smul_eq_mul, ← hV]
  refine degreeSpan_mono (Set.Iic_subset_Iic.2 ?_) (mul_mem_degreeSpan (mem_degreeSpan_self b.2) _)
  rw [add_comm]
  exact (toWithBotSyn_withBotDegree_add_le_iff hb hg hf).1 (hdeg b)

/-- Every element of `Ideal.span G` has a representation by `G` of some bounded degree. -/
private theorem exists_mem_degreeSpan_of_mem_span {f : MvPolynomial σ R}
    (hf : f ∈ Ideal.span G) : ∃ d, f ∈ degreeSpan m G (Set.Iic d) := by
  induction hf using Submodule.span_induction with
  | mem b hb => exact ⟨_, mem_degreeSpan_self hb⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hx⟩ := hx
    obtain ⟨d₂, hy⟩ := hy
    exact ⟨d₁ ⊔ d₂, add_mem (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul q x _ hx =>
    obtain ⟨d, hx⟩ := hx
    exact ⟨_, mul_mem_degreeSpan hx q⟩

/-- An element of the span of the products of degree `< d` lies in the span of the products of
degree at most some `d' < d`. -/
private theorem eq_zero_or_exists_mem_degreeSpan_Iic {d : m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ degreeSpan m G (Set.Iio d)) :
    f = 0 ∨ ∃ d' < d, f ∈ degreeSpan m G (Set.Iic d') := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    exact .inr ⟨_, had, monomial_one_mul_mem_degreeSpan hb le_rfl⟩
  | zero => exact .inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | ⟨d₁, hd₁, hx⟩
    · rwa [zero_add]
    rcases hy with rfl | ⟨d₂, hd₂, hy⟩
    · rw [add_zero]
      exact .inr ⟨d₁, hd₁, hx⟩
    exact .inr ⟨d₁ ⊔ d₂, max_lt hd₁ hd₂, add_mem
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul r x _ hx =>
    rcases hx with rfl | ⟨d', hd', hx⟩
    · exact .inl (smul_zero r)
    exact .inr ⟨d', hd', Submodule.smul_mem _ r hx⟩

/-- If an element of the span of the products whose degrees lie in `s` has a nonzero coefficient
at `e`, then one of these products, with `b ≠ 0`, has degree at least `e`. -/
private theorem exists_le_of_mem_degreeSpan {s : Set m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ degreeSpan m G s) {e : σ →₀ ℕ} (he : f.coeff e ≠ 0) :
    ∃ b ∈ G, b ≠ 0 ∧ ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ m.toSyn e ≤ m.toSyn (a + m.degree b) := by
  by_contra! H
  have hle : degreeSpan m G s ≤ LinearMap.ker (lcoeff R e) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, has, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simpa using m.coeff_eq_zero_of_lt
      ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt (H b hb hb0 a has))
  exact he (by simpa using hle hf)

/-- **The reduction step.** If every S-polynomial of `G` has remainder `0` on division by `G`, a
representation of degree at most `D` of a polynomial whose coefficient at `D` vanishes can be
replaced by a representation of degree `< D`. -/
private theorem mem_degreeSpan_Iio_of_coeff_eq_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) {D : σ →₀ ℕ}
    {f : MvPolynomial σ R} (hf : f ∈ degreeSpan m G (Set.Iic (m.toSyn D))) (hfD : f.coeff D = 0) :
    f ∈ degreeSpan m G (Set.Iio (m.toSyn D)) := by
  by_cases htop : ∃ b₀ ∈ G, b₀ ≠ 0 ∧ m.degree b₀ ≤ D
  swap
  · -- No product of degree exactly `D` is nonzero, so every product has degree `< D`.
    simp only [not_exists, not_and] at htop
    refine Submodule.span_le.2 ?_ hf
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    refine monomial_one_mul_mem_degreeSpan hb (lt_of_le_of_ne had fun h ↦ ?_)
    exact htop b hb hb0 (m.toSyn.injective h ▸ le_add_self)
  -- Fix a normalized product `q₀` of degree `D`. Every product `p` of degree at most `D` satisfies
  -- `p - p.coeff D • q₀ ∈ degreeSpan m G (Set.Iio D)`, and this condition is linear in `p`.
  obtain ⟨b₀, hb₀, hb₀0, hb₀D⟩ := htop
  obtain ⟨u₀, hu₀⟩ := hG b₀ hb₀ hb₀0
  set q₀ := monomial (D - m.degree b₀) (↑u₀⁻¹ : R) * b₀
  have hle : degreeSpan m G (Set.Iic (m.toSyn D)) ≤ (degreeSpan m G (Set.Iio (m.toSyn D))).comap
      (LinearMap.id - (lcoeff R D).smulRight q₀) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, lcoeff_apply]
    rcases eq_or_ne (a + m.degree b) D with rfl | hne
    · -- The difference is a monomial multiple of `S(b, b₀)`, which has a representation of
      -- degree `deg S(b, b₀) < deg b ⊔ deg b₀`.
      rw [coeff_monomial_mul, one_mul, ← leadingCoeff,
        m.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial hb₀D u₀ hu₀]
      set L := m.degree b ⊔ m.degree b₀
      rcases eq_or_ne (m.sPolynomial b b₀) 0 with hS0 | hS0
      · simp [hS0]
      refine degreeSpan_mono (Set.Iic_subset_Iio.2 ?_)
        (monomial_mul_mem_degreeSpan (hS b hb b₀ hb₀).mem_degreeSpan _ _)
      calc m.toSyn (a + m.degree b - L) + m.toSyn (m.degree (m.sPolynomial b b₀))
          < m.toSyn (a + m.degree b - L) + m.toSyn L := by
            gcongr; exact m.degree_sPolynomial_lt_sup_degree hS0
        _ = m.toSyn (a + m.degree b) := by
            rw [← map_add, tsub_add_cancel_of_le (sup_le le_add_self hb₀D)]
    · -- The product has degree `< D`, so its coefficient at `D` vanishes.
      have hlt : m.toSyn (a + m.degree b) < m.toSyn D :=
        lt_of_le_of_ne had (m.toSyn.injective.ne hne)
      rw [m.coeff_eq_zero_of_lt ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt hlt), zero_smul,
        sub_zero]
      exact monomial_one_mul_mem_degreeSpan hb hlt
  simpa [hfD] using hle hf

/-- If every S-polynomial of `G` has remainder `0` on division by `G`, then every polynomial with a
representation by `G` of degree at most `d` has a representation of degree at most its own
degree, so its leading monomial is divisible by the leading monomial of a nonzero element of
`G`. -/
private theorem exists_degree_le_degree_of_mem_degreeSpan
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) (d : m.syn)
    {f : MvPolynomial σ R} (hf : f ∈ degreeSpan m G (Set.Iic d)) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  induction d using WellFoundedLT.induction generalizing f with
  | ind d ih =>
  obtain ⟨b, hb, hb0, a, had, hfa⟩ :=
    exists_le_of_mem_degreeSpan hf (m.coeff_degree_ne_zero_iff.2 hf0)
  rcases eq_or_ne (m.toSyn (m.degree f)) d with hfd | hfd
  · -- A product of degree exactly `deg f` occurs, so `deg b ≤ deg f`.
    have : a + m.degree b = m.degree f := m.toSyn.injective (le_antisymm (hfd ▸ had) hfa)
    exact ⟨b, hb, hb0, this ▸ le_add_self⟩
  · -- Otherwise `deg f < d`, and the representation can be improved.
    have hlt : m.toSyn (m.degree f) < d := lt_of_le_of_ne (hfa.trans had) hfd
    obtain ⟨D, rfl⟩ := m.toSyn.surjective d
    have hfD := mem_degreeSpan_Iio_of_coeff_eq_zero hG hS hf (m.coeff_eq_zero_of_lt hlt)
    obtain hf' | ⟨d', hd', hf'⟩ := eq_zero_or_exists_mem_degreeSpan_Iic hfD
    · exact absurd hf' hf0
    exact ih d' hd' hf' hf0

/-- The S-polynomials of two members of a Gröbner basis have remainder `0` on division by that
basis. -/
theorem IsGroebnerBasis.isRemainder_sPolynomial_zero (h : m.IsGroebnerBasis G I)
    {g₁ g₂ : MvPolynomial σ R} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) :
    m.IsRemainder (m.sPolynomial g₁ g₂) G 0 :=
  h.isRemainder_zero_iff_mem.2 (sPolynomial_mem_ideal (h.subset hg₁) (h.subset hg₂))

/-- **Buchberger's criterion.** If the nonzero members of `G` have unit leading coefficients and
the S-polynomial of any two members of `G` has remainder `0` on division by `G`, then `G` is a
Gröbner basis of the ideal it generates. -/
theorem isGroebnerBasis_span_of_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) :
    m.IsGroebnerBasis G (Ideal.span G) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨Ideal.subset_span, fun f hf hf0 ↦ ?_⟩
  obtain ⟨d, hfd⟩ := exists_mem_degreeSpan_of_mem_span (m := m) hf
  exact exists_degree_le_degree_of_mem_degreeSpan hG hS d hfd hf0

/-- **Buchberger's criterion.** A set `G` whose nonzero members have unit leading coefficients is a
Gröbner basis of `I` if and only if it generates `I` and the S-polynomial of any two members of `G`
has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      Ideal.span G = I ∧ ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  refine ⟨fun h ↦ ⟨h.ideal_eq_span.symm, fun _ hg₁ _ hg₂ ↦
    h.isRemainder_sPolynomial_zero hg₁ hg₂⟩, ?_⟩
  rintro ⟨rfl, hS⟩
  exact isGroebnerBasis_span_of_isRemainder_sPolynomial_zero hG hS

/-- **Buchberger's criterion.** A set `G` whose nonzero members have unit leading coefficients is a
Gröbner basis of the ideal it generates if and only if the S-polynomial of any two members of `G`
has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_span_iff_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
      ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  simpa using isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero (I := Ideal.span G) hG

end MonomialOrder

end
end

/- BEGIN EXACT BODY: FourPapers.Common.MonicBinomialBuchberger -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.MonicBinomialBuchberger
open Classical MvPolynomial
variable {V k : Type*} [CommRing k] [IsDomain k] (m : MonomialOrder V)
variable {G : Set (MvPolynomial V k)}

/-- A literal multiple of a basis member has zero remainder. -/
theorem single_product (f q : MvPolynomial V k) (hf : f∈G) :
    m.IsRemainder (q*f) G 0 := by
  let b : G := ⟨f,hf⟩
  refine ⟨⟨Finsupp.single b q,by simp [b],?_⟩,by simp⟩
  intro c
  by_cases hc : c=b
  · subst c
    simp only [Finsupp.single_eq_same]
    change m.toWithBotSyn (m.withBotDegree f)+m.toWithBotSyn (m.withBotDegree q)≤ _
    rw [←map_add,←m.withBotDegree_mul,mul_comm]
  · simp [Finsupp.single_apply,hc,Ne.symm hc]

/-- A two-term standard representation, retaining the actual degree bound. -/
theorem two_products (f g q r s : MvPolynomial V k) (hf : f∈G) (hg : g∈G)
    (hfg : f≠g) (hs : s=q*f+r*g)
    (hq : m.toWithBotSyn (m.withBotDegree f)+m.toWithBotSyn (m.withBotDegree q)≤
      m.toWithBotSyn (m.withBotDegree s))
    (hr : m.toWithBotSyn (m.withBotDegree g)+m.toWithBotSyn (m.withBotDegree r)≤
      m.toWithBotSyn (m.withBotDegree s)) : m.IsRemainder s G 0 := by
  let bf : G := ⟨f,hf⟩
  let bg : G := ⟨g,hg⟩
  have hne : bf≠bg := fun h => hfg (congrArg Subtype.val h)
  refine ⟨⟨Finsupp.single bf q+Finsupp.single bg r,?_,?_⟩,by simp⟩
  · simpa only [map_add,Finsupp.linearCombination_single,smul_eq_mul,add_zero] using hs
  · intro b
    by_cases hbf : bf=b
    · subst b
      simpa [Finsupp.add_apply,Finsupp.single_apply,hne,Ne.symm hne,bf] using hq
    · by_cases hbg : bg=b
      · subst b
        simpa [Finsupp.add_apply,Finsupp.single_apply,hne,Ne.symm hne,bg] using hr
      · simp [Finsupp.add_apply,Finsupp.single_apply,hbf,hbg]

lemma binomial_degree {a b : V →₀ ℕ} (h : m.toSyn b< m.toSyn a) :
    m.degree (monomial a (1:k)-monomial b 1)=a := by
  have h' : m.toSyn (m.degree (monomial b (1:k)))<
      m.toSyn (m.degree (monomial a (1:k))) := by
    simpa only [m.degree_monomial,if_neg one_ne_zero] using h
  rw [m.degree_sub_of_lt h',m.degree_monomial,if_neg one_ne_zero]

lemma binomial_leadingCoeff {a b : V →₀ ℕ} (h : m.toSyn b< m.toSyn a) :
    m.leadingCoeff (monomial a (1:k)-monomial b 1)=1 := by
  have h' : m.toSyn (m.degree (monomial b (1:k)))<
      m.toSyn (m.degree (monomial a (1:k))) := by
    simpa only [m.degree_monomial,if_neg one_ne_zero] using h
  rw [m.leadingCoeff_sub_of_lt h',m.leadingCoeff_monomial]

lemma binomial_ne_zero {a b : V →₀ ℕ} (h : m.toSyn b< m.toSyn a) :
    monomial a (1:k)-monomial b 1≠0 := by
  intro hz
  have hc := binomial_leadingCoeff (k:=k) m h
  rw [hz,m.leadingCoeff_zero] at hc
  exact zero_ne_one hc

/-- The coprime S-pair criterion for two monic binomials, proved through
their actual two-term remainder representation over every integral domain. -/
theorem coprime_binomial_pair {a b c d : V →₀ ℕ}
    (hab : m.toSyn b< m.toSyn a) (hcd : m.toSyn d< m.toSyn c)
    (hac : a⊔c=a+c)
    (hf : monomial a (1:k)-monomial b 1∈G)
    (hg : monomial c (1:k)-monomial d 1∈G) :
    m.IsRemainder
      (m.sPolynomial (monomial a (1:k)-monomial b 1)
        (monomial c 1-monomial d 1)) G 0 := by
  let f : MvPolynomial V k := monomial a 1-monomial b 1
  let g : MvPolynomial V k := monomial c 1-monomial d 1
  by_cases hfg : f=g
  · rw [show monomial a (1:k)-monomial b 1=g from hfg,m.sPolynomial_self]
    exact MonomialOrder.isRemainder_zero_left_iff.mpr rfl
  have hfa : m.degree f=a := binomial_degree m hab
  have hgc : m.degree g=c := binomial_degree m hcd
  have hfl : m.leadingCoeff f=1 := binomial_leadingCoeff m hab
  have hgl : m.leadingCoeff g=1 := binomial_leadingCoeff m hcd
  have hs : m.sPolynomial f g=monomial (a+d) 1-monomial (c+b) 1 := by
    rw [m.sPolynomial_def,hfa,hgc,hfl,hgl,hac,
      add_tsub_cancel_left,add_tsub_cancel_right]
    dsimp only [f,g]
    simp only [mul_sub,monomial_mul_monomial,mul_one]
    rw [add_comm c a]
    abel
  by_cases hz : m.sPolynomial f g=0
  · rw [show m.sPolynomial (monomial a (1:k)-monomial b 1)
      (monomial c 1-monomial d 1)=0 from hz]
    exact MonomialOrder.isRemainder_zero_left_iff.mpr rfl
  have hadcb : a+d≠c+b := by
    intro he
    apply hz
    rw [hs,he,sub_self]
  have hbound1 : m.toSyn (a+d) ≤ m.toSyn (m.degree (m.sPolynomial f g)) := by
    apply m.le_degree
    rw [mem_support_iff,hs]
    simpa [coeff_sub,coeff_monomial,hadcb,Ne.symm hadcb] using (one_ne_zero : (1:k)≠0)
  have hbound2 : m.toSyn (c+b)≤ m.toSyn (m.degree (m.sPolynomial f g)) := by
    apply m.le_degree
    rw [mem_support_iff,hs]
    simpa [coeff_sub,coeff_monomial,hadcb,Ne.symm hadcb] using (neg_ne_zero.mpr (one_ne_zero : (1:k)≠0))
  apply two_products m f g (monomial d 1) (-monomial b 1) (m.sPolynomial f g) hf hg hfg
  · rw [hs]
    dsimp only [f,g]
    simp only [mul_sub,neg_mul,monomial_mul_monomial,mul_one]
    rw [add_comm d a,add_comm b c,add_comm d b]
    ring
  · apply (MonomialOrder.toWithBotSyn_withBotDegree_add_le_iff
      (binomial_ne_zero m hab) (by simp) hz).mpr
    simpa only [binomial_degree m hab, m.degree_monomial,
      if_neg one_ne_zero, ← map_add] using hbound1
  · apply (MonomialOrder.toWithBotSyn_withBotDegree_add_le_iff
      (binomial_ne_zero m hcd) (by simp) hz).mpr
    simpa only [binomial_degree m hcd, m.degree_neg, m.degree_monomial,
      if_neg one_ne_zero, ← map_add] using hbound2

end FourPapers.MonicBinomialBuchberger


end
end
end


end
