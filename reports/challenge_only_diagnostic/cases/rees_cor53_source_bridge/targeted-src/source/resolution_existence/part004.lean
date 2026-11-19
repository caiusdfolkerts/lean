module
public import resolution_existence.part002
public import shared_results.part020
public import paper_results.part005
public import resolution_existence.part001
public import Mathlib.LinearAlgebra.Dimension.Free

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialFineHomologyComparison -/
section

/-! # Fine tensor strands are the literal monomial Koszul strands

The comparison sends an exterior coordinate to its actual tensor. Thus the
homology labels used by the fine free-resolution constructor are the genuine
fine Koszul homology, rather than an independently specified collection of
vector spaces. The subsequent finite-support argument uses the explicit cone
contraction outside the generator box.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice.MonomialFineResolution
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
attribute [local instance] Classical.propDecidable

/-- Compare the actual homology quotients while the chain modules remain
abstract. The two hypotheses are the adjacent commuting squares. -/
def splitHomologyOfThreeTerm
    {R : Type*} [CommRing R]
    (C : ℕ → Type*) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
    (d : ∀ p, C (p + 1) →ₗ[R] C p)
    (dd : ∀ p, (d p).comp (d (p + 1)) = 0) (p : ℕ)
    {X Y Z : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hfg : g.comp f = 0)
    (eX : X ≃ₗ[R] C (p + 1)) (eY : Y ≃ₗ[R] C p)
    (eZ : Z ≃ₗ[R] C p.pred)
    (hf : ∀ x, eY (f x) = d p (eX x))
    (hg : ∀ y, eZ (g y) = ProjectiveComplexSplitting.previous C d p (eY y)) :
    ProjectiveComplexSplitting.Homology C d dd p ≃ₗ[R]
      FilteredHomology.Homology f g hfg :=
  (ProjectiveComplexSplitting.homologyEquivKernelQuotient C d dd p).trans
    (FilteredHomology.threeTermHomologyEquiv f g hfg (d p)
      (ProjectiveComplexSplitting.previous C d p)
      (ProjectiveComplexSplitting.previous_comp C d dd p)
      eX eY eZ hf hg).symm

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (B : Family V)

abbrev CoordinateIndex (α : Exponent V) (p : ℕ) :=
  {i : MonomialIndex B p // monomialDegree i=α}

abbrev TensorIndex (α : Exponent V) (p : ℕ) :=
  {i : Index B // (fineDegree B i,homological B i)=(α,p)}

def pieceIndexEquiv (α : Exponent V) (p : ℕ) :
    CoordinateIndex B α p ≃ TensorIndex B α p where
  toFun a := ⟨(a.val.2,a.val.1.val),Prod.ext a.property a.val.1.property⟩
  invFun a := ⟨⟨⟨a.val.2,congrArg Prod.snd a.property⟩,a.val.1⟩,
    congrArg Prod.fst a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coordinatePieceBasis (α : Exponent V) (p : ℕ) :
    Module.Basis (CoordinateIndex B α p) K (homogeneousPiece (k := K) B α p) :=
  Grading.restrictedBasis (monomialCoefficientBasis (k := K) B p)
    (fun i => monomialDegree i=α)

@[simp] theorem coordinatePieceBasis_val (α : Exponent V) (p : ℕ)
    (i : CoordinateIndex B α p) :
    (coordinatePieceBasis (K := K) B α p i).val =
      monomialCoefficientBasis (k := K) B p i.val :=
  Grading.restrictedBasis_val (monomialCoefficientBasis (k := K) B p)
    (fun j => monomialDegree j = α) i

/-- The literal exterior-coordinate tensor map restricted to one fine strand. -/
def finePieceMap (α : Exponent V) (p : ℕ) :
    homogeneousPiece (k := K) B α p →ₗ[K]
      BasisMultigradedContraction.piece (R := K) (M := TensorModule (K := K) B)
        (tensorBasis (K := K) B) (fineDegree B) (homological B) α p where
  toFun x := ⟨TensorExteriorKoszul.lift (K := K) p x.val,
    lift_fine_mem (K := K) B α p x.val x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (TensorExteriorKoszul.lift (K := K) p) x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (TensorExteriorKoszul.lift (K := K) p) c x.val

@[simp] theorem finePieceMap_val (α : Exponent V) (p : ℕ)
    (x : homogeneousPiece (k := K) B α p) :
    (finePieceMap (K := K) B α p x).val = TensorExteriorKoszul.lift (K := K) p x.val := rfl

theorem finePieceMap_injective (α : Exponent V) (p : ℕ) :
    Function.Injective (finePieceMap (K := K) B α p) := by
  intro x y h
  apply Subtype.ext
  have hval := congrArg
    (fun z : BasisMultigradedContraction.piece (R := K) (M := TensorModule (K := K) B)
      (tensorBasis (K := K) B) (fineDegree B) (homological B) α p => z.val) h
  rw [finePieceMap_val,finePieceMap_val] at hval
  exact TensorExteriorKoszul.lift_injective (K := K) (V := V)
    (M := monomialIdeal K B) p hval

theorem finePieceMap_surjective (α : Exponent V) (p : ℕ) :
    Function.Surjective (finePieceMap (K := K) B α p) := by
  apply LinearMap.range_eq_top.mp
  apply le_antisymm le_top
  rw [← (BasisMultigradedContraction.pieceBasis (R := K)
    (M := TensorModule (K := K) B) (tensorBasis (K := K) B)
      (fineDegree B) (homological B) α p).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨⟨a, F⟩, h⟩, rfl⟩
  have hp : F.card = p := congrArg Prod.snd h
  have ha : fineDegree B (a,F) = α := congrArg Prod.fst h
  let i : CoordinateIndex B α p := ⟨⟨⟨F,hp⟩,a⟩,ha⟩
  refine ⟨coordinatePieceBasis (K := K) B α p i, ?_⟩
  apply Subtype.ext
  rw [finePieceMap_val, coordinatePieceBasis_val,
    BasisMultigradedContraction.pieceBasis_val (R := K) (M := TensorModule (K := K) B)]
  change TensorExteriorKoszul.lift (K := K) p
    (monomialCoefficientBasis (k := K) B p ⟨⟨F,hp⟩,a⟩) = tensorBasis (K := K) B (a,F)
  rw [monomialCoefficientBasis_apply, TensorExteriorKoszul.lift_single, tensorBasis_apply]

/-- The fine-strand equivalence is induced by the actual tensor map. -/
def finePieceEquiv (α : Exponent V) (p : ℕ) :=
  LinearEquiv.ofBijective (finePieceMap (K := K) B α p)
    ⟨finePieceMap_injective (K := K) B α p, finePieceMap_surjective (K := K) B α p⟩

/-- The comparison is the actual exterior-coordinate tensor map. -/
theorem finePieceEquiv_val (α : Exponent V) (p : ℕ)
    (x : homogeneousPiece (k := K) B α p) :
    (finePieceEquiv (K := K) B α p x).val=TensorExteriorKoszul.lift (K := K) p x.val := rfl

/-- Both adjacent differentials are the literal Koszul differential. -/
theorem finePieceEquiv_differential (α : Exponent V) (p : ℕ)
    (x : homogeneousPiece (k := K) B α (p+1)) :
    BasisMultigradedContraction.differential (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B) (fineDegree B)
        (homological B) (differential (K := K) B) (differential_lowers (K := K) B) α p
        (finePieceEquiv (K := K) B α (p+1) x)=
      finePieceEquiv (K := K) B α p (homogeneousDifferential (k := K) B α p x) := by
  apply Subtype.ext
  change differential (K := K) B (finePieceEquiv (K := K) B α (p+1) x).val=
    (finePieceEquiv (K := K) B α p (homogeneousDifferential (k := K) B α p x)).val
  rw [finePieceEquiv_val,finePieceEquiv_val]
  exact TensorExteriorKoszul.differential_lift (K := K)
    (MvPolynomial.X : V → MvPolynomial V K) p x.val

/-- The homology used to choose free generators equals genuine fine
Koszul homology, with no dimension-only replacement. -/
def strandEquivFineHomology (α : Exponent V) (p : ℕ) :
    Strand (K := K) B α p ≃ₗ[K] monomialFineHomology (k := K) B α p := by
  let C := fun p : ℕ => ↥(BasisMultigradedContraction.piece (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B)
    (fineDegree B) (homological B) α p)
  let d := BasisMultigradedContraction.differential (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B)
    (fineDegree B) (homological B) (differential (K := K) B) (differential_lowers (K := K) B) α
  let dd := BasisMultigradedContraction.differential_square (R := K) («M» := TensorModule (K := K) B) (tensorBasis (K := K) B)
    (fineDegree B) (homological B) (differential (K := K) B) (differential_square (K := K) B)
    (differential_lowers (K := K) B) α
  have hf (x : homogeneousPiece (k := K) B α (p + 1)) :
      finePieceEquiv (K := K) B α p (homogeneousDifferential (k := K) B α p x) =
        d p (finePieceEquiv (K := K) B α (p + 1) x) :=
    (finePieceEquiv_differential (K := K) B α p x).symm
  have hg (x : homogeneousPiece (k := K) B α p) :
      finePieceEquiv (K := K) B α p.pred (monomialFinePrevious (k := K) B α p x) =
        ProjectiveComplexSplitting.previous C d p (finePieceEquiv (K := K) B α p x) := by
    cases p with
    | zero =>
        simp only [monomialFinePrevious, ProjectiveComplexSplitting.previous,
          LinearMap.zero_apply, map_zero]
    | succ p => exact (finePieceEquiv_differential (K := K) B α p x).symm
  simpa only [Strand, BasisMultigradedContraction.StrandHomology,
    monomialFineHomology] using!
      splitHomologyOfThreeTerm (R := K) C d dd p
        (homogeneousDifferential (k := K) B α p)
        (monomialFinePrevious (k := K) B α p)
        (monomialFineDifferential_comp (k := K) B α p)
        (finePieceEquiv (K := K) B α (p + 1)) (finePieceEquiv (K := K) B α p)
        (finePieceEquiv (K := K) B α p.pred) hf hg

def strandEquivCategoricalHomology (α : Exponent V) (p : ℕ) :
    Strand (K := K) B α p ≃ₗ[K] (homogeneousComplex (k := K) B α).homology p :=
  (strandEquivFineHomology (K := K) B α p).trans
    (monomialFineCategoricalHomologyEquiv (k := K) B α p).symm

instance strand_finite (α : Exponent V) (p : ℕ) : Module.Finite K (Strand (K := K) B α p) :=
  Module.Finite.equiv (strandEquivFineHomology (K := K) B α p).symm

def generatorBound : ℕ := B.sup Finsupp.degree

theorem generator_coordinate_le (b : Exponent V) (hb : b∈B) (v : V) :
    b v≤generatorBound B :=
  (Finsupp.le_degree v b).trans (Finset.le_sup (f := Finsupp.degree) hb)

theorem strand_zero_of_degree_gt (α : Exponent V) (p : ℕ)
    (hα : Fintype.card V*generatorBound B<α.degree) :
    Subsingleton (Strand (K := K) B α p) := by
  letI := monomial_fine_homology_subsingleton_of_degree_gt (k := K) B (generatorBound B)
    (generator_coordinate_le B) α hα p
  exact ⟨fun x y => (strandEquivCategoricalHomology (K := K) B α p).injective (Subsingleton.elim _ _)⟩

theorem strand_zero_of_exterior_gt (α : Exponent V) (p : ℕ)
    (hp : Fintype.card V<p) : Subsingleton (Strand (K := K) B α p) := by
  letI := monomial_fine_homology_subsingleton_of_exterior_degree_gt (k := K) B α p hp
  exact ⟨fun x y => (strandEquivCategoricalHomology (K := K) B α p).injective (Subsingleton.elim _ _)⟩

/-- Only finitely many fine shifts occur. This is derived from the
literal cone contractions outside the generator box. -/
instance homologyIndex_finite : Finite (HomologyIndex (K := K) B) := by
  have hα (a : HomologyIndex (K := K) B) :
      a.1.degree≤Fintype.card V*generatorBound B := by
    by_contra h
    letI := strand_zero_of_degree_gt (K := K) B a.1 a.2.1 (Nat.lt_of_not_ge h)
    exact (Module.Free.chooseBasis K (Strand (K := K) B a.1 a.2.1)).ne_zero a.2.2
      (Subsingleton.elim _ _)
  have hp (a : HomologyIndex (K := K) B) : a.2.1≤Fintype.card V := by
    by_contra h
    letI := strand_zero_of_exterior_gt (K := K) B a.1 a.2.1 (Nat.lt_of_not_ge h)
    exact (Module.Free.chooseBasis K (Strand (K := K) B a.1 a.2.1)).ne_zero a.2.2
      (Subsingleton.elim _ _)
  let A := {α : Exponent V // α.degree≤Fintype.card V*generatorBound B}
  letI : Finite A := (Finsupp.finite_of_degree_le (Fintype.card V*generatorBound B)).to_subtype
  let T := Σ α : A,Σ p : Fin (Fintype.card V+1),
    Module.Free.ChooseBasisIndex K (Strand (K := K) B α.val p.val)
  let f : HomologyIndex (K := K) B → T := fun a =>
    ⟨⟨a.1,hα a⟩,⟨a.2.1,Nat.lt_succ_iff.mpr (hp a)⟩,a.2.2⟩
  let g : T → HomologyIndex (K := K) B := fun a => ⟨a.1.val,a.2.1.val,a.2.2⟩
  exact Finite.of_injective f (show Function.LeftInverse g f from fun _ => rfl).injective

instance homology_finite : Module.Finite K (Homology (K := K) B) :=
  Module.Finite.of_basis (homologyBasis (K := K) B)

end FourPapers.Sublattice.MonomialFineResolution

end
end
end

end
