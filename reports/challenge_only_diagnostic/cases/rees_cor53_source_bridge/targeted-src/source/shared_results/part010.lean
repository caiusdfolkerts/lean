module
public import graph_foundation.part012
public import shared_results.part009

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialOrdinaryCoordinates -/
section

/-!
# Actual ordinary-degree monomial Koszul coordinates

Fine-degree exactness is transported through the genuine Koszul face
equivalence. The finite homogeneous support decomposition then assembles
the fillings in ordinary degree. The construction includes homological degree zero and uses the literal
ordinary homogeneous submodules of the original monomial ideal.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def monomialPreviousDifferential (B : Family V) : ∀ p : ℕ,
    (Set.powersetCard V p →₀ monomialIdeal k B) →ₗ[k]
      (Set.powersetCard V p.pred →₀ monomialIdeal k B)
  | 0 => 0
  | p+1 => monomialDifferential (k := k) B p

lemma monomialPreviousDifferential_homogeneous (B : Family V) (p : ℕ)
    (t : MonomialIndex B p) :
    monomialPreviousDifferential (k := k) B p (monomialCoefficientBasis (k := k) B p t) ∈
      Grading.Piece (monomialCoefficientBasis (k := k) B p.pred) monomialDegree (monomialDegree t) := by
  cases p with
  | zero => exact Submodule.zero_mem _
  | succ p => exact monomialDifferential_homogeneous B _ p (Grading.basis_mem_piece _ _ t)

theorem monomialCoordinate_filling_of_face_exact
    (B : Family V) (α : Exponent V) (p : ℕ)
    (hfill : Simplicial.ExactIn (k := k) (koszulFaces B α) p)
    (z : Set.powersetCard V p →₀ monomialIdeal k B)
    (hz : z ∈ homogeneousPiece (k := k) B α p)
    (hdz : monomialPreviousDifferential (k := k) B p z = 0) :
    ∃ y, y ∈ homogeneousPiece (k := k) B α (p+1) ∧ monomialDifferential (k := k) B p y = z := by
  let zf := (faceHomogeneousEquiv (k := k) B α p).symm ⟨z, hz⟩
  have hclosed : Simplicial.boundary zf.val = 0 := by
    cases p with
    | zero => exact Simplicial.boundary_zero_degree_zero zf.property
    | succ p =>
        have hh : Simplicial.chainDifferential (koszulFaces_downward B α) p zf = 0 := by
          apply (faceHomogeneousEquiv (k := k) B α p).injective
          have he := LinearMap.congr_fun (faceHomogeneousEquiv_comm (k := k) B α p) zf
          change faceHomogeneousEquiv (k := k) B α p
              (Simplicial.chainDifferential (koszulFaces_downward B α) p zf) =
            homogeneousDifferential (k := k) B α p (faceHomogeneousEquiv (k := k) B α (p+1) zf) at he
          rw [he, (faceHomogeneousEquiv (k := k) B α (p+1)).apply_symm_apply,
            (faceHomogeneousEquiv (k := k) B α p).map_zero]
          apply Subtype.ext
          exact hdz
        exact congrArg Subtype.val hh
  obtain ⟨y, hyp, hy⟩ := hfill zf.val zf.property hclosed
  let yf : Simplicial.Chains (k := k) (koszulFaces B α) (p+1) := ⟨y, hyp⟩
  refine ⟨(faceHomogeneousEquiv (k := k) B α (p+1) yf).val,
    (faceHomogeneousEquiv (k := k) B α (p+1) yf).property, ?_⟩
  have hd : Simplicial.chainDifferential (koszulFaces_downward B α) p yf = zf :=
    Subtype.ext hy
  have he := LinearMap.congr_fun (faceHomogeneousEquiv_comm (k := k) B α p) yf
  change faceHomogeneousEquiv (k := k) B α p
      (Simplicial.chainDifferential (koszulFaces_downward B α) p yf) =
    homogeneousDifferential (k := k) B α p (faceHomogeneousEquiv (k := k) B α (p+1) yf) at he
  rw [hd] at he
  simpa only [zf, LinearEquiv.apply_symm_apply, homogeneousDifferential,
    LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] using
      (congrArg Subtype.val he).symm

/-- The ordinary degree includes the exterior factor, exactly as in the
standard graded Koszul resolution of the actual monomial ideal. -/
def ordinaryMonomialPiece (B : Family V) (q p : ℕ) :
    Submodule k (Set.powersetCard V p →₀ monomialIdeal k B) :=
  Grading.Piece (monomialCoefficientBasis (k := k) B p) (fun t => (monomialDegree t).degree) q

instance ordinaryMonomialPiece_addCommGroup (B : Family V) (q p : ℕ) :
    AddCommGroup (ordinaryMonomialPiece (k := k) B q p) :=
  Submodule.addCommGroup (R := k)
    (M := Set.powersetCard V p →₀ monomialIdeal k B) (ordinaryMonomialPiece B q p)

instance ordinaryMonomialPiece_module (B : Family V) (q p : ℕ) :
    Module k (ordinaryMonomialPiece (k := k) B q p) :=
  Submodule.module (R := k)
    (M := Set.powersetCard V p →₀ monomialIdeal k B) (ordinaryMonomialPiece B q p)

def MonomialOrdinaryExact (B : Family V) (q p : ℕ) : Prop :=
  ∀ z : Set.powersetCard V p →₀ monomialIdeal k B,
    z ∈ ordinaryMonomialPiece (k := k) B q p → monomialPreviousDifferential (k := k) B p z = 0 →
      ∃ y, y ∈ ordinaryMonomialPiece (k := k) B q (p+1) ∧ monomialDifferential (k := k) B p y = z

set_option backward.isDefEq.respectTransparency true in
theorem monomialOrdinaryExact_of_fine_exact (B : Family V) (q p : ℕ)
    (hfill : ∀ α : Exponent V, α.degree = q → Simplicial.ExactIn (k := k) (koszulFaces B α) p) :
    MonomialOrdinaryExact (k := k) B q p := by
  intro z hz hdz
  let S := ((monomialCoefficientBasis (k := k) B p).repr z).support.image monomialDegree
  have hS : ∀ α ∈ S, α.degree = q := by
    intro α hα
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
    exact ((monomialCoefficientBasis (k := k) B p).mem_span_image.mp hz) hi
  have hproj (α : Exponent V) : monomialPreviousDifferential (k := k) B p
      (homogeneousProjection (k := k) B α p z) = 0 := by
    cases p with
    | zero => rfl
    | succ p =>
        have he := LinearMap.congr_fun
          (homogeneousProjection_differential (k := k) B α p) z
        change homogeneousProjection (k := k) B α p
            (monomialDifferential (k := k) B p z) =
          monomialDifferential (k := k) B p
            (homogeneousProjection (k := k) B α (p+1) z) at he
        change monomialDifferential (k := k) B p
          (homogeneousProjection (k := k) B α (p+1) z) = 0
        rw [← he]
        change homogeneousProjection (k := k) B α p
          (monomialPreviousDifferential (k := k) B (p+1) z) = 0
        rw [hdz, map_zero]
  have hf : ∀ α ∈ S, ∃ y, y ∈ homogeneousPiece (k := k) B α (p+1) ∧
      monomialDifferential (k := k) B p y = homogeneousProjection (k := k) B α p z := by
    intro α hα
    exact monomialCoordinate_filling_of_face_exact (k := k) B α p
      (hfill α (hS α hα)) _ (homogeneousProjection_mem (k := k) B α p z) (hproj α)
  let y : Exponent V → (Set.powersetCard V (p+1) →₀ monomialIdeal k B) :=
    fun α => if hα : α ∈ S then (hf α hα).choose else 0
  have hymem : ∀ α ∈ S, y α ∈ ordinaryMonomialPiece (k := k) B q (p+1) := by
    intro α hα
    dsimp only [y]
    rw [dif_pos hα]
    apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) (hf α hα).choose_spec.1
    change monomialDegree i = α at hi
    change (monomialDegree i).degree = q
    rw [hi, hS α hα]
  have hymap : ∀ α ∈ S, monomialDifferential (k := k) B p (y α) =
      homogeneousProjection (k := k) B α p z := by
    intro α hα
    simpa only [y, dif_pos hα] using (hf α hα).choose_spec.2
  refine ⟨∑ α ∈ S, y α, Submodule.sum_mem _ (fun α hα => hymem α hα), ?_⟩
  rw [map_sum, Finset.sum_congr rfl hymap]
  exact homogeneous_decomposition (k := k) B p z

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ShiftedPolynomialFree -/
section

/-!
# The actual ordinary grading on a polynomial free module with shifts

The coefficient basis consists of monomials times the displayed free
generators. Its degree is polynomial degree plus the assigned generator
shift. A matrix coefficient support identity proves that a polynomial-linear
map preserves every actual homogeneous submodule of this grading.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.ShiftedPolynomialFree

open Classical CommAlg MvPolynomial

variable {R V I J : Type*} [CommRing R]

def expandedBasis : Module.Basis (Σ _ : I, V →₀ ℕ) R (I →₀ MvPolynomial V R) :=
  Finsupp.basis (fun _ => MvPolynomial.basisMonomials V R)

def expandedDegree (shift : I → ℕ) (a : Σ _ : I, V →₀ ℕ) : ℕ := a.2.degree + shift a.1

def piece (shift : I → ℕ) (q : ℕ) : Submodule R (I →₀ MvPolynomial V R) :=
  Grading.Piece (expandedBasis (R := R) (V := V)) (expandedDegree shift) q

@[simp] theorem expandedBasis_apply (i : I) (a : V →₀ ℕ) :
    expandedBasis (R := R) ⟨i,a⟩ = Finsupp.single i (monomial a 1) := by
  simp only [expandedBasis, Finsupp.coe_basis, MvPolynomial.coe_basisMonomials]

@[simp] theorem expandedBasis_repr (x : I →₀ MvPolynomial V R) (i : I) (a : V →₀ ℕ) :
    (expandedBasis (R := R) (V := V)).repr x ⟨i,a⟩ = (x i).coeff a := rfl

theorem mem_piece (shift : I → ℕ) (q : ℕ) (x : I →₀ MvPolynomial V R) :
    x ∈ piece shift q ↔ ∀ i a, (x i).coeff a ≠ 0 → a.degree + shift i = q := by
  rw [piece, Grading.mem_piece]
  constructor
  · intro h i a ha
    exact h ⟨i,a⟩ ha
  · intro h a ha
    exact h a.1 a.2 ha

theorem single_monomial_eq_smul (i : I) (a : V →₀ ℕ) :
    (Finsupp.single i (monomial a 1) : I →₀ MvPolynomial V R) =
      (monomial a (1 : R)) • (Finsupp.single i (1 : MvPolynomial V R)) := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

variable (shift : I → ℕ) (shift' : J → ℕ)
  (f : (I →₀ MvPolynomial V R) →ₗ[MvPolynomial V R] (J →₀ MvPolynomial V R))
  (hf : ∀ i j a, ((f (Finsupp.single i 1)) j).coeff a ≠ 0 →
    a.degree + shift' j = shift i)

include hf in
theorem map_expandedBasis (a : Σ _ : I, V →₀ ℕ) :
    f (expandedBasis (R := R) a) ∈ piece shift' (expandedDegree shift a) := by
  rw [mem_piece]
  intro j b hb
  rw [expandedBasis_apply, single_monomial_eq_smul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, MvPolynomial.coeff_monomial_mul'] at hb
  by_cases hab : a.2 ≤ b
  · rw [if_pos hab, one_mul] at hb
    have hc := hf a.1 j (b-a.2) hb
    have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le hab)
    rw [map_add] at hd
    change b.degree + shift' j = a.2.degree + shift a.1
    omega
  · rw [if_neg hab] at hb
    exact (hb rfl).elim

include hf in
/-- The matrix support condition is sufficient for genuine preservation of
all homogeneous pieces, with no field or nontriviality assumption. -/
theorem map_piece (q : ℕ) {x : I →₀ MvPolynomial V R} (hx : x ∈ piece shift q) :
    f x ∈ piece shift' q :=
  map_mem_piece_of_basis (expandedBasis (R := R) (V := V))
    (expandedBasis (R := R) (V := V)) (expandedDegree shift) (expandedDegree shift')
    (f.restrictScalars R) (map_expandedBasis shift shift' f hf) q hx

theorem augmentation_piece (L : Ideal (MvPolynomial V R))
    (ε : (I →₀ MvPolynomial V R) →ₗ[MvPolynomial V R] L)
    (hε : ∀ i, IsWeightedHomogeneous (fun _ : V => (1 : ℕ))
      (ε (Finsupp.single i 1)).val (shift i))
    (q : ℕ) {x : I →₀ MvPolynomial V R} (hx : x ∈ piece shift q) :
    IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) (ε x).val q := by
  change x ∈ Submodule.span R
    ((expandedBasis (R := R) (V := V)) '' {a | expandedDegree shift a = q}) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,ha,rfl⟩ := hx
      rw [expandedBasis_apply, single_monomial_eq_smul, map_smul]
      change IsWeightedHomogeneous (fun _ : V => (1 : ℕ))
        ((monomial a.2 1) * (ε (Finsupp.single a.1 1)).val) q
      have hm : IsWeightedHomogeneous (fun _ : V => (1 : ℕ))
          (monomial a.2 (1:R)) a.2.degree :=
        isWeightedHomogeneous_monomial _ _ _ (by rw [Finsupp.degree_eq_weight_one])
      have ht := hm.mul (hε a.1)
      change a.2.degree + shift a.1 = q at ha
      rwa [ha] at ht
  | zero =>
      rw [map_zero]
      exact isWeightedHomogeneous_zero _ _ _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact ihx.add ihy
  | smul r x hx ih =>
      rw [LinearMap.map_smul_of_tower]
      exact (weightedHomogeneousSubmodule R (fun _ : V => (1 : ℕ)) q).smul_mem r ih

end FourPapers.ShiftedPolynomialFree

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesKoszulCoordinates -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

abbrev ReesFineDegree (n : Fin d → ℕ) := ℕ × Exponent (FiniteVariable.{u} n)

lemma powerFace_one_mem (hE : finiteLatticeClosed n E) :
    (1 : Simplicial.Ambient (FiniteVariable.{u} n) k) ∈
      PowerFaceModule (E := E) (k := k) 0 0 := by
  have h := idealPowerFace_list_mul_mem (k := k) hE 0
    (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) (fun p => Fin.elim0 p)
  simpa only [List.ofFn_zero, List.prod_nil, Fin.sum_univ_zero] using h

lemma powerFace_mul_mem (hE : finiteLatticeClosed n E) (a b : ReesFineDegree.{u} n)
    (x : Simplicial.Ambient (FiniteVariable.{u} n) k)
    (hx : x ∈ PowerFaceModule (E := E) a.1 a.2)
    (y : Simplicial.Ambient (FiniteVariable.{u} n) k)
    (hy : y ∈ PowerFaceModule (E := E) b.1 b.2) :
    x * y ∈ PowerFaceModule (E := E) (a + b).1 (a + b).2 := by
  exact (idealPowerFaceMul (k := k) hE a.2 b.2 (⟨x,hx⟩ ⊗ₜ[k] ⟨y,hy⟩)).property

/-- The complete fine-degree coordinate model, with finite support in the Rees
degree and fine degree. Multiplication is exterior multiplication together with
addition of these two actual degrees. -/
def reesKoszulCoordinateAlgebra (hE : finiteLatticeClosed n E) :
    Subalgebra k (AddMonoidAlgebra (Simplicial.Ambient (FiniteVariable.{u} n) k)
      (ReesFineDegree.{u} n)) :=
  gradedCoefficientAlgebra (fun g => PowerFaceModule (E := E) (k := k) g.1 g.2)
    (powerFace_one_mem hE) (powerFace_mul_mem hE)

/-- These are the canonical subalgebra structures, named explicitly to keep
instance search from exploring commutative structures on the exterior algebra. -/
instance (priority := 1200) reesKoszulCoordinateRing (hE : finiteLatticeClosed n E) :
    Ring (reesKoszulCoordinateAlgebra (k := k) hE) :=
  Subalgebra.toRing (reesKoszulCoordinateAlgebra hE)

instance (priority := 1200) reesKoszulCoordinateAlgebraInstance (hE : finiteLatticeClosed n E) :
    Algebra k (reesKoszulCoordinateAlgebra (k := k) hE) :=
  Subalgebra.algebra (reesKoszulCoordinateAlgebra hE)

def exteriorParityDifferential {V : Type u} [Fintype V] [LinearOrder V] :
    ParityDifferential k (Simplicial.Ambient V k) where
  d := Simplicial.boundary
  parity := CliffordAlgebra.involute
  square_zero := Simplicial.boundary_boundary
  parity_square := CliffordAlgebra.involute_involute
  anticommute x := by rw [CliffordAlgebra.involute_contractLeft, neg_neg]
  map_one := CliffordAlgebra.contractLeft_one _ _
  leibniz := CliffordAlgebra.contractLeft_mul _

def reesKoszulCoordinateDifferential (hE : finiteLatticeClosed n E) :
    ParityDifferential k (reesKoszulCoordinateAlgebra (k := k) hE) :=
  (exteriorParityDifferential (V := FiniteVariable.{u} n) (k := k)).onMonoidAlgebra.restrict
    (reesKoszulCoordinateAlgebra hE)
    (by
      intro x hx g
      exact boundary_mem_basisSpan
        (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) g.1) g.2) (hx g))
    (by
      intro x hx g
      exact (totalFaceInvolute
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) g.1) g.2)
          ⟨x.coeff g, hx g⟩).property)

abbrev ReesKoszulCoordinateHomology (hE : finiteLatticeClosed n E) :=
  (reesKoszulCoordinateDifferential (k := k) hE).Homology

def reesKoszulSingle (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n) :
    PowerFaceModule (E := E) (k := k) g.1 g.2 →ₗ[k] reesKoszulCoordinateAlgebra (k := k) hE :=
  coefficientSingle (fun a : ReesFineDegree.{u} n => PowerFaceModule (E := E) (k := k) a.1 a.2)
    (powerFace_one_mem hE) (powerFace_mul_mem hE) g

def reesKoszulCoefficient (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n) :
    reesKoszulCoordinateAlgebra (k := k) hE →ₗ[k] PowerFaceModule (E := E) (k := k) g.1 g.2 :=
  coefficientAt (fun a : ReesFineDegree.{u} n => PowerFaceModule (E := E) (k := k) a.1 a.2)
    (powerFace_one_mem hE) (powerFace_mul_mem hE) g

@[simp] lemma reesKoszulSingle_val (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n)
    (x : PowerFaceModule (E := E) (k := k) g.1 g.2) :
    (reesKoszulSingle hE g x).val = AddMonoidAlgebra.single g x.val := rfl

@[simp] lemma reesKoszulCoefficient_val (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n)
    (x : reesKoszulCoordinateAlgebra (k := k) hE) :
    (reesKoszulCoefficient hE g x).val = x.val.coeff g := rfl

lemma reesKoszulSingle_differential (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n)
    (x : PowerFaceModule (E := E) (k := k) g.1 g.2) :
    (reesKoszulCoordinateDifferential (k := k) hE).d (reesKoszulSingle hE g x) =
      reesKoszulSingle hE g (powerFaceDifferential g.1 g.2 x) := by
  apply Subtype.ext
  exact (exteriorParityDifferential (V := FiniteVariable.{u} n) (k := k)).coefficientDifferential_single g x.val

lemma reesKoszulCoefficient_differential (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n)
    (x : reesKoszulCoordinateAlgebra (k := k) hE) :
    powerFaceDifferential g.1 g.2 (reesKoszulCoefficient hE g x) =
      reesKoszulCoefficient hE g ((reesKoszulCoordinateDifferential (k := k) hE).d x) := rfl

def reesCycleSingle (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n) :
    LinearMap.ker (powerFaceDifferential (E := E) (k := k) g.1 g.2) →ₗ[k]
      (reesKoszulCoordinateDifferential (k := k) hE).cycles :=
  ((reesKoszulSingle hE g).domRestrict (LinearMap.ker (powerFaceDifferential g.1 g.2))).codRestrict
    (reesKoszulCoordinateDifferential (k := k) hE).cycles.toSubmodule (by
      intro x
      change (reesKoszulCoordinateDifferential (k := k) hE).d (reesKoszulSingle hE g x.val) = 0
      rw [reesKoszulSingle_differential, show powerFaceDifferential g.1 g.2 x.val = 0 from x.property,
        map_zero])

def reesCycleCoefficient (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n) :
    (reesKoszulCoordinateDifferential (k := k) hE).cycles →ₗ[k]
      LinearMap.ker (powerFaceDifferential (E := E) (k := k) g.1 g.2) :=
  ((reesKoszulCoefficient hE g).comp
    (reesKoszulCoordinateDifferential (k := k) hE).cycles.val.toLinearMap).codRestrict _ (by
      intro x
      change powerFaceDifferential g.1 g.2 (reesKoszulCoefficient hE g x.val) = 0
      rw [reesKoszulCoefficient_differential,
        show (reesKoszulCoordinateDifferential (k := k) hE).d x.val = 0 from x.property, map_zero])

def reesHomologyPieceMap (hE : finiteLatticeClosed n E) (g : ReesFineDegree.{u} n) :
    LinearMap.ker (powerFaceDifferential (E := E) (k := k) g.1 g.2) →ₗ[k]
      ReesKoszulCoordinateHomology (k := k) hE :=
  (reesKoszulCoordinateDifferential (k := k) hE).classMap.toLinearMap.comp (reesCycleSingle hE g)

lemma reesCycle_decomposition (hE : finiteLatticeClosed n E)
    (x : (reesKoszulCoordinateDifferential (k := k) hE).cycles) :
    (∑ g ∈ x.val.val.coeff.support, reesCycleSingle hE g (reesCycleCoefficient hE g x)) = x := by
  apply Subtype.ext
  change (reesKoszulCoordinateDifferential (k := k) hE).cycles.val
    (∑ g ∈ x.val.val.coeff.support, reesCycleSingle hE g (reesCycleCoefficient hE g x)) = x.val
  rw [map_sum]
  exact coefficient_decomposition _ (powerFace_one_mem hE) (powerFace_mul_mem hE) x.val

def firstReesClasses (hE : finiteLatticeClosed n E) :
    Set (ReesKoszulCoordinateHomology (k := k) hE) :=
  {z | ∃ α : Exponent (FiniteVariable.{u} n),
    ∃ x : LinearMap.ker (powerFaceDifferential (E := E) (k := k) 1 α),
      reesHomologyPieceMap (k := k) hE (1,α) x = z}

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesCycleGeneration -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

section Ring
variable {k : Type u} [CommRing k]

lemma rees_single_list_prod (m : ℕ) (β : Fin m → Exponent (FiniteVariable.{u} n))
    (x : Fin m → Simplicial.Ambient (FiniteVariable.{u} n) k) :
    (List.ofFn (fun p => AddMonoidAlgebra.single (1, β p) (x p))).prod =
      AddMonoidAlgebra.single (m, ∑ p, β p) (List.ofFn x).prod := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Fin.sum_univ_zero, AddMonoidAlgebra.one_def]
    rfl
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, ih,
      AddMonoidAlgebra.single_mul_single]
    simp only [Prod.mk_add_mk, Nat.one_add]

lemma reesHomologyPieceMap_boundary (hE : finiteLatticeClosed n E)
    (g : ReesFineDegree.{u} n) (b : PowerFaceModule (E := E) (k := k) g.1 g.2)
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) g.1 g.2))
    (hz : powerFaceDifferential g.1 g.2 b = z.val) :
    reesHomologyPieceMap (k := k) hE g z = 0 := by
  apply (reesKoszulCoordinateDifferential (k := k) hE).classMap_eq_zero _ |>.mpr
  refine ⟨reesKoszulSingle (k := k) hE g b, ?_⟩
  rw [reesKoszulSingle_differential, hz]
  rfl

lemma reesHomologyPieceMap_product_mem (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α))
    (hz : z.val ∈ firstPowerProductCycles m α) :
    reesHomologyPieceMap (k := k) hE (m,α) z ∈ Algebra.adjoin k (firstReesClasses (k := k) hE) := by
  obtain ⟨β, x, hβ, hx, hz⟩ := hz
  let y (p : Fin m) : (reesKoszulCoordinateDifferential (k := k) hE).cycles :=
    reesCycleSingle (k := k) hE (1,β p) ⟨x p, hx p⟩
  have hprod : reesCycleSingle (k := k) hE (m,α) z = (List.ofFn y).prod := by
    apply Subtype.ext
    apply Subtype.ext
    let v := (reesKoszulCoordinateAlgebra (k := k) hE).val.comp
      (reesKoszulCoordinateDifferential (k := k) hE).cycles.val
    change AddMonoidAlgebra.single (m,α) z.val.val = v ((List.ofFn y).prod)
    rw [map_list_prod, List.map_ofFn]
    change AddMonoidAlgebra.single (m,α) z.val.val =
      (List.ofFn (fun p => AddMonoidAlgebra.single (1,β p) (x p).val)).prod
    rw [rees_single_list_prod, hβ, hz]
  change (reesKoszulCoordinateDifferential (k := k) hE).classMap (reesCycleSingle (k := k) hE (m,α) z) ∈ _
  rw [hprod, map_list_prod]
  apply (Algebra.adjoin k (firstReesClasses (k := k) hE)).list_prod_mem
  intro a ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hy
  exact Algebra.subset_adjoin ⟨β p, ⟨x p,hx p⟩, rfl⟩

/-- A proved cycle-spanning identity supplies the corresponding algebra
generation statement over an arbitrary coefficient ring. -/
lemma positive_rees_class_mem_adjoin_of_cycle_spanning (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n))
    (hspan : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α) =
      productCycleBoundarySpan m α)
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α)) :
    reesHomologyPieceMap (k := k) hE (m,α) z ∈ Algebra.adjoin k (firstReesClasses (k := k) hE) := by
  let Z := LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α)
  let S := Algebra.adjoin k (firstReesClasses (k := k) hE)
  let T : Submodule k (PowerFaceModule (E := E) (k := k) m α) :=
    (S.toSubmodule.comap (reesHomologyPieceMap (k := k) hE (m,α))).map Z.subtype
  have hproducts : Submodule.span k (firstPowerProductCycles (E := E) (k := k) m α) ≤ T := by
    apply Submodule.span_le.mpr
    intro x hx
    have hc : x ∈ Z := productCycleBoundarySpan_le_cycles m α (Submodule.mem_sup_left
      (Submodule.subset_span hx))
    exact ⟨⟨x,hc⟩, reesHomologyPieceMap_product_mem hE m α ⟨x,hc⟩ hx, rfl⟩
  have hboundaries : LinearMap.range (powerFaceDifferential (E := E) (k := k) m α) ≤ T := by
    rintro x ⟨b,rfl⟩
    have hc : powerFaceDifferential m α b ∈ Z :=
      productCycleBoundarySpan_le_cycles m α (Submodule.mem_sup_right ⟨b,rfl⟩)
    refine ⟨⟨powerFaceDifferential m α b,hc⟩, ?_, rfl⟩
    change reesHomologyPieceMap (k := k) hE (m,α) _ ∈ S
    rw [reesHomologyPieceMap_boundary hE (m,α) b _ rfl]
    exact S.zero_mem
  have hZ : Z ≤ T := by
    rw [show Z = productCycleBoundarySpan m α from hspan]
    exact sup_le hproducts hboundaries
  obtain ⟨x,hx,hxz⟩ := hZ z.property
  have heq : x = z := Subtype.ext hxz
  change reesHomologyPieceMap (k := k) hE (m,α) x ∈ S at hx
  change reesHomologyPieceMap (k := k) hE (m,α) z ∈ S
  simpa only [heq] using hx

lemma zeroPowerFace_iff (α : Exponent (FiniteVariable.{u} n)) (F : Finset (FiniteVariable.{u} n)) :
    koszulFaces (exponentPowerFamily (finiteRowFamily n E) 0) α F ↔ faceExponent F ≤ α := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h,0,by simp [exponentPowerFamily],zero_le⟩

lemma zeroPower_positive_degree_boundary (α : Exponent (FiniteVariable.{u} n)) (hα : α ≠ 0)
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) 0 α)) :
    ∃ b : PowerFaceModule (E := E) (k := k) 0 α, powerFaceDifferential 0 α b = z.val := by
  letI : DecidableEq (FiniteVariable.{u} n) :=
    (inferInstance : LinearOrder (FiniteVariable.{u} n)).toDecidableEq
  have hex : ∃ e, 0 < α e := by
    by_contra! h
    apply hα
    ext e
    exact Nat.eq_zero_of_le_zero (h e)
  obtain ⟨e,he⟩ := hex
  have hb : Simplicial.creation e z.val.val ∈ PowerFaceModule (E := E) (k := k) 0 α := by
    apply creation_mem_basisSpan e _ z.val.property
    intro F hF
    apply (zeroPowerFace_iff (E := E) α (insert e F)).mpr
    exact fullKoszulFaces_insert he ((zeroPowerFace_iff (E := E) α F).mp hF)
  refine ⟨⟨Simplicial.creation e z.val.val,hb⟩, ?_⟩
  apply Subtype.ext
  change Simplicial.boundary (Simplicial.creation e z.val.val) = z.val.val
  rw [Simplicial.boundary_creation, show Simplicial.boundary z.val.val = 0 from
    congrArg Subtype.val z.property, map_zero, sub_zero]

lemma zeroPower_zero_degree_scalar (z : PowerFaceModule (E := E) (k := k) 0 0) :
    ∃ c : k, z.val = c • (1 : Simplicial.Ambient (FiniteVariable.{u} n) k) := by
  have hz : z.val ∈ Submodule.span k ({1} : Set (Simplicial.Ambient (FiniteVariable.{u} n) k)) := by
    apply Submodule.span_le.mpr ?_ z.property
    rintro x ⟨F,hF,rfl⟩
    have hF0 : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hh := ((zeroPowerFace_iff (E := E) 0 F).mp hF) e
      simp [faceExponent_apply,he] at hh
    rw [hF0, faceBasis_empty]
    exact Submodule.subset_span (Set.mem_singleton 1)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨c,hc.symm⟩

lemma zero_rees_class_mem_adjoin (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n))
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) 0 α)) :
    reesHomologyPieceMap (k := k) hE (0,α) z ∈ Algebra.adjoin k (firstReesClasses (k := k) hE) := by
  by_cases hα : α = 0
  · subst α
    obtain ⟨c,hc⟩ := zeroPower_zero_degree_scalar (E := E) (k := k) z.val
    have hh : reesCycleSingle (k := k) hE (0,0) z = c • 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change AddMonoidAlgebra.single (0,0) z.val.val = c • 1
      rw [hc, ←AddMonoidAlgebra.smul_single]
      change c • AddMonoidAlgebra.single (0 : ReesFineDegree.{u} n) 1 = c • 1
      rw [←AddMonoidAlgebra.one_def]
    change (reesKoszulCoordinateDifferential (k := k) hE).classMap (reesCycleSingle (k := k) hE (0,0) z) ∈ _
    rw [hh,map_smul,map_one]
    exact (Algebra.adjoin k (firstReesClasses (k := k) hE)).smul_mem
      (Algebra.adjoin k (firstReesClasses (k := k) hE)).one_mem c
  · obtain ⟨b,hb⟩ := zeroPower_positive_degree_boundary (E := E) (k := k) α hα z
    have hz : reesHomologyPieceMap (k := k) hE (0,α) z=0 :=
      reesHomologyPieceMap_boundary (k := k) hE (0,α) b z hb
    rw [hz]
    exact Subalgebra.zero_mem _

/-- The cycles-modulo-actual-boundaries algebra of the complete fine-coordinate
Koszul DGA is generated by its literal Rees-degree-one homology classes. -/
theorem reesCoordinateHomology_generated_of_cycle_spanning (hE : finiteLatticeClosed n E)
    (hspan : ∀ (m : ℕ), 0 < m → ∀ α : Exponent (FiniteVariable.{u} n),
      LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α) =
        productCycleBoundarySpan m α) :
    Algebra.adjoin k (firstReesClasses (k := k) hE) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨x,rfl⟩ := (reesKoszulCoordinateDifferential (k := k) hE).classMap_surjective z
  rw [← reesCycle_decomposition (k := k) hE x, map_sum]
  apply (Algebra.adjoin k (firstReesClasses (k := k) hE)).sum_mem
  intro g hg
  change reesHomologyPieceMap (k := k) hE g (reesCycleCoefficient (k := k) hE g x) ∈ _
  obtain ⟨m,α⟩ := g
  cases m with
  | zero => exact zero_rees_class_mem_adjoin hE α _
  | succ m =>
      exact positive_rees_class_mem_adjoin_of_cycle_spanning (k := k) hE
        (m+1) (Nat.succ_pos m) α (hspan (m+1) (Nat.succ_pos m) α) _

end Ring

section Field
variable {k : Type u} [Field k]

/-- Every positive Rees-degree cycle class is generated by degree-one classes.
The full all-power cycle identity has been proved for every sublattice. -/
lemma positive_rees_class_mem_adjoin (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n))
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α)) :
    reesHomologyPieceMap (k := k) hE (m,α) z ∈
      Algebra.adjoin k (firstReesClasses (k := k) hE) :=
  positive_rees_class_mem_adjoin_of_cycle_spanning hE m hm α
    (powerFaceCycles_generated hE m hm α) z

/-- The unrestricted field assertion, with the cycle-spanning premise
discharged by the all-power proof rather than assumed by the theorem. -/
theorem reesCoordinateHomology_generated_in_degree_one (hE : finiteLatticeClosed n E) :
    Algebra.adjoin k (firstReesClasses (k := k) hE) = ⊤ :=
  reesCoordinateHomology_generated_of_cycle_spanning hE
    (fun m hm α => powerFaceCycles_generated hE m hm α)

end Field

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesTensorCoordinates -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The ordinary Koszul exterior algebra with coefficients in the actual image
of the Rees presentation inside `S[t]`. -/
abbrev ReesKoszulTensorAlgebra (E : Finset (FiniteTuple n)) (k : Type u) [CommRing k] :=
  finiteReesImage E k ⊗[k] Simplicial.Ambient (FiniteVariable.{u} n) k

instance (priority := 1200) reesKoszulTensorRing : Ring (ReesKoszulTensorAlgebra E k) :=
  Algebra.TensorProduct.instRing

instance (priority := 1200) reesKoszulTensorAlgebraInstance :
    Algebra k (ReesKoszulTensorAlgebra E k) :=
  Algebra.TensorProduct.instAlgebra

abbrev ReesTensorBasisIndex (E : Finset (FiniteTuple n)) :=
  finiteReesExponentMonoid.{u} E × Finset (FiniteVariable.{u} n)

abbrev ReesCoordinateBasisIndex (E : Finset (FiniteTuple n)) :=
  Σ g : ReesFineDegree.{u} n,
    {F : Finset (FiniteVariable.{u} n) //
      koszulFaces (exponentPowerFamily (finiteRowFamily n E) g.1) g.2 F}

lemma finiteReesFineExponent_mem (a : finiteReesExponentMonoid.{u} E) :
    Contains (exponentPowerFamily (finiteRowFamily n E) (a.val none)) (finiteReesFineExponent a) := by
  apply (finiteTarget_mem_rees_iff _ _).mp
  rw [finiteReesTarget_reconstruct]
  exact a.property

def reesTensorCoordinateIndexEquiv : ReesTensorBasisIndex.{u} E ≃ ReesCoordinateBasisIndex.{u} E where
  toFun a := ⟨(a.1.val none, finiteReesFineExponent a.1 + faceExponent a.2),
    ⟨a.2, le_add_of_nonneg_left zero_le, by
      simpa only [add_tsub_cancel_right] using finiteReesFineExponent_mem a.1⟩⟩
  invFun a := (⟨finiteTargetExponent (a.1.2 - faceExponent a.2.val) a.1.1,
    (finiteTarget_mem_rees_iff _ _).mpr a.2.property.2⟩, a.2.val)
  left_inv a := by
    apply Prod.ext
    · apply Subtype.ext
      simpa only [add_tsub_cancel_right] using finiteReesTarget_reconstruct a.1
    · rfl
  right_inv a := by
    rcases a with ⟨⟨m,α⟩,F,hF⟩
    have h : finiteReesFineExponent
        (⟨finiteTargetExponent (α-faceExponent F) m,
          (finiteTarget_mem_rees_iff _ _).mpr hF.2⟩ : finiteReesExponentMonoid.{u} E) =
          α-faceExponent F := by
      ext v
      simp [finiteReesFineExponent]
    have hα : finiteReesFineExponent
        (⟨finiteTargetExponent (α-faceExponent F) m,
          (finiteTarget_mem_rees_iff _ _).mpr hF.2⟩ : finiteReesExponentMonoid.{u} E) +
        faceExponent F = α := (congrArg (fun x => x + faceExponent F) h).trans
          (tsub_add_cancel_of_le hF.1)
    apply Sigma.subtype_ext
    · exact Prod.ext (finiteTargetExponent_none _ _) hα
    · rfl

def reesTensorBasis : Module.Basis (ReesTensorBasisIndex.{u} E) k (ReesKoszulTensorAlgebra E k) :=
  (finiteReesImageBasis E k).tensorProduct (Simplicial.basis (V := FiniteVariable.{u} n) (k := k))

def reesCoordinateBasis (hE : finiteLatticeClosed n E) :
    Module.Basis (ReesCoordinateBasisIndex.{u} E) k (reesKoszulCoordinateAlgebra (k := k) hE) :=
  gradedCoefficientBasis (fun g : ReesFineDegree.{u} n => PowerFaceModule (E := E) (k := k) g.1 g.2)
    (powerFace_one_mem hE) (powerFace_mul_mem hE)
    (fun g => totalFaceBasis (koszulFaces (exponentPowerFamily (finiteRowFamily n E) g.1) g.2))

lemma reesCoordinateBasis_val (hE : finiteLatticeClosed n E) (a : ReesCoordinateBasisIndex.{u} E) :
    (reesCoordinateBasis (k := k) hE a).val =
      AddMonoidAlgebra.single a.1 (Simplicial.basis a.2.val) := by
  rcases a with ⟨g,F⟩
  have h := congrArg Subtype.val (gradedCoefficientBasis_apply
    (fun g : ReesFineDegree.{u} n => PowerFaceModule (E := E) (k := k) g.1 g.2)
    (powerFace_one_mem hE) (powerFace_mul_mem hE)
    (fun g => totalFaceBasis (koszulFaces (exponentPowerFamily (finiteRowFamily n E) g.1) g.2))
    g F)
  simpa only [reesCoordinateBasis, reesKoszulCoordinateAlgebra,
    coefficientSingle_val, totalFaceBasis_val] using h

def reesTensorCoordinateLinearEquiv (hE : finiteLatticeClosed n E) :
    ReesKoszulTensorAlgebra E k ≃ₗ[k] reesKoszulCoordinateAlgebra (k := k) hE :=
  reesTensorBasis.equiv (reesCoordinateBasis (k := k) hE) reesTensorCoordinateIndexEquiv

lemma reesTensorCoordinateLinearEquiv_basis (hE : finiteLatticeClosed n E)
    (a : finiteReesExponentMonoid.{u} E) (F : Finset (FiniteVariable.{u} n)) :
    (reesTensorCoordinateLinearEquiv (k := k) hE
      (finiteReesImageBasis E k a ⊗ₜ[k] Simplicial.basis F)).val =
      AddMonoidAlgebra.single (a.val none,finiteReesFineExponent a + faceExponent F)
        (Simplicial.basis F) := by
  have h := Module.Basis.equiv_apply reesTensorBasis (a,F)
    (reesCoordinateBasis (k := k) hE) reesTensorCoordinateIndexEquiv
  apply_fun Subtype.val at h
  have hindex : reesTensorCoordinateIndexEquiv (a,F) =
      ⟨(a.val none,finiteReesFineExponent a + faceExponent F),
        ⟨F, le_add_of_nonneg_left zero_le, by
          simpa only [add_tsub_cancel_right] using finiteReesFineExponent_mem a⟩⟩ := rfl
  rw [reesCoordinateBasis_val, hindex] at h
  simpa only [reesTensorCoordinateLinearEquiv, reesTensorBasis,
    Module.Basis.tensorProduct_apply] using h

lemma finiteReesImageBasis_mul (a b : finiteReesExponentMonoid.{u} E) :
    finiteReesImageBasis E k a * finiteReesImageBasis E k b = finiteReesImageBasis E k (a+b) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, finiteReesImageBasis_val, MvPolynomial.monomial_mul, one_mul]
  rfl

lemma finiteReesImageBasis_zero : finiteReesImageBasis E k 0 = 1 := by
  apply Subtype.ext
  simp [finiteReesImageBasis_val]

@[simp] lemma finiteReesFineExponent_add (a b : finiteReesExponentMonoid.{u} E) :
    finiteReesFineExponent (a+b) = finiteReesFineExponent a + finiteReesFineExponent b := by
  ext v
  rfl


lemma reesTensorCoordinateLinearEquiv_mul_basis (hE : finiteLatticeClosed n E)
    (a b : ReesTensorBasisIndex.{u} E) :
    reesTensorCoordinateLinearEquiv (k := k) hE (reesTensorBasis a * reesTensorBasis b) =
      reesTensorCoordinateLinearEquiv (k := k) hE (reesTensorBasis a) *
        reesTensorCoordinateLinearEquiv (k := k) hE (reesTensorBasis b) := by
  rcases a with ⟨a,F⟩
  rcases b with ⟨b,G⟩
  simp only [reesTensorBasis, Module.Basis.tensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul, finiteReesImageBasis_mul]
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, reesTensorCoordinateLinearEquiv_basis,
    AddMonoidAlgebra.single_mul_single]
  by_cases hFG : Disjoint F G
  · rw [faceBasis_mul_of_disjoint F G hFG, TensorProduct.tmul_smul]
    erw [LinearMapClass.map_smul_of_tower (S := k)]
    rw [Subalgebra.coe_smul]
    rw [reesTensorCoordinateLinearEquiv_basis,
      ← AddMonoidAlgebra.smul_single]
    congr 2
    apply Prod.ext
    · rfl
    · rw [finiteReesFineExponent_add]
      simp only [Prod.snd_add]
      have hface := faceExponent_union_of_disjoint F G hFG
      convert (show finiteReesFineExponent a + finiteReesFineExponent b +
        (faceExponent F + faceExponent G) =
        (finiteReesFineExponent a + faceExponent F) +
        (finiteReesFineExponent b + faceExponent G) by abel) using 1
      congr 1
      convert hface using 1
      congr 1
      ext x
      simp only [Finset.mem_union]
  · rw [faceBasis_mul_of_not_disjoint F G hFG]
    simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero,
      Subalgebra.coe_zero, AddMonoidAlgebra.single_zero]

lemma reesTensorCoordinateLinearEquiv_mul (hE : finiteLatticeClosed n E)
    (x y : ReesKoszulTensorAlgebra E k) :
    reesTensorCoordinateLinearEquiv (k := k) hE (x*y) =
      reesTensorCoordinateLinearEquiv (k := k) hE x * reesTensorCoordinateLinearEquiv (k := k) hE y := by
  let f := (reesTensorCoordinateLinearEquiv (k := k) hE).toLinearMap
  have h : (LinearMap.mul k (ReesKoszulTensorAlgebra E k)).compr₂ f =
      (LinearMap.mul k (reesKoszulCoordinateAlgebra (k := k) hE)).compl₁₂ f f := by
    apply reesTensorBasis.ext
    intro a
    apply reesTensorBasis.ext
    intro b
    exact reesTensorCoordinateLinearEquiv_mul_basis (k := k) hE a b
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

lemma reesTensorCoordinateLinearEquiv_one (hE : finiteLatticeClosed n E) :
    reesTensorCoordinateLinearEquiv (k := k) hE 1 = 1 := by
  have h1 : (1 : ReesKoszulTensorAlgebra E k) =
      finiteReesImageBasis E k 0 ⊗ₜ[k] Simplicial.basis (∅ : Finset (FiniteVariable.{u} n)) := by
    rw [finiteReesImageBasis_zero, faceBasis_empty]
    rfl
  apply Subtype.ext
  rw [h1, reesTensorCoordinateLinearEquiv_basis]
  simp [finiteReesFineExponent, faceBasis_empty, AddMonoidAlgebra.one_def]
  rfl

/-- A genuine algebra equivalence from the ordinary Rees-coefficient tensor
exterior algebra to the complete fine-coordinate model. -/
def reesTensorCoordinateAlgEquiv (hE : finiteLatticeClosed n E) :
    ReesKoszulTensorAlgebra E k ≃ₐ[k] reesKoszulCoordinateAlgebra (k := k) hE :=
  AlgEquiv.ofLinearEquiv (reesTensorCoordinateLinearEquiv (k := k) hE)
    (reesTensorCoordinateLinearEquiv_one (k := k) hE) (reesTensorCoordinateLinearEquiv_mul (k := k) hE)

/-- The actual base variable as a monomial in the Rees image. -/
def finiteReesBaseIndex (E : Finset (FiniteTuple n)) (v : FiniteVariable.{u} n) :
    finiteReesExponentMonoid.{u} E :=
  ⟨Finsupp.single (some v) 1, ⟨Finsupp.single (Sum.inl v) 1, by
    simp [finiteReesExponentMap, Finsupp.weight_single, finiteReesVariableExponent]⟩⟩

def finiteReesBaseVariable (E : Finset (FiniteTuple n)) (v : FiniteVariable.{u} n) :
    finiteReesImage E k := finiteReesImageBasis E k (finiteReesBaseIndex E v)

lemma finiteReesBaseVariable_val (v : FiniteVariable.{u} n) :
    (finiteReesBaseVariable (k := k) E v).val = MvPolynomial.X (some v) := by
  rw [finiteReesBaseVariable, finiteReesImageBasis_val]
  rfl

@[simp] lemma finiteReesBaseIndex_degree (v : FiniteVariable.{u} n) :
    (finiteReesBaseIndex E v).val none = 0 := by
  simp [finiteReesBaseIndex]

@[simp] lemma finiteReesBaseIndex_fine (v : FiniteVariable.{u} n) :
    finiteReesFineExponent (finiteReesBaseIndex E v) = Finsupp.single v 1 := by
  ext x
  simp [finiteReesFineExponent,finiteReesBaseIndex,Finsupp.single_apply]

/-- The standard Koszul differential, literally the sum of multiplication by
each base variable tensored with contraction of its exterior generator. -/
def reesKoszulTensorDifferential : Module.End k (ReesKoszulTensorAlgebra E k) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k (finiteReesBaseVariable E v)) (Simplicial.contraction v)

lemma reesKoszulTensorDifferential_tmul (r : finiteReesImage E k)
    (x : Simplicial.Ambient (FiniteVariable.{u} n) k) :
    reesKoszulTensorDifferential (r ⊗ₜ[k] x) =
      ∑ v : FiniteVariable.{u} n, (finiteReesBaseVariable E v * r) ⊗ₜ[k] Simplicial.contraction v x := by
  simp [reesKoszulTensorDifferential, TensorProduct.map_tmul]


lemma reesTensorCoordinate_contraction_basis (hE : finiteLatticeClosed n E)
    (a : finiteReesExponentMonoid.{u} E) (F : Finset (FiniteVariable.{u} n))
    (v : FiniteVariable.{u} n) :
    (reesTensorCoordinateLinearEquiv (k := k) hE
      ((finiteReesBaseVariable E v * finiteReesImageBasis E k a) ⊗ₜ[k]
        Simplicial.contraction v (Simplicial.basis F))).val =
      AddMonoidAlgebra.single (a.val none,finiteReesFineExponent a + faceExponent F)
        (Simplicial.contraction v (Simplicial.basis F)) := by
  rw [finiteReesBaseVariable, finiteReesImageBasis_mul, Simplicial.contraction_basis]
  by_cases hv : v ∈ F
  · rw [if_pos hv, TensorProduct.tmul_smul]
    erw [LinearMapClass.map_smul_of_tower (S := k)]
    rw [Subalgebra.coe_smul]
    rw [reesTensorCoordinateLinearEquiv_basis,
      ←AddMonoidAlgebra.smul_single]
    congr 2
    apply Prod.ext
    · simp
    · rw [finiteReesFineExponent_add, finiteReesBaseIndex_fine]
      have hface := faceExponent_erase_add hv
      rw [←hface]
      abel
  · rw [if_neg hv]
    simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero,
      Subalgebra.coe_zero, AddMonoidAlgebra.single_zero]

/-- The coordinate equivalence intertwines the literal variable-multiplication
Koszul differential with the normalized signed exterior boundary. -/
theorem reesTensorCoordinate_intertwines (hE : finiteLatticeClosed n E)
    (x : ReesKoszulTensorAlgebra E k) :
    reesTensorCoordinateLinearEquiv (k := k) hE (reesKoszulTensorDifferential x) =
      (reesKoszulCoordinateDifferential (k := k) hE).d (reesTensorCoordinateLinearEquiv (k := k) hE x) := by
  let f := (reesTensorCoordinateLinearEquiv (k := k) hE).toLinearMap
  have h : f.comp reesKoszulTensorDifferential =
      (reesKoszulCoordinateDifferential (k := k) hE).d.comp f := by
    apply reesTensorBasis.ext
    rintro ⟨a,F⟩
    simp only [LinearMap.comp_apply,f,LinearEquiv.coe_coe,reesTensorBasis,
      Module.Basis.tensorProduct_apply]
    apply Subtype.ext
    change (reesTensorCoordinateLinearEquiv (k := k) hE
      (reesKoszulTensorDifferential (finiteReesImageBasis E k a ⊗ₜ[k] Simplicial.basis F))).val =
        (exteriorParityDifferential (V := FiniteVariable.{u} n) (k := k)).coefficientDifferential
          (reesTensorCoordinateLinearEquiv (k := k) hE
            (finiteReesImageBasis E k a ⊗ₜ[k] Simplicial.basis F)).val
    rw [reesTensorCoordinateLinearEquiv_basis, FourPapers.ParityDifferential.coefficientDifferential_single]
    rw [reesKoszulTensorDifferential_tmul]
    change ((reesKoszulCoordinateAlgebra (k := k) hE).val.toLinearMap.comp f)
        (∑ v : FiniteVariable.{u} n,
          (finiteReesBaseVariable E v * finiteReesImageBasis E k a) ⊗ₜ[k]
            Simplicial.contraction v (Simplicial.basis F)) =
      AddMonoidAlgebra.single (a.val none,finiteReesFineExponent a + faceExponent F)
        (Simplicial.boundary (Simplicial.basis F))
    rw [map_sum, Simplicial.boundary_eq_sum]
    change (∑ v : FiniteVariable.{u} n, _) =
      AddMonoidAlgebra.lsingle (R := k)
        (a.val none,finiteReesFineExponent a + faceExponent F)
        (∑ v : FiniteVariable.{u} n, Simplicial.contraction v (Simplicial.basis F))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro v _
    exact reesTensorCoordinate_contraction_basis hE a F v
  exact LinearMap.congr_fun h x

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphParameterGroebner -/
section

/-! # The literal one-parameter closed-graph ideal

The coefficients of the family are powers of a single parameter. Its two
nontrivial types of S-pairs have one-term standard representations. This
proves the monic Gröbner-basis assertion over the coefficient domain itself;
in particular it applies directly to `ℤ[z]`.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.MonicBinomialBuchberger
open Classical MvPolynomial
variable {V R : Type*} [CommRing R] [IsDomain R] (m : MonomialOrder V)
variable {G : Set (MvPolynomial V R)}

lemma weightedBinomial_degree {a b : V →₀ ℕ} {c : R}
    (hab : m.toSyn b < m.toSyn a) (hc : c ≠ 0) :
    m.degree (monomial a (1 : R) - monomial b c) = a := by
  have h' : m.toSyn (m.degree (monomial b c)) <
      m.toSyn (m.degree (monomial a (1 : R))) := by
    simpa only [m.degree_monomial, if_neg hc, if_neg one_ne_zero] using hab
  rw [m.degree_sub_of_lt h', m.degree_monomial, if_neg one_ne_zero]

lemma weightedBinomial_leadingCoeff {a b : V →₀ ℕ} {c : R}
    (hab : m.toSyn b < m.toSyn a) (hc : c ≠ 0) :
    m.leadingCoeff (monomial a (1 : R) - monomial b c) = 1 := by
  have h' : m.toSyn (m.degree (monomial b c)) <
      m.toSyn (m.degree (monomial a (1 : R))) := by
    simpa only [m.degree_monomial, if_neg hc, if_neg one_ne_zero] using hab
  rw [m.leadingCoeff_sub_of_lt h', m.leadingCoeff_monomial]

lemma weightedBinomial_ne_zero {a b : V →₀ ℕ} {c : R}
    (hab : m.toSyn b < m.toSyn a) (hc : c ≠ 0) :
    monomial a (1 : R) - monomial b c ≠ 0 := by
  intro hz
  have hh := weightedBinomial_leadingCoeff m hab hc
  rw [hz, m.leadingCoeff_zero] at hh
  exact zero_ne_one hh

/-- The coprime S-pair calculation with the actual coefficient multipliers,
including the case when the two remaining exponents agree. -/
theorem coprime_weightedBinomial_pair {a b c d : V →₀ ℕ} {r s : R}
    (hab : m.toSyn b < m.toSyn a) (hcd : m.toSyn d < m.toSyn c)
    (hr : r ≠ 0) (hs : s ≠ 0) (hac : a ⊔ c = a + c)
    (hf : monomial a (1 : R) - monomial b r ∈ G)
    (hg : monomial c (1 : R) - monomial d s ∈ G) :
    m.IsRemainder
      (m.sPolynomial (monomial a (1 : R) - monomial b r)
        (monomial c 1 - monomial d s)) G 0 := by
  let f : MvPolynomial V R := monomial a 1 - monomial b r
  let g : MvPolynomial V R := monomial c 1 - monomial d s
  by_cases hfg : f = g
  · rw [show monomial a (1 : R) - monomial b r = g from hfg, m.sPolynomial_self]
    exact MonomialOrder.isRemainder_zero_left_iff.mpr rfl
  have hfa : m.degree f = a := weightedBinomial_degree m hab hr
  have hgc : m.degree g = c := weightedBinomial_degree m hcd hs
  have hfl : m.leadingCoeff f = 1 := weightedBinomial_leadingCoeff m hab hr
  have hgl : m.leadingCoeff g = 1 := weightedBinomial_leadingCoeff m hcd hs
  have hsp : m.sPolynomial f g = monomial (a + d) s - monomial (c + b) r := by
    rw [m.sPolynomial_def, hfa, hgc, hfl, hgl, hac,
      add_tsub_cancel_left, add_tsub_cancel_right]
    dsimp only [f, g]
    simp only [mul_sub, monomial_mul_monomial, one_mul, mul_one]
    rw [add_comm c a]
    abel
  by_cases hz : m.sPolynomial f g = 0
  · rw [show m.sPolynomial (monomial a (1 : R) - monomial b r)
      (monomial c 1 - monomial d s) = 0 from hz]
    exact MonomialOrder.isRemainder_zero_left_iff.mpr rfl
  have hbounds : m.toSyn (a + d) ≤ m.toSyn (m.degree (m.sPolynomial f g)) ∧
      m.toSyn (c + b) ≤ m.toSyn (m.degree (m.sPolynomial f g)) := by
    by_cases he : a + d = c + b
    · have hsp' : m.sPolynomial f g = monomial (a + d) (s - r) := by
        rw [hsp, ← he, map_sub]
      have hsr : s - r ≠ 0 := by
        intro hzero
        exact hz (by rw [hsp', hzero, map_zero])
      rw [hsp', m.degree_monomial, if_neg hsr, ← he]
      exact ⟨le_rfl, le_rfl⟩
    · constructor
      · apply m.le_degree
        rw [mem_support_iff, hsp]
        simpa [coeff_sub, coeff_monomial, he, Ne.symm he] using hs
      · apply m.le_degree
        rw [mem_support_iff, hsp]
        simpa [coeff_sub, coeff_monomial, he, Ne.symm he] using neg_ne_zero.mpr hr
  apply two_products m f g (monomial d s) (-monomial b r)
    (m.sPolynomial f g) hf hg hfg
  · rw [hsp]
    dsimp only [f, g]
    simp only [mul_sub, neg_mul, monomial_mul_monomial, mul_one]
    rw [add_comm d a, add_comm b c, add_comm d b, mul_comm s r]
    ring
  · apply (MonomialOrder.toWithBotSyn_withBotDegree_add_le_iff
      (weightedBinomial_ne_zero m hab hr) (by simpa using hs) hz).mpr
    simpa only [weightedBinomial_degree m hab hr, m.degree_monomial, if_neg hs,
      ← map_add] using hbounds.1
  · apply (MonomialOrder.toWithBotSyn_withBotDegree_add_le_iff
      (weightedBinomial_ne_zero m hcd hs) (by simpa using hr) hz).mpr
    simpa only [weightedBinomial_degree m hcd hs, m.degree_neg, m.degree_monomial,
      if_neg hr, ← map_add] using hbounds.2

end FourPapers.MonicBinomialBuchberger

namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {N : ℕ} {R : Type u} [CommRing R] [IsDomain R]

def graphParameterBinomial (t : R) (i j : Fin N) :
    MvPolynomial (FiniteVariable.{u} (GraphRows N)) R :=
  monomial (graphPairExponent i j) 1 -
    monomial (graphPairExponent j i) (t ^ (j.val - i.val))

lemma graphParameterBinomial_variables (t : R) (i j : Fin N) :
    graphParameterBinomial t i j =
      X ⟨0, ULift.up i⟩ * X ⟨1, ULift.up j⟩ -
        C (t ^ (j.val - i.val)) * X ⟨0, ULift.up j⟩ * X ⟨1, ULift.up i⟩ := by
  simp only [graphParameterBinomial, graphPairExponent, X, C_apply,
    monomial_mul_monomial, zero_add, one_mul, mul_one]

lemma graphParameterBinomial_degree (t : R) (ht : t ≠ 0) {i j : Fin N} (hij : i < j) :
    graphLexOrder.degree (graphParameterBinomial t i j) = graphPairExponent i j :=
  MonicBinomialBuchberger.weightedBinomial_degree graphLexOrder
    (graphPairExponent_order hij) (pow_ne_zero _ ht)

lemma graphParameterBinomial_leadingCoeff (t : R) (ht : t ≠ 0)
    {i j : Fin N} (hij : i < j) :
    graphLexOrder.leadingCoeff (graphParameterBinomial t i j) = 1 :=
  MonicBinomialBuchberger.weightedBinomial_leadingCoeff graphLexOrder
    (graphPairExponent_order hij) (pow_ne_zero _ ht)

lemma graphParameterBinomial_ne_zero (t : R) (ht : t ≠ 0)
    {i j : Fin N} (hij : i < j) :
    graphParameterBinomial t i j ≠ 0 :=
  MonicBinomialBuchberger.weightedBinomial_ne_zero graphLexOrder
    (graphPairExponent_order hij) (pow_ne_zero _ ht)

def graphParameterGenerators (t : R) (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) R) :=
  {f | ∃ i j, i < j ∧ G.Adj i j ∧ f = graphParameterBinomial t i j}

def graphParameterIdeal (t : R) (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) R) :=
  Ideal.span (graphParameterGenerators t G)

lemma graphParameterBinomial_mem (t : R) {G : SimpleGraph (Fin N)} {i j : Fin N}
    (hij : i < j) (hG : G.Adj i j) :
    graphParameterBinomial t i j ∈ graphParameterGenerators t G :=
  ⟨i, j, hij, hG, rfl⟩

lemma graphParameter_sPolynomial_same_first (t : R) (ht : t ≠ 0)
    (i j l : Fin N) (hij : i < j) (hjl : j < l) :
    graphLexOrder.sPolynomial (graphParameterBinomial t i j)
      (graphParameterBinomial t i l) =
      -(C (t ^ (j.val - i.val)) * X ⟨1, ULift.up i⟩) * graphParameterBinomial t j l := by
  rw [MonomialOrder.sPolynomial, graphParameterBinomial_degree t ht hij,
    graphParameterBinomial_degree t ht (hij.trans hjl),
    graphParameterBinomial_leadingCoeff t ht hij,
    graphParameterBinomial_leadingCoeff t ht (hij.trans hjl),
    graphPairExponent_sub_same_first i j l hjl.ne,
    graphPairExponent_sub_same_first i l j hjl.ne.symm]
  change X ⟨1, ULift.up l⟩ * graphParameterBinomial t i j -
    X ⟨1, ULift.up j⟩ * graphParameterBinomial t i l = _
  have hexp : l.val - i.val = (j.val - i.val) + (l.val - j.val) := by omega
  simp only [graphParameterBinomial_variables, hexp, pow_add, map_mul]
  ring

lemma graphParameter_sPolynomial_same_last (t : R) (ht : t ≠ 0)
    (i h j : Fin N) (hih : i < h) (hhj : h < j) :
    graphLexOrder.sPolynomial (graphParameterBinomial t i j)
      (graphParameterBinomial t h j) =
      (C (t ^ (j.val - h.val)) * X ⟨0, ULift.up j⟩) * graphParameterBinomial t i h := by
  rw [MonomialOrder.sPolynomial, graphParameterBinomial_degree t ht (hih.trans hhj),
    graphParameterBinomial_degree t ht hhj,
    graphParameterBinomial_leadingCoeff t ht (hih.trans hhj),
    graphParameterBinomial_leadingCoeff t ht hhj,
    graphPairExponent_sub_same_last i h j hih.ne,
    graphPairExponent_sub_same_last h i j hih.ne.symm]
  change X ⟨0, ULift.up h⟩ * graphParameterBinomial t i j -
    X ⟨0, ULift.up i⟩ * graphParameterBinomial t h j = _
  have hexp : j.val - i.val = (j.val - h.val) + (h.val - i.val) := by omega
  simp only [graphParameterBinomial_variables, hexp, pow_add, map_mul]
  ring

theorem closedGraph_parameter_groebner (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : ClosedLabeling G) :
    graphLexOrder.IsGroebnerBasis (graphParameterGenerators t G) (graphParameterIdeal t G) := by
  apply MonomialOrder.isGroebnerBasis_span_of_isRemainder_sPolynomial_zero
  · rintro _ ⟨i, j, hij, _, rfl⟩ _
    rw [graphParameterBinomial_leadingCoeff t ht hij]
    exact isUnit_one
  · rintro _ ⟨i, j, hij, hijG, rfl⟩ _ ⟨h, l, hhl, hhlG, rfl⟩
    by_cases hih : i = h
    · subst h
      by_cases hjl : j = l
      · subst l
        rw [MonomialOrder.sPolynomial_self]
        exact MonomialOrder.isRemainder_zero_left_iff.mpr rfl
      · have hjlG := hG.1 hij hhl hjl hijG hhlG
        rcases lt_or_gt_of_ne hjl with hjl' | hlj'
        · rw [graphParameter_sPolynomial_same_first t ht i j l hij hjl']
          exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphParameterBinomial_mem t hjl' hjlG)
        · rw [graphLexOrder.sPolynomial_antisymm (graphParameterBinomial t i j)
            (graphParameterBinomial t i l),
            graphParameter_sPolynomial_same_first t ht i l j hhl hlj',
            neg_mul, neg_neg]
          exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphParameterBinomial_mem t hlj' hjlG.symm)
    · by_cases hjl : j = l
      · subst l
        have hihG := hG.2 hij hhl hih hijG hhlG
        rcases lt_or_gt_of_ne hih with hih' | hhi'
        · rw [graphParameter_sPolynomial_same_last t ht i h j hih' hhl]
          exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphParameterBinomial_mem t hih' hihG)
        · rw [graphLexOrder.sPolynomial_antisymm (graphParameterBinomial t i j)
            (graphParameterBinomial t h j),
            graphParameter_sPolynomial_same_last t ht h i j hhi' hij, ← neg_mul]
          exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphParameterBinomial_mem t hhi' hihG.symm)
      · exact MonicBinomialBuchberger.coprime_weightedBinomial_pair graphLexOrder
          (graphPairExponent_order hij) (graphPairExponent_order hhl)
          (pow_ne_zero _ ht) (pow_ne_zero _ ht)
          (graphPairExponent_sup_disjoint i j h l hih hjl)
          (graphParameterBinomial_mem t hij hijG) (graphParameterBinomial_mem t hhl hhlG)

/-- In particular, the displayed family in Theorem 9.1 has a monic Gröbner
basis over its literal parameter ring `ℤ[z]`. -/
theorem closedGraph_integral_parameter_groebner {G : SimpleGraph (Fin N)}
    (hG : ClosedLabeling G) :
    graphLexOrder.IsGroebnerBasis (graphParameterGenerators (Polynomial.X : Polynomial ℤ) G)
      (graphParameterIdeal (Polynomial.X : Polynomial ℤ) G) :=
  closedGraph_parameter_groebner _ Polynomial.X_ne_zero hG

theorem graphParameterGenerators_unit_leading (t : R) (ht : t ≠ 0)
    (G : SimpleGraph (Fin N)) :
    ∀ g ∈ graphParameterGenerators t G, g ≠ 0 → IsUnit (graphLexOrder.leadingCoeff g) := by
  rintro _ ⟨i, j, hij, _, rfl⟩ _
  rw [graphParameterBinomial_leadingCoeff t ht hij]
  exact isUnit_one

theorem closedGraph_parameter_standardMonomials (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : ClosedLabeling G)
    (a : Exponent (FiniteVariable.{u} (GraphRows N))) :
    a ∈ graphLexOrder.standardMonomials (graphParameterIdeal t G) ↔
      ¬CommAlg.Polymatroid.Contains (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) a := by
  rw [(closedGraph_parameter_groebner t ht hG).mem_standardMonomials_iff]
  constructor
  · intro h hc
    rcases hc with ⟨b, hb, hba⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    rcases (mem_graphEdgeLattice G e).mp he with ⟨helt, heG⟩
    apply h _ (graphParameterBinomial_mem t helt heG) (graphParameterBinomial_ne_zero t ht helt)
    rw [graphParameterBinomial_degree t ht helt, graphPairExponent_eq_row, graphTuple_eta]
    exact hba
  · rintro h _ ⟨i, j, hij, hijG, rfl⟩ _ hle
    apply h
    refine ⟨finiteRowExponent (GraphRows N) (graphTuple i j), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨graphTuple i j, ?_, rfl⟩
      apply (mem_graphEdgeLattice G _).mpr
      simpa only [graphTuple_zero, graphTuple_one] using And.intro hij hijG
    · rw [graphParameterBinomial_degree t ht hij, graphPairExponent_eq_row] at hle
      exact hle

theorem graphParameterGenerators_weight_tails (t : R) (ht : t ≠ 0)
    (G : SimpleGraph (Fin N)) :
    ∀ g ∈ graphParameterGenerators t G, g ≠ 0 →
      ∀ a ∈ (monomial (graphLexOrder.degree g) 1 - g).support,
        Finsupp.weight graphDiagonalWeight a <
          Finsupp.weight graphDiagonalWeight (graphLexOrder.degree g) := by
  rintro _ ⟨i, j, hij, _, rfl⟩ _ a ha
  rw [graphParameterBinomial_degree t ht hij] at ha ⊢
  have htail : monomial (graphPairExponent i j) (1 : R) - graphParameterBinomial t i j =
      monomial (graphPairExponent j i) (t ^ (j.val - i.val)) := by
    unfold graphParameterBinomial
    abel
  rw [htail, support_monomial, if_neg (pow_ne_zero _ ht), Finset.mem_singleton] at ha
  subst a
  rw [graphPairExponent_weight, graphPairExponent_weight]
  have hj := j.isLt
  have hi : i.val < j.val := hij
  omega

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem graphParameterIdeal_vertexRow_homogeneous (t : R) (G : SimpleGraph (Fin N)) :
    (graphParameterIdeal t G).IsHomogeneous
      (weightedHomogeneousSubmodule R graphVertexRowDegree) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i, j, _, _, rfl⟩
  refine ⟨Finsupp.weight graphVertexRowDegree (graphPairExponent i j), ?_⟩
  exact (isWeightedHomogeneous_monomial graphVertexRowDegree
    (graphPairExponent i j) (1 : R) rfl).sub
      (isWeightedHomogeneous_monomial graphVertexRowDegree
        (graphPairExponent j i) (t ^ (j.val - i.val))
        (graphPairExponent_vertexRowDegree i j).symm)

@[simp] theorem graphParameterBinomial_one (i j : Fin N) :
    graphParameterBinomial (1 : R) i j = graphBinomial i j := by
  simp [graphParameterBinomial, graphBinomial]

@[simp] theorem graphParameterIdeal_one (G : SimpleGraph (Fin N)) :
    graphParameterIdeal (1 : R) G = graphBinomialIdeal G := by
  simp only [graphParameterIdeal, graphParameterGenerators, graphBinomialIdeal,
    graphBinomialGenerators, graphParameterBinomial_one]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphParameterIdeal -/
section

/-! # Initial ideal and ordinary grading of the graph parameter family

These first-power ideal identities are independent of the all-power integral
Gröbner-basis construction. They retain the actual polynomial ideal, the original
monomial order, and every ordinary degree.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section

namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ} {R : Type u} [CommRing R] [IsDomain R]

theorem graphParameter_initialIdeal (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : ClosedLabeling G) :
    FourPapers.initialIdeal graphLexOrder (graphParameterIdeal t G) =
      finiteSublatticeIdeal (GraphRows N) (k := R) (graphEdgeLattice G) := by
  rw [FourPapers.initialIdeal, (closedGraph_parameter_groebner t ht hG).span_leadingTerm_image,
    finiteSublatticeIdeal]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, j, hij, hijG, rfl⟩, rfl⟩
    refine ⟨graphTuple i j, ?_, ?_⟩
    · exact (mem_graphEdgeLattice G _).mpr
        (by simpa only [graphTuple_zero, graphTuple_one] using And.intro hij hijG)
    · rw [finiteRowMonomial_eq_monomial, MonomialOrder.leadingTerm,
        graphParameterBinomial_degree t ht hij, graphParameterBinomial_leadingCoeff t ht hij,
        graphPairExponent_eq_row]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨hij, hijG⟩ := (mem_graphEdgeLattice G a).mp ha
    refine ⟨graphParameterBinomial t (a 0) (a 1), graphParameterBinomial_mem t hij hijG, ?_⟩
    rw [MonomialOrder.leadingTerm, graphParameterBinomial_degree t ht hij,
      graphParameterBinomial_leadingCoeff t ht hij, finiteRowMonomial_eq_monomial,
      graphPairExponent_eq_row, graphTuple_eta]

theorem graphParameterIdeal_ordinary_homogeneous (t : R) (G : SimpleGraph (Fin N)) :
    (graphParameterIdeal t G).IsHomogeneous
      (weightedHomogeneousSubmodule R (fun _ : FiniteVariable (GraphRows N) => (1 : ℕ))) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i, j, _, _, rfl⟩
  refine ⟨2, ?_⟩
  apply IsWeightedHomogeneous.sub
  · apply isWeightedHomogeneous_monomial
    simp [graphPairExponent, Finsupp.weight_single]
  · apply isWeightedHomogeneous_monomial
    simp [graphPairExponent, Finsupp.weight_single]

theorem graphParameterPower_ordinary_homogeneous (t : R)
    (G : SimpleGraph (Fin N)) (s : ℕ) :
    (graphParameterIdeal t G ^ s).IsHomogeneous
      (weightedHomogeneousSubmodule R (fun _ : FiniteVariable (GraphRows N) => (1 : ℕ))) := by
  induction s with
  | zero =>
      simpa only [pow_zero, Ideal.one_eq_top] using
        (Ideal.IsHomogeneous.top
          (weightedHomogeneousSubmodule R (fun _ : FiniteVariable (GraphRows N) => (1 : ℕ))))
  | succ s ih =>
      rw [pow_succ]
      exact ih.mul (graphParameterIdeal_ordinary_homogeneous t G)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CanonicalQuotientGroebnerData -/
section

/-! # Canonical coordinate data for an arbitrary ideal over a field

The coordinate basis uses the ideal itself as its Gröbner basis. A finite
Gröbner basis, whose existence follows from the Hilbert basis theorem, is
used only to give the monomial family the finite presentation required by
the existing coordinate API. No Gröbner-basis condition is assumed.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid MvPolynomial

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))

def canonicalFiniteGroebnerBasis : Finset (MvPolynomial V K) :=
  Classical.choose (m.exists_finset_isGroebnerBasis J)

theorem canonicalFiniteGroebnerBasis_spec :
    m.IsGroebnerBasis (canonicalFiniteGroebnerBasis m J) J :=
  Classical.choose_spec (m.exists_finset_isGroebnerBasis J)

def canonicalInitialFamily : Family V :=
  ((canonicalFiniteGroebnerBasis m J).erase 0).image m.degree

theorem canonicalInitialFamily_standard (a : V →₀ ℕ) :
    a ∈ m.standardMonomials J ↔ QuotientAllowed (canonicalInitialFamily m J) a := by
  rw [(canonicalFiniteGroebnerBasis_spec m J).mem_standardMonomials_iff]
  simp only [QuotientAllowed,Contains,canonicalInitialFamily,
    Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ha ⟨b,⟨f,⟨hf0,hf⟩,rfl⟩,hba⟩
    exact ha f hf hf0 hba
  · intro ha f hf hf0 hfa
    exact ha ⟨m.degree f,⟨f,⟨hf0,hf⟩,rfl⟩,hfa⟩

/-- Exact Gröbner coordinate data for every ideal over every field, for an
arbitrary original monomial order. All proof fields are constructed. -/
def canonicalQuotientGroebnerData : QuotientGroebnerData V K where
  order := m
  ideal := J
  generators := J
  groebner := m.isGroebnerBasis_self J
  unitLeading := fun f _ hf => m.isUnit_leadingCoeff.mpr hf
  family := canonicalInitialFamily m J
  standard := canonicalInitialFamily_standard m J

@[simp] theorem canonicalQuotientGroebnerData_ideal :
    (canonicalQuotientGroebnerData m J).ideal = J := rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedHomologyDecomposition -/
section

/-! # Total homology is the direct sum of its homogeneous homology groups

All cycles and boundaries are literal kernels and images. Homogeneity of
cycles and boundaries is enough for the construction; a differential that
shifts a grading has both properties. No homology splitting is assumed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.GradedHomologyDecomposition

open Classical DirectSum FilteredHomology
open scoped BigOperators

variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq I]
  (P : I → Submodule K M) [DirectSum.Decomposition P]
  (d : Module.End K M) (hdd : d.comp d = 0)

abbrev degreeCycles (i : I) : Submodule K (LinearMap.ker d) :=
  (P i).comap (LinearMap.ker d).subtype

abbrev totalBoundaries : Submodule K (LinearMap.ker d) :=
  LinearMap.range (boundaryMap d d hdd)

abbrev degreeBoundaries (i : I) : Submodule K (degreeCycles P d i) :=
  (totalBoundaries d hdd).comap (degreeCycles P d i).subtype

abbrev DegreeHomology (i : I) := degreeCycles P d i ⧸ degreeBoundaries P d hdd i

instance degreeCyclesAddCommGroup (i : I) : AddCommGroup (degreeCycles P d i) :=
  Submodule.addCommGroup (R := K) (M := LinearMap.ker d) (degreeCycles P d i)

instance degreeCyclesModule (i : I) : Module K (degreeCycles P d i) :=
  Submodule.module (R := K) (M := LinearMap.ker d) (degreeCycles P d i)

instance degreeHomologyAddCommGroup (i : I) : AddCommGroup (DegreeHomology P d hdd i) :=
  Submodule.Quotient.addCommGroup (R := K) (M := degreeCycles P d i) (degreeBoundaries P d hdd i)

instance degreeHomologyModule (i : I) : Module K (DegreeHomology P d hdd i) :=
  Submodule.Quotient.module (R := K) (M := degreeCycles P d i) (degreeBoundaries P d hdd i)

theorem mem_totalBoundaries (x : LinearMap.ker d) :
    x ∈ totalBoundaries d hdd ↔ x.val ∈ LinearMap.range d := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

variable
  (hcycles : ∀ i x, d x = 0 → d (DirectSum.decompose P x i).val = 0)
  (hboundaries : ∀ i x, x ∈ LinearMap.range d →
    (DirectSum.decompose P x i).val ∈ LinearMap.range d)

def cycleDecomposition : LinearMap.ker d →ₗ[K] ⨁ i, degreeCycles P d i where
  toFun x :=
    { toFun := fun i =>
        ⟨⟨(DirectSum.decompose P x.val i).val, hcycles i x.val x.property⟩,
          (DirectSum.decompose P x.val i).property⟩
      support' := Trunc.mk ⟨(DirectSum.decompose P x.val).support.val, by
        intro i
        by_cases hi : i ∈ (DirectSum.decompose P x.val).support
        · exact Or.inl hi
        · right
          apply Subtype.ext
          apply Subtype.ext
          change (DirectSum.decompose P x.val i).val = 0
          exact congrArg (fun z : P i => z.val) ((DFinsupp.notMem_support_iff (f := DirectSum.decompose P x.val) (i := i)).mp hi)⟩ }
  map_add' x y := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (DirectSum.decompose P (x.val + y.val) i).val =
      (DirectSum.decompose P x.val i).val + (DirectSum.decompose P y.val i).val
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  map_smul' r x := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (DirectSum.decompose P (r • x.val) i).val =
      r • (DirectSum.decompose P x.val i).val
    simp only [DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]

@[simp] theorem cycleDecomposition_apply (x : LinearMap.ker d) (i : I) :
    ((cycleDecomposition P d hcycles x i).val).val =
      (DirectSum.decompose P x.val i).val := rfl

theorem cycleDecomposition_homogeneous (i : I) (x : degreeCycles P d i) :
    cycleDecomposition P d hcycles x.val = DirectSum.of (fun j => degreeCycles P d j) i x := by
  apply DFinsupp.ext
  intro j
  apply Subtype.ext
  apply Subtype.ext
  by_cases hij : i = j
  · subst j
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same P x.property
  · rw [DirectSum.of_eq_of_ne (β := fun j => degreeCycles P d j) i j x (Ne.symm hij)]
    exact DirectSum.decompose_of_mem_ne P x.property hij

def classDecomposition : LinearMap.ker d →ₗ[K] ⨁ i, DegreeHomology P d hdd i :=
  (DirectSum.lmap (fun i => (degreeBoundaries P d hdd i).mkQ)).comp
    (cycleDecomposition P d hcycles)

@[simp] theorem classDecomposition_apply (x : LinearMap.ker d) (i : I) :
    classDecomposition P d hdd hcycles x i =
      (degreeBoundaries P d hdd i).mkQ (cycleDecomposition P d hcycles x i) := rfl

theorem classDecomposition_homogeneous (i : I) (x : degreeCycles P d i) :
    classDecomposition P d hdd hcycles x.val =
      DirectSum.of (fun j => DegreeHomology P d hdd j) i
        ((degreeBoundaries P d hdd i).mkQ x) := by
  simp only [classDecomposition, LinearMap.comp_apply, cycleDecomposition_homogeneous,
    DirectSum.lmap_of]

theorem classDecomposition_surjective :
    Function.Surjective (classDecomposition P d hdd hcycles) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of i x =>
      obtain ⟨x, rfl⟩ := (degreeBoundaries P d hdd i).mkQ_surjective x
      exact ⟨x.val, classDecomposition_homogeneous P d hdd hcycles i x⟩
  | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩

include hboundaries in
theorem classDecomposition_ker :
    LinearMap.ker (classDecomposition P d hdd hcycles) = totalBoundaries d hdd := by
  ext x
  rw [LinearMap.mem_ker, mem_totalBoundaries]
  constructor
  · intro hx
    have hpieces (i : I) : (DirectSum.decompose P x.val i).val ∈ LinearMap.range d := by
      have hi := congrArg (fun a : ⨁ i, DegreeHomology P d hdd i => a i) hx
      change (degreeBoundaries P d hdd i).mkQ (cycleDecomposition P d hcycles x i) = 0 at hi
      have hb := (Submodule.Quotient.mk_eq_zero (degreeBoundaries P d hdd i)).mp hi
      exact (mem_totalBoundaries d hdd _).mp hb
    rw [← DirectSum.sum_support_decompose P x.val]
    exact (LinearMap.range d).sum_mem (fun i _ => hpieces i)
  · intro hx
    apply DFinsupp.ext
    intro i
    change (degreeBoundaries P d hdd i).mkQ (cycleDecomposition P d hcycles x i) = 0
    apply (Submodule.Quotient.mk_eq_zero (degreeBoundaries P d hdd i)).mpr
    exact (mem_totalBoundaries d hdd _).mpr (hboundaries i x.val hx)

attribute [local irreducible] classDecomposition cycleDecomposition

set_option maxHeartbeats 150000 in
set_option diagnostics true in
/-- The canonical equivalence sends a cycle class to the classes of its
actual homogeneous projections. -/
def homologyDecomposition :
    Homology d d hdd ≃ₗ[K] ⨁ i, DegreeHomology P d hdd i := by
  let f : LinearMap.ker d →ₗ[K] (⨁ i, DegreeHomology P d hdd i) :=
    classDecomposition P d hdd hcycles
  have hk : LinearMap.ker f = totalBoundaries d hdd :=
    classDecomposition_ker P d hdd hcycles hboundaries
  let F : Homology d d hdd →ₗ[K] (⨁ i, DegreeHomology P d hdd i) :=
    (totalBoundaries d hdd).liftQ (R := K) (R₂ := K)
      (M := LinearMap.ker d) (M₂ := ⨁ i, DegreeHomology P d hdd i)
      (τ₁₂ := RingHom.id K) f hk.ge
  apply LinearEquiv.ofBijective F
  constructor
  · exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (totalBoundaries d hdd) f hk.ge hk.le)
  · intro y
    obtain ⟨x, rfl⟩ := classDecomposition_surjective P d hdd hcycles y
    exact ⟨homologyClass d d hdd x, rfl⟩

@[simp] theorem homologyDecomposition_class (x : LinearMap.ker d) :
    homologyDecomposition P d hdd hcycles hboundaries (homologyClass d d hdd x) =
      classDecomposition P d hdd hcycles x := rfl

section Dimension

variable [Fintype I] [StrongRankCondition K] [Module.Free K (Homology d d hdd)]
  [∀ i, Module.Free K (DegreeHomology P d hdd i)]
  [∀ i, Module.Finite K (DegreeHomology P d hdd i)]

include hcycles hboundaries in
theorem finrank_homology_eq_sum :
    Module.finrank K (Homology d d hdd) = ∑ i, Module.finrank K (DegreeHomology P d hdd i) := by
  rw [(homologyDecomposition P d hdd hcycles hboundaries).finrank_eq,
    Module.finrank_directSum]

end Dimension

section IndividualGroup

variable {X : Type*} [AddCommGroup X] [Module K X]
  (i : I) (f : X →ₗ[K] P i)
  (hfd : (d.domRestrict (P i)).comp f = 0)

def degreeCyclesEquiv : LinearMap.ker (d.domRestrict (P i)) ≃ₗ[K] degreeCycles P d i where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem degreeCyclesEquiv_boundaries
    (hf : ∀ y : X, (f y).val ∈ LinearMap.range d)
    (hfill : ∀ x : M, d x ∈ P i → ∃ y : X, (f y).val = d x) :
    (LinearMap.range (boundaryMap f (d.domRestrict (P i)) hfd)).map
        (degreeCyclesEquiv P d i).toLinearMap = degreeBoundaries P d hdd i := by
  ext z
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    apply (mem_totalBoundaries d hdd _).mpr
    exact hf a
  · intro hz
    obtain ⟨a, ha⟩ := (mem_totalBoundaries d hdd z.val).mp hz
    obtain ⟨b, hb⟩ := hfill a (by
      rw [ha]
      exact z.property)
    refine ⟨boundaryMap f (d.domRestrict (P i)) hfd b, ⟨b, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hb.trans ha

/-- Identification with the usual three-term homology in an individual
degree. The incoming map is required to be an actual differential, and every
ambient boundary in this degree has a homogeneous preimage. -/
def degreeHomologyEquiv
    (hf : ∀ y : X, (f y).val ∈ LinearMap.range d)
    (hfill : ∀ x : M, d x ∈ P i → ∃ y : X, (f y).val = d x) :
    Homology f (d.domRestrict (P i)) hfd ≃ₗ[K] DegreeHomology P d hdd i :=
  Submodule.Quotient.equiv _ _ (degreeCyclesEquiv P d i)
    (degreeCyclesEquiv_boundaries P d hdd i f hfd hf hfill)

end IndividualGroup

end FourPapers.GradedHomologyDecomposition

namespace FourPapers.FilteredHomology

variable {R X Y Z W : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z] [AddCommGroup W] [Module R W]
  (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hfg : g.comp f = 0)
  (j : Z →ₗ[R] W) (hj : Function.Injective j)

include hfg in
theorem postcompose_comp_zero : (j.comp g).comp f = 0 := by
  rw [LinearMap.comp_assoc, hfg, LinearMap.comp_zero]

def cyclesEquiv_postcompose : LinearMap.ker g ≃ₗ[R] LinearMap.ker (j.comp g) where
  toFun x := ⟨x.val, by change j (g x.val) = 0; rw [x.property, map_zero]⟩
  invFun x := ⟨x.val, by apply hj; exact x.property.trans (map_zero j).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cyclesEquiv_postcompose_range :
    (LinearMap.range (boundaryMap f g hfg)).map
      (cyclesEquiv_postcompose g j hj).toLinearMap =
      LinearMap.range (boundaryMap f (j.comp g) (postcompose_comp_zero f g hfg j)) := by
  ext z
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨boundaryMap f g hfg a, ⟨a, rfl⟩, rfl⟩

/-- Enlarging the target of the outgoing differential by an injective
linear inclusion preserves the literal homology quotient. -/
def homologyEquiv_postcompose :
    Homology f g hfg ≃ₗ[R]
      Homology f (j.comp g) (postcompose_comp_zero f g hfg j) :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv_postcompose g j hj)
    (cyclesEquiv_postcompose_range f g hfg j hj)

end FourPapers.FilteredHomology

namespace FourPapers.ParityDifferential

open FilteredHomology GradedHomologyDecomposition

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (D : ParityDifferential K A)

theorem differential_comp_zero : D.d.comp D.d = 0 := LinearMap.ext D.square_zero

def cyclesLinearEquiv : D.cycles ≃ₗ[K] LinearMap.ker D.d where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cyclesLinearEquiv_boundaries :
    (D.boundaries.asIdeal.restrictScalars K).map D.cyclesLinearEquiv.toLinearMap =
      totalBoundaries D.d D.differential_comp_zero := by
  rw [D.boundaries_exact_range]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (mem_totalBoundaries D.d D.differential_comp_zero _).mpr
    change z.val ∈ LinearMap.range D.d at hz
    exact hz
  · intro hx
    refine ⟨⟨x.val, x.property⟩, ?_, rfl⟩
    change x.val ∈ LinearMap.range D.d
    exact (mem_totalBoundaries D.d D.differential_comp_zero x).mp hx

/-- The homology algebra's underlying module is exactly the usual quotient
of the kernel of the differential by its range. -/
def homologyLinearEquiv :
    D.Homology ≃ₗ[K] FilteredHomology.Homology D.d D.d D.differential_comp_zero :=
  (Submodule.Quotient.restrictScalarsEquiv K D.boundaries.asIdeal).symm.trans
    (Submodule.Quotient.equiv _ _ D.cyclesLinearEquiv D.cyclesLinearEquiv_boundaries)

end FourPapers.ParityDifferential

namespace FourPapers.GradedHomologyDecomposition

open Classical DirectSum FilteredHomology

section ShiftedGrading

variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  [AddCommGroup I] [DecidableEq I]
  (P : I → Submodule K M) [DirectSum.Decomposition P]
  (d : Module.End K M) (δ : I)
  (hd : ∀ i x, x ∈ P i → d x ∈ P (i + δ))

include hd in
theorem differential_projection (i : I) (x : M) :
    d (DirectSum.decompose P x i).val = (DirectSum.decompose P (d x) (i + δ)).val := by
  refine DirectSum.Decomposition.inductionOn P (by simp) ?_ ?_ x
  · intro j a
    by_cases hji : j = i
    · subst j
      rw [DirectSum.decompose_of_mem_same P a.property,
        DirectSum.decompose_of_mem_same P (hd i a.val a.property)]
    · rw [DirectSum.decompose_of_mem_ne P a.property hji,
        DirectSum.decompose_of_mem_ne P (hd j a.val a.property)
          (fun h => hji (add_right_cancel h)), map_zero]
  · intro x y hx hy
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, hx, hy]

include hd in
theorem cycles_homogeneous :
    ∀ i x, d x = 0 → d (DirectSum.decompose P x i).val = 0 := by
  intro i x hx
  rw [differential_projection P d δ hd, hx]
  simp

include hd in
theorem boundaries_homogeneous :
    ∀ i x, x ∈ LinearMap.range d → (DirectSum.decompose P x i).val ∈ LinearMap.range d := by
  rintro i x ⟨y, rfl⟩
  refine ⟨(DirectSum.decompose P y (i - δ)).val, ?_⟩
  rw [differential_projection P d δ hd, sub_add_cancel]

end ShiftedGrading

section FieldComparison

variable {k V W ι : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [DecidableEq ι]
  (P : ι → Submodule k V) (Q : ι → Submodule k W)
  [DirectSum.Decomposition P] [DirectSum.Decomposition Q]
  (d : Module.End k V) (e : Module.End k W)
  (hdd : d.comp d = 0) (hee : e.comp e = 0)
  (hcd : ∀ i x, d x = 0 → d (DirectSum.decompose P x i).val = 0)
  (hbd : ∀ i x, x ∈ LinearMap.range d → (DirectSum.decompose P x i).val ∈ LinearMap.range d)
  (hce : ∀ i x, e x = 0 → e (DirectSum.decompose Q x i).val = 0)
  (hbe : ∀ i x, x ∈ LinearMap.range e → (DirectSum.decompose Q x i).val ∈ LinearMap.range e)
  [∀ i, FiniteDimensional k (DegreeHomology P d hdd i)]
  [∀ i, FiniteDimensional k (DegreeHomology Q e hee i)]

include hcd hbd hce hbe in
/-- Pointwise equality of the actual graded Betti dimensions implies equality
of total homology dimensions, even when the grading index is infinite. -/
theorem finrank_total_eq_of_degree_eq
    (hβ : ∀ i, Module.finrank k (DegreeHomology P d hdd i) =
      Module.finrank k (DegreeHomology Q e hee i)) :
    Module.finrank k (Homology d d hdd) = Module.finrank k (Homology e e hee) := by
  let E : (⨁ i, DegreeHomology P d hdd i) ≃ₗ[k] ⨁ i, DegreeHomology Q e hee i :=
    DirectSum.congrLinearEquiv (fun i => LinearEquiv.ofFinrankEq _ _ (hβ i))
  exact ((homologyDecomposition P d hdd hcd hbd).trans
    (E.trans (homologyDecomposition Q e hee hce hbe).symm)).finrank_eq

end FieldComparison

end FourPapers.GradedHomologyDecomposition

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesHomologyGeneration -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

section Ring
variable {k : Type u} [CommRing k]

def reesKoszulTensorDGA (hE : finiteLatticeClosed n E) :
    ParityDifferential k (ReesKoszulTensorAlgebra E k) :=
  (reesKoszulCoordinateDifferential (k := k) hE).pullback (reesTensorCoordinateAlgEquiv (k := k) hE)

/-- The differential in the transported structure is exactly the ordinary
Koszul differential, with no change to its coefficients or multiplication. -/
theorem reesKoszulTensorDGA_d (hE : finiteLatticeClosed n E) :
    (reesKoszulTensorDGA (k := k) hE).d = reesKoszulTensorDifferential := by
  apply LinearMap.ext
  intro x
  apply (reesTensorCoordinateAlgEquiv (k := k) hE).injective
  change (reesTensorCoordinateAlgEquiv (k := k) hE)
    (((reesKoszulCoordinateDifferential (k := k) hE).pullback
      (reesTensorCoordinateAlgEquiv (k := k) hE)).d x) = _
  rw [FourPapers.ParityDifferential.pullback_intertwines]
  exact (reesTensorCoordinate_intertwines (k := k) hE x).symm

abbrev ReesKoszulHomology (hE : finiteLatticeClosed n E) :=
  (reesKoszulTensorDGA (k := k) hE).Homology

/-- Rees degree measured in the original monomial basis inside `S[t]`, before
any fine-coordinate change. Exterior generators have Rees degree zero. -/
def actualReesDegreePiece (m : ℕ) : Submodule k (ReesKoszulTensorAlgebra E k) :=
  Submodule.span k (reesTensorBasis '' {a : ReesTensorBasisIndex.{u} E | a.1.val none = m})

def actualFirstReesClasses (hE : finiteLatticeClosed n E) : Set (ReesKoszulHomology (k := k) hE) :=
  {z | ∃ x : (reesKoszulTensorDGA (k := k) hE).cycles,
    x.val ∈ actualReesDegreePiece 1 ∧ (reesKoszulTensorDGA (k := k) hE).classMap x = z}

lemma reesTensorCoordinate_symm_single_degree (hE : finiteLatticeClosed n E)
    (g : ReesFineDegree.{u} n) (x : PowerFaceModule (E := E) (k := k) g.1 g.2) :
    (reesTensorCoordinateLinearEquiv (k := k) hE).symm (reesKoszulSingle (k := k) hE g x) ∈
      actualReesDegreePiece g.1 := by
  let b := totalFaceBasis (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) g.1) g.2)
  let f := (reesTensorCoordinateLinearEquiv (k := k) hE).symm.toLinearMap.comp
    (reesKoszulSingle (k := k) hE g)
  have hf : (⊤ : Submodule k (PowerFaceModule (E := E) (k := k) g.1 g.2)) ≤
      (actualReesDegreePiece (E := E) (k := k) g.1).comap f := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro y ⟨F,rfl⟩
    change (reesTensorCoordinateLinearEquiv (k := k) hE).symm
      (reesKoszulSingle (k := k) hE g (b F)) ∈ actualReesDegreePiece g.1
    have h : (reesTensorCoordinateLinearEquiv (k := k) hE).symm
        (reesKoszulSingle (k := k) hE g (b F)) =
        reesTensorBasis (reesTensorCoordinateIndexEquiv.symm ⟨g,F⟩) := by
      apply (reesTensorCoordinateLinearEquiv (k := k) hE).injective
      rw [LinearEquiv.apply_symm_apply]
      change reesKoszulSingle (k := k) hE g (b F) =
        reesTensorBasis.equiv (reesCoordinateBasis (k := k) hE) reesTensorCoordinateIndexEquiv
          (reesTensorBasis (reesTensorCoordinateIndexEquiv.symm ⟨g,F⟩))
      rw [Module.Basis.equiv_apply, Equiv.apply_symm_apply]
      apply Subtype.ext
      change AddMonoidAlgebra.single g (b F).val = _
      rw [totalFaceBasis_val]
      exact (reesCoordinateBasis_val (k := k) hE ⟨g,F⟩).symm
    rw [h]
    apply Submodule.subset_span
    refine ⟨reesTensorCoordinateIndexEquiv.symm ⟨g,F⟩, ?_, rfl⟩
    exact finiteTargetExponent_none _ _
  exact hf (show x ∈ (⊤ : Submodule k (PowerFaceModule (E := E) (k := k) g.1 g.2)) from trivial)

def reesKoszulHomologyCoordinateEquiv (hE : finiteLatticeClosed n E) :
    ReesKoszulHomology (k := k) hE ≃ₐ[k] ReesKoszulCoordinateHomology (k := k) hE :=
  FourPapers.ParityDifferential.homologyEquiv
    (reesKoszulTensorDGA (k := k) hE) (reesKoszulCoordinateDifferential (k := k) hE)
    (reesTensorCoordinateAlgEquiv (k := k) hE)
    ((reesKoszulCoordinateDifferential (k := k) hE).pullback_intertwines (reesTensorCoordinateAlgEquiv (k := k) hE))

lemma firstReesClasses_transport (hE : finiteLatticeClosed n E)
    (z : ReesKoszulCoordinateHomology (k := k) hE) (hz : z ∈ firstReesClasses (k := k) hE) :
    (reesKoszulHomologyCoordinateEquiv (k := k) hE).symm z ∈ actualFirstReesClasses (k := k) hE := by
  obtain ⟨α,x,rfl⟩ := hz
  let e := reesTensorCoordinateAlgEquiv (k := k) hE
  let D := reesKoszulTensorDGA (k := k) hE
  let D' := reesKoszulCoordinateDifferential (k := k) hE
  let c := FourPapers.ParityDifferential.cyclesEquiv D D' e (D'.pullback_intertwines e)
  let y := c.symm (reesCycleSingle (k := k) hE (1,α) x)
  refine ⟨y, ?_, ?_⟩
  · exact reesTensorCoordinate_symm_single_degree (k := k) hE (1,α) x.val
  · apply (reesKoszulHomologyCoordinateEquiv (k := k) hE).injective
    rw [AlgEquiv.apply_symm_apply]
    change FourPapers.ParityDifferential.homologyEquiv D D' e (D'.pullback_intertwines e)
      (D.classMap y) = D'.classMap (reesCycleSingle (k := k) hE (1,α) x)
    rw [FourPapers.ParityDifferential.homologyEquiv_classMap]
    exact congrArg D'.classMap (c.apply_symm_apply _)

/-- Transfer a proved generation statement through the actual algebra
equivalence. This lemma works integrally as well as over fields. -/
theorem reesKoszulHomology_generated_of_coordinate_generation
    (hE : finiteLatticeClosed n E)
    (hgen : Algebra.adjoin k (firstReesClasses (k := k) hE) = ⊤) :
    Algebra.adjoin k (actualFirstReesClasses (k := k) hE) = ⊤ := by
  let S := Algebra.adjoin k (actualFirstReesClasses (k := k) hE)
  let e := reesKoszulHomologyCoordinateEquiv (k := k) hE
  have h : Algebra.adjoin k (firstReesClasses (k := k) hE) ≤ S.comap e.symm.toAlgHom := by
    apply Algebra.adjoin_le
    intro z hz
    exact Algebra.subset_adjoin (firstReesClasses_transport (k := k) hE z hz)
  rw [hgen] at h
  apply top_unique
  intro z _
  have hz := h (show e z ∈ (⊤ : Subalgebra k (ReesKoszulCoordinateHomology (k := k) hE)) from trivial)
  change e.symm (e z) ∈ S at hz
  simpa only [e.symm_apply_apply] using hz

end Ring

section Field
variable {k : Type u} [Field k]

/-- **The homology-algebra assertion of Theorem 1.2.** For every finite
sublattice and every field, the homology algebra of the ordinary Koszul complex
over its actual Rees image in `S[t]` is generated in Rees degree one. -/
theorem reesKoszulHomology_generated_in_degree_one (hE : finiteLatticeClosed n E) :
    Algebra.adjoin k (actualFirstReesClasses (k := k) hE) = ⊤ :=
  reesKoszulHomology_generated_of_coordinate_generation hE
    (reesCoordinateHomology_generated_in_degree_one (k := k) hE)

end Field
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FineTensorFaces -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
namespace QuotientGroebnerData

def tensorFineIndexEquiv (P : QuotientGroebnerData V k) (α : Exponent V) :
    {F : Finset V // quotientKoszulFaces P.family α F} ≃
      {t : P.TensorIndex // P.tensorDegree t=α} where
  toFun F := ⟨(⟨α-faceExponent F.val,F.property.2⟩,F.val),
    tsub_add_cancel_of_le F.property.1⟩
  invFun t := ⟨t.val.2,⟨by
    have hh : faceExponent t.val.2≤P.tensorDegree t.val := le_add_of_nonneg_left zero_le
    exact hh.trans_eq t.property,by
      have hh : α-faceExponent t.val.2=t.val.1.val := by
        simpa only [tensorDegree, add_tsub_cancel_right] using
          congrArg (fun a : Exponent V => a - faceExponent t.val.2) t.property.symm
      change QuotientAllowed P.family (α-faceExponent t.val.2)
      rw [hh]
      exact t.val.1.property⟩⟩
  left_inv F := rfl
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change α-faceExponent t.val.2=t.val.1.val
      simpa only [tensorDegree, add_tsub_cancel_right] using
        congrArg (fun a : Exponent V => a - faceExponent t.val.2) t.property.symm
    · rfl

/-- The complete fine face quotient is identified with the actual fine
submodule of the tensor Koszul module, including every exterior degree. -/
def faceTensorEquiv (P : QuotientGroebnerData V k) (α : Exponent V) :
    TotalFaceModule (k := k) (quotientKoszulFaces P.family α) ≃ₗ[k]
      Grading.Piece P.tensorBasis P.tensorDegree α :=
  (totalFaceBasis (k := k) (quotientKoszulFaces P.family α)).equiv
    (Grading.restrictedBasis P.tensorBasis (fun t => P.tensorDegree t=α))
    (P.tensorFineIndexEquiv α)

def faceTensorLift (P : QuotientGroebnerData V k) (α : Exponent V) :
    TotalFaceModule (k := k) (quotientKoszulFaces P.family α) →ₗ[k] P.TensorModel :=
  (Grading.Piece P.tensorBasis P.tensorDegree α).subtype.comp (P.faceTensorEquiv α).toLinearMap

lemma faceTensorLift_injective (P : QuotientGroebnerData V k) (α : Exponent V) :
    Function.Injective (P.faceTensorLift α) :=
  Subtype.val_injective.comp (P.faceTensorEquiv α).injective

lemma faceTensorLift_fine (P : QuotientGroebnerData V k) (α : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α)) :
    P.faceTensorLift α x∈Grading.Piece P.tensorBasis P.tensorDegree α :=
  (P.faceTensorEquiv α x).property

lemma faceTensorLift_basis_index (P : QuotientGroebnerData V k) (α : Exponent V)
    (F : {F : Finset V // quotientKoszulFaces P.family α F}) :
    P.faceTensorLift α (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)=
      P.tensorBasis (P.tensorFineIndexEquiv α F).val := by
  change (P.faceTensorEquiv α (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)).val=_
  calc
    _ = (Grading.restrictedBasis P.tensorBasis (fun t => P.tensorDegree t = α)
          (P.tensorFineIndexEquiv α F)).val :=
      congrArg (fun z : Submodule.span k
          (P.tensorBasis '' {t | P.tensorDegree t = α}) => z.val)
        (Module.Basis.equiv_apply
          (totalFaceBasis (k := k) (quotientKoszulFaces P.family α)) F
          (Grading.restrictedBasis P.tensorBasis (fun t => P.tensorDegree t = α))
          (P.tensorFineIndexEquiv α))
    _ = P.tensorBasis (P.tensorFineIndexEquiv α F).val :=
      Grading.restrictedBasis_val P.tensorBasis (fun t => P.tensorDegree t = α)
        (P.tensorFineIndexEquiv α F)

-- The value lemmas above identify these maps without expanding their basis
-- constructions again during subtype and tensor-coordinate inference.
attribute [local irreducible] totalFaceBasis faceTensorEquiv faceTensorLift

lemma faceTensorLift_basis (P : QuotientGroebnerData V k) (α : Exponent V)
    (F : {F : Finset V // quotientKoszulFaces P.family α F}) :
    P.faceTensorLift α (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)=
      quotientMonomial P.family (α-faceExponent F.val) ⊗ₜ[k] Simplicial.basis F.val := by
  rw [P.faceTensorLift_basis_index α F, tensorBasis,
    Module.Basis.tensorProduct_apply', quotientMonomialBasis_apply]
  rfl

lemma faceTensorLift_basis_of_value (P : QuotientGroebnerData V k) (α : Exponent V)
    (F : Finset V) (hF : quotientKoszulFaces P.family α F) :
    P.faceTensorLift α (⟨Simplicial.basis F,Submodule.subset_span ⟨F,hF,rfl⟩⟩)=
      quotientMonomial P.family (α-faceExponent F) ⊗ₜ[k] Simplicial.basis F := by
  have he : (⟨Simplicial.basis F,Submodule.subset_span ⟨F,hF,rfl⟩⟩ :
      TotalFaceModule (k := k) (quotientKoszulFaces P.family α))=
        totalFaceBasis (k := k) (quotientKoszulFaces P.family α) ⟨F,hF⟩ := by
    apply Subtype.ext
    exact (totalFaceBasis_val (k := k) (quotientKoszulFaces P.family α) ⟨F,hF⟩).symm
  rw [he]
  exact P.faceTensorLift_basis α ⟨F, hF⟩

lemma faceTensorLift_degree (P : QuotientGroebnerData V k) (α : Exponent V) (i : ℕ)
    (x : Simplicial.Chains (k := k) (quotientKoszulFaces P.family α) i) :
    P.faceTensorLift α ⟨x.val,chains_mem_basisSpan x.property⟩=
      FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
        (M := CoefficientQuotient (k := k) P.family) i
        (quotientFaceHomogeneousEquiv (k := k) P.family α i x).val := by
  let f := (P.faceTensorLift α).comp
    (Submodule.inclusion (show Simplicial.Chains (k := k) (quotientKoszulFaces P.family α) i≤
      TotalFaceModule (k := k) (quotientKoszulFaces P.family α) from fun _ hx => chains_mem_basisSpan hx))
  let g := (FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
        (M := CoefficientQuotient (k := k) P.family) i).comp
    ((Submodule.subtype (quotientPiece (k := k) P.family α i)).comp
      (quotientFaceHomogeneousEquiv (k := k) P.family α i).toLinearMap)
  have he : f=g := by
    apply (quotientFaceBasis (k := k) P.family α i).ext
    intro F
    change P.faceTensorLift α ⟨(quotientFaceBasis (k := k) P.family α i F).val,
        chains_mem_basisSpan (quotientFaceBasis (k := k) P.family α i F).property⟩=_
    have hh : (⟨(quotientFaceBasis (k := k) P.family α i F).val,
        chains_mem_basisSpan (quotientFaceBasis (k := k) P.family α i F).property⟩ :
        TotalFaceModule (k := k) (quotientKoszulFaces P.family α))=
          totalFaceBasis (k := k) (quotientKoszulFaces P.family α) ⟨F.val,F.property.1⟩ := by
      apply Subtype.ext
      exact (quotientFaceBasis_val (k := k) P.family α i F).trans
        (totalFaceBasis_val (k := k) (quotientKoszulFaces P.family α)
          ⟨F.val, F.property.1⟩).symm
    rw [hh,P.faceTensorLift_basis]
    change _=FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
        (M := CoefficientQuotient (k := k) P.family) i
      (quotientFaceHomogeneousEquiv (k := k) P.family α i (quotientFaceBasis (k := k) P.family α i F)).val
    rw [quotientFaceHomogeneousEquiv_basis (k := k),quotientCoefficientBasis_apply (k := k),
      FourPapers.TensorExteriorKoszul.lift_single]
    rfl
  exact LinearMap.congr_fun he x

def initialTensorDifferential (P : QuotientGroebnerData V k) : Module.End k P.TensorModel :=
  FourPapers.TensorExteriorKoszul.differential (K := k) (R := MvPolynomial V k)
    (M := CoefficientQuotient (k := k) P.family) (MvPolynomial.X : V → MvPolynomial V k)

/-- The tensor differential in the literal quotient coordinate presentation. -/
lemma initialTensorDifferential_lift (P : QuotientGroebnerData V k) (i : ℕ)
    (z : Set.powersetCard V (i+1) →₀ CoefficientQuotient (k := k) P.family) :
    P.initialTensorDifferential
        (FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
          (M := CoefficientQuotient (k := k) P.family) (i+1) z) =
      FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
        (M := CoefficientQuotient (k := k) P.family) i
        (quotientDifferential (k := k) P.family i z) :=
  FourPapers.TensorExteriorKoszul.differential_lift
    (K := k) (R := MvPolynomial V k) (V := V)
    (M := CoefficientQuotient (k := k) P.family)
    (MvPolynomial.X : V → MvPolynomial V k) i z

/-- Forget the homogeneous subtype before applying the tensor inclusion. -/
lemma faceHomogeneousDifferential_value (B : Family V) (α : Exponent V) (i : ℕ)
    (x : Simplicial.Chains (k := k) (quotientKoszulFaces B α) (i+1)) :
    quotientDifferential (k := k) B i
        (quotientFaceHomogeneousEquiv (k := k) B α (i+1) x).val =
      (quotientFaceHomogeneousEquiv (k := k) B α i
        (quotientFaceDifferential (k := k) B α i x)).val :=
  congrArg
    (@Subtype.val (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B)
      (fun z => z ∈ quotientPiece (k := k) B α i))
    (quotientFaceHomogeneousEquiv_differential (k := k) B α i x)

lemma faceTensorLift_differential_degree (P : QuotientGroebnerData V k)
    (α : Exponent V) (i : ℕ)
    (x : Simplicial.Chains (k := k) (quotientKoszulFaces P.family α) (i+1)) :
    P.initialTensorDifferential (P.faceTensorLift α ⟨x.val,chains_mem_basisSpan x.property⟩)=
      P.faceTensorLift α
        ⟨(quotientFaceDifferential (k := k) P.family α i x).val,
          chains_mem_basisSpan (quotientFaceDifferential (k := k) P.family α i x).property⟩ := by
  rw [P.faceTensorLift_degree,P.faceTensorLift_degree]
  exact (P.initialTensorDifferential_lift i
    (quotientFaceHomogeneousEquiv (k := k) P.family α (i+1) x).val).trans
      (congrArg (FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
        (M := CoefficientQuotient (k := k) P.family) i)
        (faceHomogeneousDifferential_value (k := k) P.family α i x))

/-- The fine-strand inclusion intertwines the complete actual differentials,
including exterior degree zero. -/
theorem faceTensorLift_differential (P : QuotientGroebnerData V k)
    (α : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α)) :
    P.initialTensorDifferential (P.faceTensorLift α x)=
      P.faceTensorLift α (quotientTotalDifferential P.family α x) := by
  suffices h : P.initialTensorDifferential.comp (P.faceTensorLift α)=
      (P.faceTensorLift α).comp (quotientTotalDifferential P.family α) from
    LinearMap.congr_fun h x
  apply (totalFaceBasis (k := k) (quotientKoszulFaces P.family α)).ext
  intro F
  change P.initialTensorDifferential (P.faceTensorLift α
    (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)) =
    P.faceTensorLift α (quotientTotalDifferential (k := k) P.family α
      (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F))
  by_cases hzero : F.val.card=0
  · have he : F.val=∅ := Finset.card_eq_zero.mp hzero
    rw [P.faceTensorLift_basis,initialTensorDifferential,
      FourPapers.TensorExteriorKoszul.differential_tmul]
    have hd : quotientTotalDifferential P.family α
        (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)=0 := by
      apply Subtype.ext
      simp only [quotientTotalDifferential_val,totalFaceBasis_val,he,
        Simplicial.boundary_eq_sum,Simplicial.contraction_basis,Finset.notMem_empty,
        if_false,Finset.sum_const_zero,map_zero,Submodule.coe_zero]
    simp only [he,Simplicial.contraction_basis,Finset.notMem_empty,if_false,
      TensorProduct.tmul_zero,Finset.sum_const_zero,hd,map_zero]
  · obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    let y : Simplicial.Chains (k := k) (quotientKoszulFaces P.family α) (i+1) :=
      ⟨Simplicial.basis F.val,Simplicial.basis_mem F.property hi⟩
    have hy : (⟨y.val,chains_mem_basisSpan y.property⟩ :
        TotalFaceModule (k := k) (quotientKoszulFaces P.family α))=
          totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F :=
      Subtype.ext (totalFaceBasis_val (k := k) _ _).symm
    have hd : (⟨(quotientFaceDifferential (k := k) P.family α i y).val,
          chains_mem_basisSpan (quotientFaceDifferential (k := k) P.family α i y).property⟩ :
        TotalFaceModule (k := k) (quotientKoszulFaces P.family α))=
          quotientTotalDifferential P.family α (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F) := by
      apply Subtype.ext
      rw [quotientFaceDifferential_val,quotientTotalDifferential_val,totalFaceBasis_val]
    simpa only [hy,hd] using P.faceTensorLift_differential_degree α i y

lemma faceTensorLift_projected_basis (P : QuotientGroebnerData V k)
    (α : Exponent V) (F : Finset V) (hF : fullKoszulFaces α F) :
    P.faceTensorLift α
      ⟨quotientFaceProjection P.family α (Simplicial.basis F),relativeProjection_mem _ _ _ _⟩=
        quotientMonomial P.family (α-faceExponent F) ⊗ₜ[k] Simplicial.basis F := by
  by_cases hq : QuotientAllowed P.family (α-faceExponent F)
  · have hz : (⟨quotientFaceProjection P.family α (Simplicial.basis F),
          relativeProjection_mem _ _ _ _⟩ :
        TotalFaceModule (k := k) (quotientKoszulFaces P.family α))=
          totalFaceBasis (k := k) (quotientKoszulFaces P.family α) ⟨F,⟨hF,hq⟩⟩ := by
      apply Subtype.ext
      rw [totalFaceBasis_val]
      change relativeProjection (Simplicial.basis (k := k)) (fullKoszulFaces α)
        (forbiddenKoszulFaces P.family α) (Simplicial.basis F) = Simplicial.basis F
      rw [relativeProjection_basis, if_pos ⟨hF,hq⟩]
    rw [hz,P.faceTensorLift_basis]
  · have hn : ¬(fullKoszulFaces α F ∧ ¬forbiddenKoszulFaces P.family α F) :=
      fun h => hq h.2
    have hz : (⟨quotientFaceProjection P.family α (Simplicial.basis F),
          relativeProjection_mem _ _ _ _⟩ :
        TotalFaceModule (k := k) (quotientKoszulFaces P.family α))=0 := by
      apply Subtype.ext
      change relativeProjection (Simplicial.basis (k := k)) (fullKoszulFaces α)
        (forbiddenKoszulFaces P.family α) (Simplicial.basis F) = 0
      rw [relativeProjection_basis,if_neg hn]
    rw [hz,map_zero,quotientMonomial_zero P.family _ hq,TensorProduct.zero_tmul]

/-- The actual projected multiplication, as a bilinear map. -/
def quotientFaceMulBilinear (B : Family V) (α β : Exponent V) :
    TotalFaceModule (k := k) (quotientKoszulFaces B α) →ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces B β) →ₗ[k]
        TotalFaceModule (k := k) (quotientKoszulFaces B (α+β)) :=
  ((LinearMap.mul k (Simplicial.Ambient V k)).compl₁₂
    (TotalFaceModule (k := k) (quotientKoszulFaces B α)).subtype
    (TotalFaceModule (k := k) (quotientKoszulFaces B β)).subtype).compr₂
      ((quotientFaceProjection (k := k) B (α+β)).codRestrict _
        (fun _ => relativeProjection_mem _ _ _ _))

/-- Multiplication of fine strands is the genuine monomial-quotient tensor
product. The quotient projection on exterior faces is retained on the left. -/
theorem faceTensorLift_mul (P : QuotientGroebnerData V k) (α β : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α))
    (y : TotalFaceModule (k := k) (quotientKoszulFaces P.family β)) :
    P.faceTensorLift (α+β) (quotientFaceMul P.family α β x y)=
      P.faceTensorLift α x*P.faceTensorLift β y := by
  let f := (quotientFaceMulBilinear (k := k) P.family α β).compr₂ (P.faceTensorLift (α+β))
  let g := (LinearMap.mul k P.TensorModel).compl₁₂ (P.faceTensorLift α) (P.faceTensorLift β)
  have he : f=g := by
    apply (totalFaceBasis (k := k) (quotientKoszulFaces P.family α)).ext
    intro F
    apply (totalFaceBasis (k := k) (quotientKoszulFaces P.family β)).ext
    intro G
    change P.faceTensorLift (α+β)
      (quotientFaceMul P.family α β (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)
        (totalFaceBasis (k := k) (quotientKoszulFaces P.family β) G))=
      P.faceTensorLift α (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F) *
        P.faceTensorLift β (totalFaceBasis (k := k) (quotientKoszulFaces P.family β) G)
    rw [P.faceTensorLift_basis,P.faceTensorLift_basis,Algebra.TensorProduct.tmul_mul_tmul]
    by_cases hd : Disjoint F.val G.val
    · let σ := faceWedgeSign F.val G.val hd
      have hz : quotientFaceMul P.family α β
          (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)
          (totalFaceBasis (k := k) (quotientKoszulFaces P.family β) G)=
          σ • (⟨quotientFaceProjection P.family (α+β) (Simplicial.basis (F.val∪G.val)),
            relativeProjection_mem _ _ _ _⟩ :
              TotalFaceModule (k := k) (quotientKoszulFaces P.family (α+β))) := by
        apply Subtype.ext
        simp only [quotientFaceMul,totalFaceBasis_val,faceBasis_mul_of_disjoint _ _ hd,
          map_zsmul_unit,Submodule.coe_smul_of_tower,σ]
      rw [hz,map_zsmul_unit,P.faceTensorLift_projected_basis (α+β) (F.val∪G.val)
        (fullKoszulFaces_union α β F.val G.val F.property.1 G.property.1 hd),
        faceBasis_mul_of_disjoint _ _ hd,TensorProduct.tmul_smul]
      congr 1
      rw [residual_union_of_disjoint α β F.val G.val hd F.property.1 G.property.1]
      congr 1
      change Ideal.Quotient.mk _ (MvPolynomial.monomial _ (1:k))=
        Ideal.Quotient.mk _ (MvPolynomial.monomial _ (1:k))*
          Ideal.Quotient.mk _ (MvPolynomial.monomial _ (1:k))
      rw [←map_mul,MvPolynomial.monomial_mul_monomial,one_mul]
    · have hz : quotientFaceMul P.family α β
          (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)
          (totalFaceBasis (k := k) (quotientKoszulFaces P.family β) G)=0 := by
        apply Subtype.ext
        simp only [quotientFaceMul,totalFaceBasis_val,faceBasis_mul_of_not_disjoint _ _ hd,
          map_zero,Submodule.coe_zero]
      rw [hz,map_zero,faceBasis_mul_of_not_disjoint _ _ hd,TensorProduct.tmul_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTensorDifferential -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
namespace QuotientGroebnerData

/-- The actual binomial quotient Koszul differential transported through the
verified standard-monomial coefficient basis. -/
def tensorDifferential (P : QuotientGroebnerData V k) : Module.End k P.TensorModel :=
  P.tensorEquiv.symm.toLinearMap.comp
    ((FourPapers.TensorExteriorKoszul.differential (K := k) (R := MvPolynomial V k)
      (M := MvPolynomial V k ⧸ P.ideal) (MvPolynomial.X : V → MvPolynomial V k)).comp
        P.tensorEquiv.toLinearMap)

lemma tensorEquiv_differential (P : QuotientGroebnerData V k) (x : P.TensorModel) :
    P.tensorEquiv (P.tensorDifferential x)=
      FourPapers.TensorExteriorKoszul.differential (K := k) (R := MvPolynomial V k)
        (M := MvPolynomial V k ⧸ P.ideal) MvPolynomial.X (P.tensorEquiv x) := by
  simp only [tensorDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem tensorDifferential_comp (P : QuotientGroebnerData V k) :
    P.tensorDifferential.comp P.tensorDifferential=0 := by
  apply LinearMap.ext
  intro x
  apply P.tensorEquiv.injective
  rw [LinearMap.comp_apply,LinearMap.zero_apply,P.tensorEquiv_differential,
    P.tensorEquiv_differential,tensorLinearEquiv_zero (R := k) P.tensorEquiv]
  exact LinearMap.congr_fun (FourPapers.TensorExteriorKoszul.differential_comp
    (K := k) (R := MvPolynomial V k) (M := MvPolynomial V k ⧸ P.ideal)
    (MvPolynomial.X : V → MvPolynomial V k)) _

theorem tensorCycles_mul (P : QuotientGroebnerData V k) (x y : P.TensorModel)
    (hx : P.tensorDifferential x=0) (hy : P.tensorDifferential y=0) :
    P.tensorDifferential (P.tensorMul x y)=0 := by
  apply P.tensorEquiv.injective
  rw [P.tensorEquiv_differential,P.tensorMul_apply,LinearEquiv.apply_symm_apply,tensorLinearEquiv_zero (R := k) P.tensorEquiv]
  have hx' : FourPapers.TensorExteriorKoszul.differential (K := k) (R := MvPolynomial V k)
      (M := MvPolynomial V k ⧸ P.ideal) MvPolynomial.X (P.tensorEquiv x)=0 := by
    rw [←P.tensorEquiv_differential,hx,tensorLinearEquiv_zero (R := k) P.tensorEquiv]
  have hy' : FourPapers.TensorExteriorKoszul.differential (K := k) (R := MvPolynomial V k)
      (M := MvPolynomial V k ⧸ P.ideal) MvPolynomial.X (P.tensorEquiv y)=0 := by
    rw [←P.tensorEquiv_differential,hy,tensorLinearEquiv_zero (R := k) P.tensorEquiv]
  rw [FourPapers.TensorExteriorKoszul.differential_algebraMap (K := k)
    (R := MvPolynomial V k) (A := MvPolynomial V k ⧸ P.ideal)
    (MvPolynomial.X : V → MvPolynomial V k)] at hx' hy' ⊢
  exact FourPapers.TensorExteriorKoszul.cycles_mul _ _ _ hx' hy'

lemma coefficientEquiv_one (P : QuotientGroebnerData V k) (hzero : QuotientAllowed P.family 0) :
    P.coefficientEquiv 1=1 := by
  have hh := groebnerCoefficientEquiv_basis P.order P.ideal P.generators P.groebner
    P.unitLeading P.family P.standard ⟨0,hzero⟩
  simpa only [quotientMonomialBasis_apply,quotientMonomial,MvPolynomial.monomial_zero',
    MvPolynomial.C_1,map_one,coefficientEquiv] using hh

lemma tensorEquiv_one (P : QuotientGroebnerData V k) (hzero : QuotientAllowed P.family 0) :
    P.tensorEquiv 1=1 := by
  change P.tensorEquiv ((1 : CoefficientQuotient (k := k) P.family) ⊗ₜ[k]
    (1 : Simplicial.Ambient V k))=(1 : MvPolynomial V k ⧸ P.ideal) ⊗ₜ[k] (1 : Simplicial.Ambient V k)
  simp only [tensorEquiv,TensorProduct.congr_tmul,LinearEquiv.refl_apply,P.coefficientEquiv_one hzero]

lemma tensorDifferential_one (P : QuotientGroebnerData V k) (hzero : QuotientAllowed P.family 0) :
    P.tensorDifferential 1=0 := by
  apply P.tensorEquiv.injective
  rw [P.tensorEquiv_differential,P.tensorEquiv_one hzero,tensorLinearEquiv_zero (R := k) P.tensorEquiv,
    FourPapers.TensorExteriorKoszul.differential_algebraMap (K := k)
      (R := MvPolynomial V k) (A := MvPolynomial V k ⧸ P.ideal)
      (MvPolynomial.X : V → MvPolynomial V k)]
  exact FourPapers.TensorExteriorKoszul.differential_one _

lemma tensorDifferential_basis (P : QuotientGroebnerData V k) (t : P.TensorIndex) :
    P.tensorDifferential (P.tensorBasis t)=
      ∑v : V,P.coefficientEquiv.symm (Ideal.Quotient.mk P.ideal
          (MvPolynomial.monomial (t.1.val+Finsupp.single v 1) 1)) ⊗ₜ[k]
        Simplicial.contraction v (Simplicial.basis t.2) := by
  change P.tensorEquiv.symm (FourPapers.TensorExteriorKoszul.differential
    (K := k) (R := MvPolynomial V k) (M := MvPolynomial V k ⧸ P.ideal)
      MvPolynomial.X (P.tensorEquiv (P.tensorBasis t)))=_
  rw [P.tensorEquiv_basis,FourPapers.TensorExteriorKoszul.differential_tmul,
    tensorLinearEquiv_sum (R := k) P.tensorEquiv.symm]
  apply Finset.sum_congr rfl
  intro v hv
  have hm : (MvPolynomial.X v : MvPolynomial V k) •
      Ideal.Quotient.mk P.ideal (MvPolynomial.monomial t.1.val 1)=
        Ideal.Quotient.mk P.ideal (MvPolynomial.monomial (t.1.val+Finsupp.single v 1) 1) := by
    change Ideal.Quotient.mk P.ideal (MvPolynomial.X v*MvPolynomial.monomial t.1.val (1:k))=_
    simp [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,add_comm]
  rw [hm]
  simp only [tensorEquiv,TensorProduct.congr_symm,TensorProduct.congr_tmul,LinearEquiv.refl_symm,LinearEquiv.refl_apply]

lemma initialTensorDifferential_basis (P : QuotientGroebnerData V k) (t : P.TensorIndex) :
    P.initialTensorDifferential (P.tensorBasis t)=
      ∑v : V,quotientMonomial P.family (t.1.val+Finsupp.single v 1) ⊗ₜ[k]
        Simplicial.contraction v (Simplicial.basis t.2) := by
  rw [tensorBasis,Module.Basis.tensorProduct_apply',quotientMonomialBasis_apply,
    initialTensorDifferential,FourPapers.TensorExteriorKoszul.differential_tmul]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  change Ideal.Quotient.mk _ (MvPolynomial.X v*MvPolynomial.monomial t.1.val (1:k))=
    Ideal.Quotient.mk _ (MvPolynomial.monomial (t.1.val+Finsupp.single v 1) 1)
  simp [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,add_comm]

/-- The total actual quotient differential has precisely the monomial
differential as its leading-weight part, in all exterior degrees at once. -/
theorem tensorDifferential_basis_strict_correction (P : QuotientGroebnerData V k)
    (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(MvPolynomial.monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (t u : P.TensorIndex)
    (hweight : Finsupp.weight w (P.tensorDegree t)≤Finsupp.weight w (P.tensorDegree u)) :
    P.tensorBasis.repr ((P.tensorDifferential-P.initialTensorDifferential)
      (P.tensorBasis t)) u=0 := by
  rw [LinearMap.sub_apply,P.tensorDifferential_basis,P.initialTensorDifferential_basis,
    ←Finset.sum_sub_distrib,tensorLinearEquiv_sum (R := k) P.tensorBasis.repr,
    Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro v hv
  rw [←TensorProduct.sub_tmul,Simplicial.contraction_basis]
  by_cases ht : v∈t.2
  · rw [if_pos ht,TensorProduct.tmul_smul,
      tensorLinearEquiv_unit_smul (R := k) P.tensorBasis.repr,Finsupp.smul_apply]
    change TauCeti.ExteriorAlgebra.basisEraseSign v t.2 •
      ((quotientMonomialBasis P.family).tensorProduct (Simplicial.basis (k := k))).repr
        ((_ : CoefficientQuotient (k := k) P.family) ⊗ₜ[k] Simplicial.basis (t.2.erase v)) u=0
    rw [Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,Finsupp.single_apply]
    by_cases hu : t.2.erase v=u.2
    · rw [if_pos hu,one_smul]
      have he : (t.1.val+Finsupp.single v 1)+faceExponent u.2=P.tensorDegree t := by
        rw [←hu,add_assoc,add_comm (Finsupp.single v 1),faceExponent_erase_add ht]
        rfl
      have hw : Finsupp.weight w (t.1.val+Finsupp.single v 1)≤Finsupp.weight w u.1.val := by
        have hh := congrArg (Finsupp.weight w) he
        simp only [tensorDegree,map_add] at hh hweight ⊢
        omega
      rw [P.coefficient_normalForm_correction w htail _ _ hw,smul_zero]
    · rw [if_neg hu,zero_smul,smul_zero]
  · rw [if_neg ht,TensorProduct.tmul_zero,tensorLinearEquiv_zero (R := k) P.tensorBasis.repr,
      Finsupp.zero_apply]

theorem tensorDifferential_fine_strict_correction (P : QuotientGroebnerData V k)
    (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(MvPolynomial.monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (α : Exponent V) (x : P.TensorModel) (hx : x∈Grading.Piece P.tensorBasis P.tensorDegree α) :
    P.tensorDifferential x-P.initialTensorDifferential x∈
      (FourPapers.Universal.basisFiltration P.tensorBasis
        (fun t => Finsupp.weight w (P.tensorDegree t))).level (Finsupp.weight w α) := by
  let δ := P.tensorDifferential-P.initialTensorDifferential
  change δ x∈_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t,ht,rfl⟩ := hx
    change P.tensorDegree t = α at ht
    rw [FourPapers.Universal.basisFiltration_mem]
    intro u hu
    exact P.tensorDifferential_basis_strict_correction w htail t u (by simpa only [ht] using hu)
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end


end
