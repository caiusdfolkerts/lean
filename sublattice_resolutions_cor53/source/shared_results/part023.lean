module
public import graph_foundation.part014
public import shared_results.part022

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FinerIdealGrading -/
section

/-! # Arbitrary finer gradings respected by the degeneration

The grading group may be any additive commutative monoid. A homomorphism
to the integers records refinement of the ordinary degree; it is not
required to map all grading labels to nonnegative integers.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial FilteredHomology

universe u v
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  {Γ : Type v} [AddCommMonoid Γ]
  (P : QuotientGroebnerData V K) (ω : V → Γ)

def finerIdealPiece (γ : Γ) (p : ℕ) :
    Submodule K (Set.powersetCard V p →₀ P.ideal) :=
  Grading.Piece (actualIdealCoefficientBasis P p)
    (fun a => Finsupp.weight ω (actualIdealDegree a)) γ

instance finerIdealPieceAddCommGroup (γ : Γ) (p : ℕ) :
    AddCommGroup (finerIdealPiece P ω γ p) :=
  Submodule.addCommGroup (R := K) (M := Set.powersetCard V p →₀ P.ideal)
    (module_M := inferInstance) (finerIdealPiece P ω γ p)

instance finerIdealPieceModule (γ : Γ) (p : ℕ) :
    Module K (finerIdealPiece P ω γ p) :=
  Submodule.module (R := K) (M := Set.powersetCard V p →₀ P.ideal)
    (finerIdealPiece P ω γ p)

def finerIdealBasis (γ : Γ) (p : ℕ) :
    Module.Basis {a : ActualIdealIndex P p // Finsupp.weight ω (actualIdealDegree a)=γ}
      K (finerIdealPiece P ω γ p) :=
  Grading.restrictedBasis (actualIdealCoefficientBasis P p)
    (fun a => Finsupp.weight ω (actualIdealDegree a)=γ)

@[simp] theorem finerIdealBasis_val (γ : Γ) (p : ℕ)
    (a : {a : ActualIdealIndex P p // Finsupp.weight ω (actualIdealDegree a)=γ}) :
    (finerIdealBasis P ω γ p a).val = actualIdealCoefficientBasis P p a.val :=
  Grading.restrictedBasis_val (actualIdealCoefficientBasis P p)
    (fun a => Finsupp.weight ω (actualIdealDegree a)=γ) a

/-- The restricted homogeneous basis keeps the original ideal coordinates. -/
theorem finerIdealBasis_repr (γ : Γ) (p : ℕ) (x : finerIdealPiece P ω γ p)
    (a : {a : ActualIdealIndex P p // Finsupp.weight ω (actualIdealDegree a)=γ}) :
    (finerIdealBasis P ω γ p).repr x a =
      (actualIdealCoefficientBasis P p).repr x.val a.val := by
  have he : (finerIdealBasis P ω γ p).coord a =
      ((actualIdealCoefficientBasis P p).coord a.val).comp
        (finerIdealPiece P ω γ p).subtype := by
    apply (finerIdealBasis P ω γ p).ext
    intro j
    simp only [Module.Basis.coord_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      finerIdealBasis_val, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [Subtype.ext_iff]
  exact LinearMap.congr_fun he x

/-- Every support bound is the restriction of the same bound on the
ambient ideal basis. This includes both closed and strict order levels. -/
theorem finerIdealBasis_span_mem_iff (γ : Γ) (p : ℕ)
    (S : Set (ActualIdealIndex P p)) (x : finerIdealPiece P ω γ p) :
    x ∈ Submodule.span K ((finerIdealBasis P ω γ p) '' {a | a.val ∈ S}) ↔
      x.val ∈ Submodule.span K ((actualIdealCoefficientBasis P p) '' S) := by
  rw [(finerIdealBasis P ω γ p).mem_span_image,
    (actualIdealCoefficientBasis P p).mem_span_image]
  refine finsupp_support_subset_iff_of_restrict
    ((finerIdealBasis P ω γ p).repr x)
    ((actualIdealCoefficientBasis P p).repr x.val) Subtype.val
    (fun a => finerIdealBasis_repr P ω γ p x a) ?_ S
  intro a ha
  have hd : Finsupp.weight ω (actualIdealDegree a)=γ :=
    (Grading.mem_piece (actualIdealCoefficientBasis P p)
      (fun a => Finsupp.weight ω (actualIdealDegree a)) γ x.val).mp x.property a
        (Finsupp.mem_support_iff.mp ha)
  exact ⟨⟨a, hd⟩, rfl⟩

/-- A basis-free description: the literal polynomial coefficients and
exterior monomials all have precisely the stated weighted degree. -/
def polynomialWeightedCoordinatePiece (J : Ideal (MvPolynomial V K)) (γ : Γ) (p : ℕ) :
    Submodule K (Set.powersetCard V p →₀ J) :=
  (Grading.Piece (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
    (fun a => Finsupp.weight ω (quotientDegree a)) γ).comap (idealCoordinatesToAmbient J p)

variable (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω))

include hJ in
theorem idealCoordinatesToAmbient_basis_finer (p : ℕ) (a : ActualIdealIndex P p) :
    idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a)∈
      Grading.Piece (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
        (fun b => Finsupp.weight ω (quotientDegree b))
        (Finsupp.weight ω (actualIdealDegree a)) := by
  rw [Grading.mem_piece]
  intro b hb
  rw [idealCoordinatesToAmbient_repr,actualIdealCoefficientBasis_apply] at hb
  by_cases hF : a.1=b.1
  · rw [Finsupp.single_apply,if_pos hF] at hb
    have hd := idealLift_homogeneous P.order P.ideal P.generators P.groebner P.unitLeading ω hJ a.2 hb
    simp only [quotientDegree,actualIdealDegree,map_add,hd,hF]
  · rw [Finsupp.single_apply,if_neg hF] at hb
    exact (hb rfl).elim

include hJ in
/-- This equality establishes that the basis-defined graded component is
exactly the original weighted polynomial Koszul component. -/
theorem finerIdealPiece_eq_polynomial (γ : Γ) (p : ℕ) :
    finerIdealPiece P ω γ p=polynomialWeightedCoordinatePiece ω P.ideal γ p := by
  ext x
  constructor
  · exact map_mem_piece_of_basis_monoid (R := K)
      (X := Set.powersetCard V p →₀ P.ideal)
      (Y := AmbientKoszulCoordinates (k := K) (V := V) p)
      (I := ActualIdealIndex P p) (J := QuotientIndex (∅ : Family V) p) (A := Γ)
      (actualIdealCoefficientBasis P p)
      (quotientCoefficientBasis (k := K) (∅ : Family V) p)
      (fun a => Finsupp.weight ω (actualIdealDegree a))
      (fun a => Finsupp.weight ω (quotientDegree a))
      (idealCoordinatesToAmbient P.ideal p)
      (idealCoordinatesToAmbient_basis_finer P ω hJ p) γ
  · intro hx
    rw [finerIdealPiece, Grading.mem_piece]
    intro a ha
    apply (Grading.mem_piece _ _ _ _).mp hx (actualIdealAmbientIndex P p a)
    simpa only [idealCoordinatesToAmbient_repr,actualIdealAmbientIndex,
      actualIdealCoefficientBasis_repr] using ha

include hJ in
theorem actualIdealCoordinateDifferential_finer (γ : Γ) (p : ℕ)
    (x : Set.powersetCard V (p+1) →₀ P.ideal) (hx : x∈finerIdealPiece P ω γ (p+1)) :
    actualIdealCoordinateDifferential P.ideal p x∈finerIdealPiece P ω γ p := by
  rw [finerIdealPiece_eq_polynomial P ω hJ] at hx ⊢
  change idealCoordinatesToAmbient P.ideal p (actualIdealCoordinateDifferential P.ideal p x) ∈
    Grading.Piece (quotientCoefficientBasis (k := K) (∅ : Family V) p)
      (fun a => Finsupp.weight ω (quotientDegree a)) γ
  rw [← idealCoordinatesToAmbient_differential]
  exact map_mem_piece_of_basis_monoid (R := K)
    (X := AmbientKoszulCoordinates (k := K) (V := V) (p+1))
    (Y := AmbientKoszulCoordinates (k := K) (V := V) p)
    (I := QuotientIndex (∅ : Family V) (p+1))
    (J := QuotientIndex (∅ : Family V) p) (A := Γ)
    (quotientCoefficientBasis (k := K) (∅ : Family V) (p+1))
    (quotientCoefficientBasis (k := K) (∅ : Family V) p)
    (fun a => Finsupp.weight ω (quotientDegree a))
    (fun a => Finsupp.weight ω (quotientDegree a))
    (quotientDifferential (k := K) (∅ : Family V) p)
    (quotientDifferential_basis_regraded (k := K) (∅ : Family V) (Finsupp.weight ω) p) γ hx

def finerIdealDifferential (γ : Γ) (p : ℕ) :
    finerIdealPiece P ω γ (p+1) →ₗ[K] finerIdealPiece P ω γ p :=
  ((actualIdealCoordinateDifferential P.ideal p).domRestrict
    (finerIdealPiece P ω γ (p+1))).codRestrict
      (finerIdealPiece P ω γ p)
      (fun x => actualIdealCoordinateDifferential_finer P ω hJ γ p x.val x.property)

@[simp] theorem finerIdealDifferential_val (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ (p+1)) :
    (finerIdealDifferential P ω hJ γ p x).val = actualIdealCoordinateDifferential P.ideal p x.val := rfl

def finerIdealPrevious (γ : Γ) : ∀ p,finerIdealPiece P ω γ p →ₗ[K] finerIdealPiece P ω γ p.pred
  | 0 => 0
  | p+1 => finerIdealDifferential P ω hJ γ p

@[simp] theorem finerIdealPrevious_val (γ : Γ) (p : ℕ) (x : finerIdealPiece P ω γ p) :
    (finerIdealPrevious P ω hJ γ p x).val=actualIdealPreviousDifferential P.ideal p x.val := by
  cases p <;> rfl

theorem finerIdealDifferential_comp (γ : Γ) (p : ℕ) :
    (finerIdealPrevious P ω hJ γ p).comp (finerIdealDifferential P ω hJ γ p)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (finerIdealPrevious P ω hJ γ p
    (finerIdealDifferential P ω hJ γ p x)).val = 0
  rw [finerIdealPrevious_val, finerIdealDifferential_val]
  exact LinearMap.congr_fun (actualIdealCoordinateDifferential_comp P.ideal p) x.val

abbrev finerIdealHomology (γ : Γ) (p : ℕ) :=
  Homology (finerIdealDifferential P ω hJ γ p) (finerIdealPrevious P ω hJ γ p)
    (finerIdealDifferential_comp P ω hJ γ p)

def initialFinerIdealDifferential (γ : Γ) (p : ℕ) :
    finerIdealPiece P ω γ (p+1) →ₗ[K] finerIdealPiece P ω γ p :=
  ((initialActualIdealDifferential P p).domRestrict
    (finerIdealPiece P ω γ (p+1))).codRestrict
      (finerIdealPiece P ω γ p)
      (fun x => map_mem_piece_of_basis_monoid (R := K)
        (X := Set.powersetCard V (p+1) →₀ P.ideal)
        (Y := Set.powersetCard V p →₀ P.ideal)
        (I := ActualIdealIndex P (p+1)) (J := ActualIdealIndex P p) (A := Γ)
        (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
        (fun a => Finsupp.weight ω (actualIdealDegree a))
        (fun a => Finsupp.weight ω (actualIdealDegree a))
        (initialActualIdealDifferential P p)
        (initialActualIdealDifferential_basis_regrade P (Finsupp.weight ω) p) γ x.property)

@[simp] theorem initialFinerIdealDifferential_val (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ (p+1)) :
    (initialFinerIdealDifferential P ω γ p x).val =
      initialActualIdealDifferential P p x.val := rfl

def initialFinerIdealPrevious (γ : Γ) : ∀ p,finerIdealPiece P ω γ p →ₗ[K] finerIdealPiece P ω γ p.pred
  | 0 => 0
  | p+1 => initialFinerIdealDifferential P ω γ p

@[simp] theorem initialFinerIdealPrevious_val (γ : Γ) (p : ℕ) (x : finerIdealPiece P ω γ p) :
    (initialFinerIdealPrevious P ω γ p x).val=initialActualIdealPrevious P p x.val := by
  cases p <;> rfl

theorem initialFinerIdealDifferential_comp (γ : Γ) (p : ℕ) :
    (initialFinerIdealPrevious P ω γ p).comp (initialFinerIdealDifferential P ω γ p)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (initialFinerIdealPrevious P ω γ p
    (initialFinerIdealDifferential P ω γ p x)).val = 0
  rw [initialFinerIdealPrevious_val, initialFinerIdealDifferential_val]
  exact LinearMap.congr_fun (initialActualIdealDifferential_comp P p) x.val

abbrev initialFinerIdealHomology (γ : Γ) (p : ℕ) :=
  Homology (initialFinerIdealDifferential P ω γ p) (initialFinerIdealPrevious P ω γ p)
    (initialFinerIdealDifferential_comp P ω γ p)

variable (ρ : Γ →+ ℤ) (hρ : ∀ v,ρ (ω v)=1)

include hρ in
theorem refinement_weight_degree (a : Exponent V) :
    ρ (Finsupp.weight ω a)=(a.degree : ℤ) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb,Nat.cast_add]
  | single v n => simp only [Finsupp.weight_single,Finsupp.degree_single,map_nsmul,hρ,nsmul_eq_mul,mul_one]

abbrev FinerDegreeIndex (γ : Γ) := {a : Exponent V // Finsupp.weight ω a=γ}

include ρ hρ in
theorem finerDegreeIndex_finite (γ : Γ) : Finite (FinerDegreeIndex ω γ) := by
  let Q := {a : Exponent V // a.degree≤(ρ γ).toNat}
  letI : Finite Q := (Finsupp.finite_of_degree_le (ρ γ).toNat).to_subtype
  have hb (a : FinerDegreeIndex ω γ) : a.val.degree≤(ρ γ).toNat := by
    have he := refinement_weight_degree ω ρ hρ a.val
    rw [a.property] at he
    omega
  exact Finite.of_injective (fun a : FinerDegreeIndex ω γ => (⟨a.val,hb a⟩ : Q))
    (fun a b h => Subtype.ext (congrArg (fun z : Q => z.val) h))

include hρ in
/-- Labels of negative ordinary degree contain no polynomial Koszul chains.
This proves vanishing for all integer labels, rather than excluding them. -/
theorem finerIdealPiece_eq_bot_of_negative_refinement (γ : Γ) (p : ℕ)
    (hγ : ρ γ < 0) : finerIdealPiece P ω γ p = ⊥ := by
  apply bot_unique
  intro x hx
  apply (Submodule.mem_bot K).mpr
  apply (actualIdealCoefficientBasis P p).repr.injective
  ext a
  simp only [map_zero, Finsupp.zero_apply]
  by_contra ha
  have he := (Grading.mem_piece (actualIdealCoefficientBasis P p)
    (fun a => Finsupp.weight ω (actualIdealDegree a)) γ x).mp hx a ha
  have hd := refinement_weight_degree ω ρ hρ (actualIdealDegree a)
  rw [he] at hd
  omega

theorem finerIdealPiece_finite_of_finite_fiber (γ : Γ) (p : ℕ)
    [Finite (FinerDegreeIndex ω γ)] : Module.Finite K (finerIdealPiece P ω γ p) := by
  let f : {a : ActualIdealIndex P p // Finsupp.weight ω (actualIdealDegree a)=γ} →
      FinerDegreeIndex ω γ × Set.powersetCard V p := fun a => (⟨actualIdealDegree a.val,a.property⟩,a.val.1)
  have hf : Function.Injective f := by
    intro a b h
    have hF : a.val.1=b.val.1 := congrArg Prod.snd h
    have hdeg : actualIdealDegree a.val=actualIdealDegree b.val :=
      congrArg (fun z : FinerDegreeIndex ω γ × Set.powersetCard V p => z.1.val) h
    have ha : a.val.2.val=b.val.2.val := by
      change a.val.2.val+faceExponent a.val.1.val=b.val.2.val+faceExponent b.val.1.val at hdeg
      rw [hF] at hdeg
      exact add_right_cancel hdeg
    apply Subtype.ext
    rcases a with ⟨⟨F,a⟩,hA⟩
    rcases b with ⟨⟨H,b⟩,hB⟩
    dsimp only at hF ha ⊢
    subst H
    exact congrArg (Sigma.mk F) (Subtype.ext ha)
  letI := Finite.of_injective f hf
  exact Module.Finite.of_basis (finerIdealBasis P ω γ p)

include ρ hρ in
theorem finerIdealPiece_finite (γ : Γ) (p : ℕ) : Module.Finite K (finerIdealPiece P ω γ p) := by
  letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite ω ρ hρ γ
  exact finerIdealPiece_finite_of_finite_fiber P ω γ p

/-- The intrinsic meaning of a grading refining ordinary degree: equal
weighted monomial labels have equal ordinary degrees. No homomorphism on
unused grading labels is required. -/
def RefinesOrdinaryDegree : Prop :=
  ∀ a b : Exponent V, Finsupp.weight ω a = Finsupp.weight ω b → a.degree = b.degree

include hρ in
theorem refinesOrdinaryDegree_of_hom : RefinesOrdinaryDegree ω := by
  intro a b hab
  have ha := refinement_weight_degree ω ρ hρ a
  have hb := refinement_weight_degree ω ρ hρ b
  have he := congrArg ρ hab
  rw [ha, hb] at he
  exact_mod_cast he

theorem finerDegreeIndex_finite_of_refines (href : RefinesOrdinaryDegree ω) (γ : Γ) :
    Finite (FinerDegreeIndex ω γ) := by
  classical
  by_cases h : Nonempty (FinerDegreeIndex ω γ)
  · obtain ⟨a⟩ := h
    let Q := {b : Exponent V // b.degree ≤ a.val.degree}
    letI : Finite Q := (Finsupp.finite_of_degree_le a.val.degree).to_subtype
    let f : FinerDegreeIndex ω γ → Q := fun b =>
      ⟨b.val, (href b.val a.val (b.property.trans a.property.symm)).le⟩
    exact Finite.of_injective f (fun b c he => Subtype.ext (congrArg (fun z : Q => z.val) he))
  · letI : IsEmpty (FinerDegreeIndex ω γ) := not_nonempty_iff.mp h
    infer_instance

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FinerIdealTor -/
section

/-! # The finer graded groups as submodules of actual derived Tor -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial FilteredHomology

universe u v
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  {Γ : Type v} [AddCommMonoid Γ]
  (P : QuotientGroebnerData V K) (ω : V → Γ)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω))

def finerIdealCyclesInclusion (γ : Γ) (p : ℕ) :
    LinearMap.ker (finerIdealPrevious P ω hJ γ p) →ₗ[K]
      LinearMap.ker (actualIdealPreviousDifferential P.ideal p) :=
  (((finerIdealPiece P ω γ p).subtype).comp
    (LinearMap.ker (finerIdealPrevious P ω hJ γ p)).subtype).codRestrict _ (by
      intro z
      change actualIdealPreviousDifferential P.ideal p z.val.val=0
      rw [← finerIdealPrevious_val P ω hJ γ p z.val]
      exact congrArg Subtype.val z.property)

theorem finerIdealDifferential_toPolynomialCoordinates (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ (p+1)) :
    (finerIdealDifferential P ω hJ γ p x).val =
      PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=P.ideal) p x.val := rfl

theorem finerIdealPrevious_toPolynomialCoordinates (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ p) :
    (finerIdealPrevious P ω hJ γ p x).val =
      PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=P.ideal) p x.val := by
  cases p <;> rfl

section
attribute [local irreducible] finerIdealPiece finerIdealDifferential finerIdealPrevious
  PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option backward.isDefEq.respectTransparency true in
def finerIdealHomologyInclusion (γ : Γ) (p : ℕ) :
    finerIdealHomology P ω hJ γ p →ₗ[K] actualIdealCoordinateHomology P p :=
  threeTermHomologyMap (K:=K)
    (X:=finerIdealPiece P ω γ (p+1)) (Y:=finerIdealPiece P ω γ p)
    (Z:=finerIdealPiece P ω γ p.pred)
    (X':=Set.powersetCard V (p+1) →₀ P.ideal)
    (Y':=Set.powersetCard V p →₀ P.ideal)
    (Z':=Set.powersetCard V p.pred →₀ P.ideal)
    (finerIdealDifferential P ω hJ γ p) (finerIdealPrevious P ω hJ γ p)
    (finerIdealDifferential_comp P ω hJ γ p)
    (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=P.ideal) p)
    (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=P.ideal) p)
    (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=P.ideal) p)
    (finerIdealPiece P ω γ (p+1)).subtype (finerIdealPiece P ω γ p).subtype
    (finerIdealPiece P ω γ p.pred).subtype
    (finerIdealDifferential_toPolynomialCoordinates P ω hJ γ p)
    (finerIdealPrevious_toPolynomialCoordinates P ω hJ γ p)
end

/-- A homogeneous boundary is filled by the corresponding homogeneous
projection of any ambient filling. -/
theorem finerIdeal_boundary_reflects (γ : Γ) (p : ℕ)
    (z : finerIdealPiece P ω γ p)
    (a : Set.powersetCard V (p+1) →₀ P.ideal)
    (ha : PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=P.ideal) p a = z.val) :
    ∃ y, finerIdealDifferential P ω hJ γ p y = z := by
  let y : finerIdealPiece P ω γ (p+1) :=
    ⟨Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun b => Finsupp.weight ω (actualIdealDegree b)) γ a, Grading.projection_mem _ _ _ _⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hc := LinearMap.congr_fun (fineProjection_commutes (R:=K)
    (X:=Set.powersetCard V (p+1) →₀ P.ideal)
    (Y:=Set.powersetCard V p →₀ P.ideal)
    (I:=ActualIdealIndex P (p+1)) (J:=ActualIdealIndex P p) (Γ:=Γ)
    (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
    (fun b => Finsupp.weight ω (actualIdealDegree b))
    (fun b => Finsupp.weight ω (actualIdealDegree b))
    (actualIdealCoordinateDifferential P.ideal p)
    (fun b => actualIdealCoordinateDifferential_finer P ω hJ _ p _
      (Grading.basis_mem_piece _ _ b)) γ) a
  change actualIdealCoordinateDifferential P.ideal p
    (Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ a) =
    Grading.projection (actualIdealCoefficientBasis P p)
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ
      (actualIdealCoordinateDifferential P.ideal p a) at hc
  change actualIdealCoordinateDifferential P.ideal p a = z.val at ha
  change actualIdealCoordinateDifferential P.ideal p
    (Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ a) = z.val
  rw [hc, ha, Grading.projection_eq_self z.property]

section
attribute [local irreducible] finerIdealPiece finerIdealDifferential finerIdealPrevious
  PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option backward.isDefEq.respectTransparency true in
theorem finerIdealHomologyInclusion_injective (γ : Γ) (p : ℕ) :
    Function.Injective (finerIdealHomologyInclusion P ω hJ γ p) := by
  unfold finerIdealHomologyInclusion
  apply threeTermHomologyMap_injective_of_reflects_boundaries
  intro z _ hz
  obtain ⟨a, ha⟩ := hz
  exact finerIdeal_boundary_reflects P ω hJ γ p z a ha
end

def finerIdealHomologyToTor (γ : Γ) (p : ℕ) :
    finerIdealHomology P ω hJ γ p →ₗ[K] actualIdealTor P p :=
  ((PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=P.ideal) p).toLinearEquiv.symm.toLinearMap).comp
    (finerIdealHomologyInclusion P ω hJ γ p)

theorem finerIdealHomologyToTor_injective (γ : Γ) (p : ℕ) :
    Function.Injective (finerIdealHomologyToTor P ω hJ γ p) :=
  (PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=P.ideal) p).toLinearEquiv.symm.injective.comp
    (finerIdealHomologyInclusion_injective P ω hJ γ p)

def finerIdealGradedTor (γ : Γ) (p : ℕ) : Submodule K (actualIdealTor P p) :=
  LinearMap.range (finerIdealHomologyToTor P ω hJ γ p)

def finerIdealGradedTorEquiv (γ : Γ) (p : ℕ) :
    finerIdealHomology P ω hJ γ p ≃ₗ[K] finerIdealGradedTor P ω hJ γ p :=
  LinearEquiv.ofInjective (finerIdealHomologyToTor P ω hJ γ p)
    (finerIdealHomologyToTor_injective P ω hJ γ p)

theorem initialFinerPiece_mem_polynomial (γ : Γ) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) :
    actualIdealMonomialEquiv P p x∈polynomialWeightedCoordinatePiece ω (monomialIdeal K P.family) γ p ↔
      x∈finerIdealPiece P ω γ p := by
  change initialIdealAmbientMap P p x ∈
    Grading.Piece (quotientCoefficientBasis (k := K) (∅ : Family V) p)
      (fun a => Finsupp.weight ω (quotientDegree a)) γ ↔ x ∈ finerIdealPiece P ω γ p
  constructor
  · intro hx
    rw [finerIdealPiece, Grading.mem_piece]
    intro a ha
    apply (Grading.mem_piece
      (quotientCoefficientBasis (k := K) (∅ : Family V) p)
      (fun b => Finsupp.weight ω (quotientDegree b)) γ _).mp hx
        (actualIdealAmbientIndex P p a)
    simpa only [initialIdealAmbient_repr] using ha
  · exact map_mem_piece_of_basis_monoid (R := K)
      (X := Set.powersetCard V p →₀ P.ideal)
      (Y := AmbientKoszulCoordinates (k := K) (V := V) p)
      (I := ActualIdealIndex P p) (J := QuotientIndex (∅ : Family V) p) (A := Γ)
      (actualIdealCoefficientBasis P p)
      (quotientCoefficientBasis (k := K) (∅ : Family V) p)
      (fun a => Finsupp.weight ω (actualIdealDegree a))
      (fun a => Finsupp.weight ω (quotientDegree a)) (initialIdealAmbientMap P p)
      (fun a => by
        rw [initialIdealAmbient_basis]
        exact Grading.basis_mem_piece _ _ (actualIdealAmbientIndex P p a)) γ

def initialFinerCyclesInclusion (γ : Γ) (p : ℕ) :
    LinearMap.ker (initialFinerIdealPrevious P ω γ p) →ₗ[K]
      LinearMap.ker (PolynomialCoordinateTor.previous (K:=K) (V:=V)
        (M:=monomialIdeal K P.family) p) :=
  ((actualIdealMonomialEquiv P p).toLinearMap.comp
    (((finerIdealPiece P ω γ p).subtype).comp
      (LinearMap.ker (initialFinerIdealPrevious P ω γ p)).subtype)).codRestrict _ (by
        intro z
        cases p with
        | zero => rfl
        | succ p =>
          change monomialDifferential P.family p (actualIdealMonomialEquiv P (p+1) z.val.val)=0
          rw [← actualIdealMonomialEquiv_differential]
          have hz := congrArg Subtype.val z.property
          change initialActualIdealDifferential P p z.val.val=0 at hz
          rw [hz,map_zero])

def initialFinerCoordinateMap (γ : Γ) (p : ℕ) :
    finerIdealPiece P ω γ p →ₗ[K]
      PolynomialCoordinateTor.Coordinates (V:=V) (M:=monomialIdeal K P.family) p :=
  (actualIdealMonomialEquiv P p).toLinearMap.comp (finerIdealPiece P ω γ p).subtype

theorem initialFinerCoordinateMap_differential (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ (p+1)) :
    initialFinerCoordinateMap P ω γ p (initialFinerIdealDifferential P ω γ p x) =
      PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=monomialIdeal K P.family) p
        (initialFinerCoordinateMap P ω γ (p+1) x) :=
  actualIdealMonomialEquiv_differential P p x.val

theorem initialFinerCoordinateMap_previous (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ p) :
    initialFinerCoordinateMap P ω γ p.pred (initialFinerIdealPrevious P ω γ p x) =
      PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=monomialIdeal K P.family) p
        (initialFinerCoordinateMap P ω γ p x) := by
  cases p with
  | zero => exact (initialFinerCoordinateMap P ω γ 0).map_zero
  | succ p => exact initialFinerCoordinateMap_differential P ω γ p x

section
attribute [local irreducible] finerIdealPiece initialFinerIdealDifferential
  initialFinerIdealPrevious PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option backward.isDefEq.respectTransparency true in
def initialFinerHomologyInclusion (γ : Γ) (p : ℕ) :
    initialFinerIdealHomology P ω γ p →ₗ[K]
      PolynomialCoordinateTor.Homology (K:=K) (V:=V) (M:=monomialIdeal K P.family) p :=
  threeTermHomologyMap (K:=K)
    (X:=finerIdealPiece P ω γ (p+1)) (Y:=finerIdealPiece P ω γ p)
    (Z:=finerIdealPiece P ω γ p.pred)
    (X':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=monomialIdeal K P.family) (p+1))
    (Y':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=monomialIdeal K P.family) p)
    (Z':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=monomialIdeal K P.family) p.pred)
    (initialFinerIdealDifferential P ω γ p) (initialFinerIdealPrevious P ω γ p)
    (initialFinerIdealDifferential_comp P ω γ p)
    (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=monomialIdeal K P.family) p)
    (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=monomialIdeal K P.family) p)
    (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=monomialIdeal K P.family) p)
    (initialFinerCoordinateMap P ω γ (p+1)) (initialFinerCoordinateMap P ω γ p)
    (initialFinerCoordinateMap P ω γ p.pred)
    (initialFinerCoordinateMap_differential P ω γ p)
    (initialFinerCoordinateMap_previous P ω γ p)
end

theorem initialFiner_boundary_reflects (γ : Γ) (p : ℕ)
    (z : finerIdealPiece P ω γ p)
    (a : PolynomialCoordinateTor.Coordinates (V:=V) (M:=monomialIdeal K P.family) (p+1))
    (ha : PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=monomialIdeal K P.family) p a =
      initialFinerCoordinateMap P ω γ p z) :
    ∃ y, initialFinerIdealDifferential P ω γ p y = z := by
  change monomialDifferential P.family p a = actualIdealMonomialEquiv P p z.val at ha
  let b := (actualIdealMonomialEquiv P (p+1)).symm a
  have hdb : initialActualIdealDifferential P p b = z.val := by
    apply (actualIdealMonomialEquiv P p).injective
    rw [actualIdealMonomialEquiv_differential, LinearEquiv.apply_symm_apply, ha]
  let y : finerIdealPiece P ω γ (p+1) :=
    ⟨Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ b, Grading.projection_mem _ _ _ _⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hc := LinearMap.congr_fun (fineProjection_commutes (R:=K)
    (X:=Set.powersetCard V (p+1) →₀ P.ideal)
    (Y:=Set.powersetCard V p →₀ P.ideal)
    (I:=ActualIdealIndex P (p+1)) (J:=ActualIdealIndex P p) (Γ:=Γ)
    (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
    (fun i => Finsupp.weight ω (actualIdealDegree i))
    (fun i => Finsupp.weight ω (actualIdealDegree i))
    (initialActualIdealDifferential P p)
    (initialActualIdealDifferential_basis_regrade P (Finsupp.weight ω) p) γ) b
  change initialActualIdealDifferential P p
    (Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ b) =
    Grading.projection (actualIdealCoefficientBasis P p)
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ
      (initialActualIdealDifferential P p b) at hc
  change initialActualIdealDifferential P p
    (Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun i => Finsupp.weight ω (actualIdealDegree i)) γ b) = z.val
  rw [hc, hdb, Grading.projection_eq_self z.property]

section
attribute [local irreducible] finerIdealPiece initialFinerIdealDifferential
  initialFinerIdealPrevious PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option backward.isDefEq.respectTransparency true in
theorem initialFinerHomologyInclusion_injective (γ : Γ) (p : ℕ) :
    Function.Injective (initialFinerHomologyInclusion P ω γ p) := by
  unfold initialFinerHomologyInclusion
  apply threeTermHomologyMap_injective_of_reflects_boundaries
  intro z _ hz
  obtain ⟨a, ha⟩ := hz
  exact initialFiner_boundary_reflects P ω γ p z a ha
end

def initialFinerHomologyToTor (γ : Γ) (p : ℕ) :
    initialFinerIdealHomology P ω γ p →ₗ[K]
      PolynomialCoordinateTor.Tor (K:=K) (V:=V) (M:=monomialIdeal K P.family) p :=
  ((PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=monomialIdeal K P.family) p).toLinearEquiv.symm.toLinearMap).comp
    (initialFinerHomologyInclusion P ω γ p)

def initialFinerGradedTor (γ : Γ) (p : ℕ) : Submodule K
    (PolynomialCoordinateTor.Tor (K:=K) (V:=V) (M:=monomialIdeal K P.family) p) :=
  LinearMap.range (initialFinerHomologyToTor P ω γ p)

def initialFinerGradedTorEquiv (γ : Γ) (p : ℕ) :
    initialFinerIdealHomology P ω γ p ≃ₗ[K] initialFinerGradedTor P ω γ p :=
  LinearEquiv.ofInjective (initialFinerHomologyToTor P ω γ p)
    ((PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=monomialIdeal K P.family) p).toLinearEquiv.symm.injective.comp
      (initialFinerHomologyInclusion_injective P ω γ p))

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FinerIdealBettiComparison -/
section

/-! # The full finer-grading clause of the first-power criterion -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical CommAlg MvPolynomial FilteredHomology

universe u v
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  {Γ : Type v} [AddCommMonoid Γ]
  (P : QuotientGroebnerData V K) (ω : V → Γ)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω))
  (ρ : Γ →+ ℤ) (hρ : ∀ v,ρ (ω v)=1)

def finerFineAssignment (γ : Γ) (p : ℕ)
    (a : {a : ActualIdealIndex P p // Finsupp.weight ω (actualIdealDegree a)=γ}) :
    FinerDegreeIndex ω γ := ⟨actualIdealDegree a.val,a.property⟩

theorem finerIdeal_ordered_lifts_of_coordinate_lifts (γ : Γ) (p : ℕ)
    (hlift : ActualIdealOrderedLifts P p) :
    BasisCycleLifting.LinearLifts (finerIdealBasis P ω γ p) (finerIdealBasis P ω γ p.pred)
      (fun a => P.order.toSyn (actualIdealDegree a.val))
      (fun b => P.order.toSyn (actualIdealDegree b.val)) (finerIdealPrevious P ω hJ γ p) := by
  intro n x hx hdx
  have hdx' : actualIdealPreviousDifferential P.ideal p x.val ∈
      BasisCycleLifting.lower (actualIdealCoefficientBasis P p.pred)
        (fun a => P.order.toSyn (actualIdealDegree a)) n := by
    have he := (finerIdealBasis_span_mem_iff P ω γ p.pred
      {a | P.order.toSyn (actualIdealDegree a)<n} (finerIdealPrevious P ω hJ γ p x)).mp hdx
    rwa [finerIdealPrevious_val] at he
  obtain ⟨y,hy,hdy,herr⟩ := hlift n x.val
    ((finerIdealBasis_span_mem_iff P ω γ p
      {a | P.order.toSyn (actualIdealDegree a)≤n} x).mp hx) hdx'
  let z : finerIdealPiece P ω γ p :=
    ⟨Grading.projection (actualIdealCoefficientBasis P p)
      (fun a => Finsupp.weight ω (actualIdealDegree a)) γ y,Grading.projection_mem _ _ _ _⟩
  refine ⟨z,?_,?_,?_⟩
  · apply (finerIdealBasis_span_mem_iff P ω γ p
      {a | P.order.toSyn (actualIdealDegree a)≤n} z).mpr
    exact projection_preserves_basisSpan_monoid (R := K)
      (X := Set.powersetCard V p →₀ P.ideal) (I := ActualIdealIndex P p) (A := Γ)
      (actualIdealCoefficientBasis P p) (fun a => Finsupp.weight ω (actualIdealDegree a)) γ
      {a | P.order.toSyn (actualIdealDegree a)≤n} y hy
  · apply Subtype.ext
    cases p with
    | zero => rfl
    | succ p =>
      have he := LinearMap.congr_fun (fineProjection_commutes (R := K)
        (X := Set.powersetCard V (p+1) →₀ P.ideal)
        (Y := Set.powersetCard V p →₀ P.ideal)
        (I := ActualIdealIndex P (p+1)) (J := ActualIdealIndex P p) (Γ := Γ)
        (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
        (fun a => Finsupp.weight ω (actualIdealDegree a))
        (fun a => Finsupp.weight ω (actualIdealDegree a))
        (actualIdealCoordinateDifferential P.ideal p)
        (fun a => actualIdealCoordinateDifferential_finer P ω hJ _ p _
          (Grading.basis_mem_piece _ _ a)) γ) y
      change actualIdealCoordinateDifferential P.ideal p y = 0 at hdy
      change actualIdealCoordinateDifferential P.ideal p
        (Grading.projection (actualIdealCoefficientBasis P (p+1))
          (fun a => Finsupp.weight ω (actualIdealDegree a)) γ y) = 0
      simpa only [LinearMap.comp_apply, hdy, map_zero] using he
  · apply (finerIdealBasis_span_mem_iff P ω γ p
      {a | P.order.toSyn (actualIdealDegree a)<n} (x-z)).mpr
    change x.val - Grading.projection (actualIdealCoefficientBasis P p)
      (fun a => Finsupp.weight ω (actualIdealDegree a)) γ y ∈ _
    have he := projection_preserves_basisSpan_monoid (R := K)
      (X := Set.powersetCard V p →₀ P.ideal) (I := ActualIdealIndex P p) (A := Γ)
      (actualIdealCoefficientBasis P p)
      (fun a => Finsupp.weight ω (actualIdealDegree a)) γ
      {a | P.order.toSyn (actualIdealDegree a)<n} (x.val-y) herr
    rw [actualIdealCoordinate_sub_eq_add_neg_one_smul P p x.val y,
      map_add, map_smul, Grading.projection_eq_self x.property,
      ← actualIdealCoordinate_sub_eq_add_neg_one_smul P p x.val
        (Grading.projection (actualIdealCoefficientBasis P p)
          (fun a => Finsupp.weight ω (actualIdealDegree a)) γ y)] at he
    exact he

theorem finerIdeal_kernel_eq_of_finite_fiber (γ : Γ) (p : ℕ)
    [Finite (FinerDegreeIndex ω γ)]
    (hlift : ActualIdealOrderedLifts P p) :
    Module.finrank K (LinearMap.ker (finerIdealPrevious P ω hJ γ p))=
      Module.finrank K (LinearMap.ker (initialFinerIdealPrevious P ω γ p)) := by
  letI : FiniteDimensional K (finerIdealPiece P ω γ p) := finerIdealPiece_finite_of_finite_fiber P ω γ p
  letI : FiniteDimensional K (finerIdealPiece P ω γ p.pred) :=
    finerIdealPiece_finite_of_finite_fiber P ω γ p.pred
  letI : Fintype (FinerDegreeIndex ω γ) := Fintype.ofFinite _
  apply FiniteBasedComparison.kernel_finrank_eq_of_orderedLifts
    (finerIdealBasis P ω γ p) (finerIdealBasis P ω γ p.pred)
    (finerFineAssignment P ω γ p) (finerFineAssignment P ω γ p.pred)
    (fun a : FinerDegreeIndex ω γ => P.order.toSyn a.val)
    (finerIdealPrevious P ω hJ γ p) (initialFinerIdealPrevious P ω γ p)
  · intro a b hb
    have hb' : (actualIdealCoefficientBasis P p.pred).repr
        (initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a.val)) b.val≠0 := by
      simpa only [finerIdealBasis_repr,initialFinerIdealPrevious_val,
        finerIdealBasis_val] using hb
    exact (Grading.mem_piece _ _ _ _).mp
      (initialActualIdealPrevious_basis_regrade P P.order.toSyn p a.val) b.val hb'
  · intro a b hab
    have h0 := actualIdealPrevious_order_leading P p a.val b.val hab
    rw [actualIdealCoefficientBasis_repr_sub P p.pred] at h0
    have he := sub_eq_zero.mp h0
    simpa only [finerIdealBasis_repr,finerIdealPrevious_val,
      initialFinerIdealPrevious_val,finerIdealBasis_val] using he
  · exact finerIdeal_ordered_lifts_of_coordinate_lifts P ω hJ γ p hlift

include ρ hρ in
theorem finerIdeal_kernel_eq_of_ordered_lifts (γ : Γ) (p : ℕ)
    (hlift : ActualIdealOrderedLifts P p) :
    Module.finrank K (LinearMap.ker (finerIdealPrevious P ω hJ γ p)) =
      Module.finrank K (LinearMap.ker (initialFinerIdealPrevious P ω γ p)) := by
  letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite ω ρ hρ γ
  exact finerIdeal_kernel_eq_of_finite_fiber P ω hJ γ p hlift

theorem finerIdealHomology_finrank_eq_initial_of_finite_fiber
    (hlift : ∀ p,ActualIdealOrderedLifts P p) (γ : Γ) (p : ℕ)
    [Finite (FinerDegreeIndex ω γ)] :
    Module.finrank K (finerIdealHomology P ω hJ γ p)=
      Module.finrank K (initialFinerIdealHomology P ω γ p) := by
  letI : ∀ r,FiniteDimensional K (finerIdealPiece P ω γ r) :=
    fun r => finerIdealPiece_finite_of_finite_fiber P ω γ r
  have hleft := finrank_homology_add_finrank_source
    (finerIdealDifferential P ω hJ γ p) (finerIdealPrevious P ω hJ γ p)
    (finerIdealDifferential_comp P ω hJ γ p)
  have hright := finrank_homology_add_finrank_source
    (initialFinerIdealDifferential P ω γ p) (initialFinerIdealPrevious P ω γ p)
    (initialFinerIdealDifferential_comp P ω γ p)
  have hin := finerIdeal_kernel_eq_of_finite_fiber P ω hJ γ (p+1) (hlift (p+1))
  have hout := finerIdeal_kernel_eq_of_finite_fiber P ω hJ γ p (hlift p)
  change Module.finrank K (LinearMap.ker (finerIdealDifferential P ω hJ γ p))=
    Module.finrank K (LinearMap.ker (initialFinerIdealDifferential P ω γ p)) at hin
  change Module.finrank K (finerIdealHomology P ω hJ γ p) +
      Module.finrank K (finerIdealPiece P ω γ (p+1)) =
    Module.finrank K (LinearMap.ker (finerIdealPrevious P ω hJ γ p)) +
      Module.finrank K (LinearMap.ker (finerIdealDifferential P ω hJ γ p)) at hleft
  change Module.finrank K (initialFinerIdealHomology P ω γ p) +
      Module.finrank K (finerIdealPiece P ω γ (p+1)) =
    Module.finrank K (LinearMap.ker (initialFinerIdealPrevious P ω γ p)) +
      Module.finrank K (LinearMap.ker (initialFinerIdealDifferential P ω γ p)) at hright
  omega

include ρ hρ in
theorem finerIdealHomology_finrank_eq_initial_of_ordered_lifts
    (hlift : ∀ p,ActualIdealOrderedLifts P p) (γ : Γ) (p : ℕ) :
    Module.finrank K (finerIdealHomology P ω hJ γ p) =
      Module.finrank K (initialFinerIdealHomology P ω γ p) := by
  letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite ω ρ hρ γ
  exact finerIdealHomology_finrank_eq_initial_of_finite_fiber P ω hJ hlift γ p

def finerIdealBettiNumber (p : ℕ) (γ : Γ) : ℕ := Module.finrank K (finerIdealGradedTor P ω hJ γ p)
def initialFinerBettiNumber (p : ℕ) (γ : Γ) : ℕ := Module.finrank K (initialFinerGradedTor P ω γ p)

include hρ in
/-- The genuine Tor component is zero when its refined ordinary degree is
negative. The corresponding chain piece is already zero. -/
theorem finerIdealBettiNumber_eq_zero_of_negative_refinement (p : ℕ) (γ : Γ)
    (hγ : ρ γ < 0) : finerIdealBettiNumber P ω hJ p γ = 0 := by
  letI : Subsingleton (finerIdealPiece P ω γ p) :=
    Submodule.subsingleton_iff_eq_bot.mpr
      (finerIdealPiece_eq_bot_of_negative_refinement P ω ρ hρ γ p hγ)
  rw [finerIdealBettiNumber, ← (finerIdealGradedTorEquiv P ω hJ γ p).finrank_eq]
  exact Module.finrank_zero_of_subsingleton

include hρ in
theorem initialFinerBettiNumber_eq_zero_of_negative_refinement (p : ℕ) (γ : Γ)
    (hγ : ρ γ < 0) : initialFinerBettiNumber P ω p γ = 0 := by
  letI : Subsingleton (finerIdealPiece P ω γ p) :=
    Submodule.subsingleton_iff_eq_bot.mpr
      (finerIdealPiece_eq_bot_of_negative_refinement P ω ρ hρ γ p hγ)
  rw [initialFinerBettiNumber, ← (initialFinerGradedTorEquiv P ω γ p).finrank_eq]
  exact Module.finrank_zero_of_subsingleton

theorem finerIdealBettiNumber_eq_initial_of_finite_fiber
    (hlift : ∀ p,ActualIdealOrderedLifts P p) (p : ℕ) (γ : Γ)
    [Finite (FinerDegreeIndex ω γ)] :
    finerIdealBettiNumber P ω hJ p γ=initialFinerBettiNumber P ω p γ := by
  rw [finerIdealBettiNumber,initialFinerBettiNumber,
    ← (finerIdealGradedTorEquiv P ω hJ γ p).finrank_eq,
    ← (initialFinerGradedTorEquiv P ω γ p).finrank_eq]
  exact finerIdealHomology_finrank_eq_initial_of_finite_fiber P ω hJ hlift γ p

include ρ hρ in
theorem finerIdealBettiNumber_eq_initial_of_ordered_lifts
    (hlift : ∀ p,ActualIdealOrderedLifts P p) (p : ℕ) (γ : Γ) :
    finerIdealBettiNumber P ω hJ p γ = initialFinerBettiNumber P ω p γ := by
  letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite ω ρ hρ γ
  exact finerIdealBettiNumber_eq_initial_of_finite_fiber P ω hJ hlift p γ

end FourPapers.Sublattice

namespace FourPapers.Sublattice

open Classical MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u v
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J=finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1:ℕ))))
  {Γ : Type v} [AddCommMonoid Γ] (ω : FiniteVariable.{u} n → Γ)
  (ρ : Γ →+ ℤ) (hρ : ∀ v,ρ (ω v)=1)
  (hJω : J.IsHomogeneous (weightedHomogeneousSubmodule K ω))

include hJω in
theorem homogeneousIdealPowerWeighted (s : ℕ) :
    (J^s).IsHomogeneous (weightedHomogeneousSubmodule K ω) := by
  induction s with
  | zero => simpa only [pow_zero,Ideal.one_eq_top] using
      (Ideal.IsHomogeneous.top (weightedHomogeneousSubmodule K ω))
  | succ s ih => rw [pow_succ]; exact ih.mul hJω

include ρ hρ in
/-- Every finer additive grading respected by the degeneration and refining
ordinary internal degree has the same Betti numbers in every power. Both
sides are explicit graded submodules of their genuine derived Tor objects. -/
theorem theorem43_finer_betti
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q)
    (s p : ℕ) (γ : Γ) :
    finerIdealBettiNumber (sublatticePowerQuotientData n m J E hE hinit s) ω
      (homogeneousIdealPowerWeighted n J ω hJω s) p γ =
    initialFinerBettiNumber (sublatticePowerQuotientData n m J E hE hinit s) ω p γ :=
  finerIdealBettiNumber_eq_initial_of_ordered_lifts
    (sublatticePowerQuotientData n m J E hE hinit s) ω
    (homogeneousIdealPowerWeighted n J ω hJω s) ρ hρ
    (sublattice_all_power_ordered_lifts n m J E hE hinit hJ hβ s) p γ

/-- The unrestricted refinement formulation of the finer-grading clause:
only equality of monomial labels must imply equality of ordinary degrees.
There is no extension requirement on unused labels of the grading monoid. -/
theorem theorem43_finer_betti_of_refines
    (href : RefinesOrdinaryDegree ω)
    (hβ : ∀ p q, sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q)
    (s p : ℕ) (γ : Γ) :
    finerIdealBettiNumber (sublatticePowerQuotientData n m J E hE hinit s) ω
      (homogeneousIdealPowerWeighted n J ω hJω s) p γ =
    initialFinerBettiNumber (sublatticePowerQuotientData n m J E hE hinit s) ω p γ := by
  letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite_of_refines ω href γ
  exact finerIdealBettiNumber_eq_initial_of_finite_fiber
    (sublatticePowerQuotientData n m J E hE hinit s) ω
    (homogeneousIdealPowerWeighted n J ω hJω s)
    (sublattice_all_power_ordered_lifts n m J E hE hinit hJ hβ s) p γ

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientOrdinaryHomology -/
section

/-!
# Ordinary graded Tor of a coefficient quotient

The ordinary Koszul strand is defined on the original polynomial quotient.
Its actual cycle/boundary quotient is identified with the finite sum of fine
Tor pieces. Thus summing fine Betti numbers is a theorem about the usual
ordinary grading, rather than a substitute definition of that invariant.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
section General
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def ordinaryQuotientPiece (B : Family V) (q p : ℕ) :
    Submodule k (Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) :=
  Grading.Piece (quotientCoefficientBasis (k := k) B p) (fun t => (quotientDegree t).degree) q

instance ordinaryQuotientPiece_addCommGroup (B : Family V) (q p : ℕ) :
    AddCommGroup (ordinaryQuotientPiece (k := k) B q p) :=
  Submodule.addCommGroup (R := k)
    (M := Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) (ordinaryQuotientPiece B q p)

instance ordinaryQuotientPiece_module (B : Family V) (q p : ℕ) :
    Module k (ordinaryQuotientPiece (k := k) B q p) :=
  Submodule.module (R := k)
    (M := Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) (ordinaryQuotientPiece B q p)

lemma quotientDifferential_ordinary (B : Family V) (q p : ℕ)
    {x : Set.powersetCard V (p+1) →₀ CoefficientQuotient (k := k) B}
    (hx : x ∈ ordinaryQuotientPiece (k := k) B q (p+1)) :
    quotientDifferential (k := k) B p x ∈ ordinaryQuotientPiece (k := k) B q p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have hf := quotientDifferential_homogeneous (k := k) B (quotientDegree a) p
        (Grading.basis_mem_piece (quotientCoefficientBasis (k := k) B (p+1)) quotientDegree a)
      apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) hf
      change quotientDegree i = quotientDegree a at hi
      change (quotientDegree i).degree = q
      change (quotientDegree a).degree = q at ha
      rw [hi, ha]
  | zero => simpa only [map_zero] using
      (Submodule.zero_mem (ordinaryQuotientPiece (k := k) B q p))
  | add x y hx hy ihx ihy => simpa only [map_add] using
      (Submodule.add_mem (ordinaryQuotientPiece (k := k) B q p) ihx ihy)
  | smul r x hx ih => simpa only [map_smul] using
      (Submodule.smul_mem (ordinaryQuotientPiece (k := k) B q p) r ih)

def ordinaryQuotientDifferential (B : Family V) (q p : ℕ) :
    ordinaryQuotientPiece (k := k) B q (p+1) →ₗ[k] ordinaryQuotientPiece (k := k) B q p :=
  ((quotientDifferential (k := k) B p).domRestrict _).codRestrict _
    (fun x => quotientDifferential_ordinary (k := k) B q p x.property)

def ordinaryQuotientPrevious (B : Family V) (q : ℕ) : ∀ p : ℕ,
    ordinaryQuotientPiece (k := k) B q p →ₗ[k] ordinaryQuotientPiece (k := k) B q p.pred
  | 0 => 0
  | p+1 => ordinaryQuotientDifferential (k := k) B q p

@[simp] lemma ordinaryQuotientPrevious_val (B : Family V) (q p : ℕ)
    (x : ordinaryQuotientPiece (k := k) B q p) :
    (ordinaryQuotientPrevious (k := k) B q p x).val = quotientPreviousDifferential (k := k) B p x.val := by
  cases p <;> rfl

lemma ordinaryQuotientDifferential_comp (B : Family V) (q p : ℕ) :
    (ordinaryQuotientPrevious (k := k) B q p).comp
      (ordinaryQuotientDifferential (k := k) B q p) = 0 := by
  cases p with
  | zero => simp only [ordinaryQuotientPrevious, LinearMap.zero_comp]
  | succ p =>
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (quotientDifferential_comp (k := k) B p) x.val

abbrev ordinaryQuotientHomology (B : Family V) (q p : ℕ) :=
  FourPapers.FilteredHomology.Homology (K := k)
    (X := ordinaryQuotientPiece (k := k) B q (p+1))
    (Y := ordinaryQuotientPiece (k := k) B q p)
    (Z := ordinaryQuotientPiece (k := k) B q p.pred)
    (ordinaryQuotientDifferential (k := k) B q p)
    (ordinaryQuotientPrevious (k := k) B q p) (ordinaryQuotientDifferential_comp (k := k) B q p)

instance quotientFinePiece_addCommGroup (B : Family V) (α : Exponent V) (p : ℕ) :
    AddCommGroup (quotientPiece (k := k) B α p) :=
  Submodule.addCommGroup (R := k)
    (M := Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) (quotientPiece B α p)

instance quotientFinePiece_module (B : Family V) (α : Exponent V) (p : ℕ) :
    Module k (quotientPiece (k := k) B α p) :=
  Submodule.module (R := k)
    (M := Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) (quotientPiece B α p)

def quotientFinePrevious (B : Family V) (α : Exponent V) : ∀ p : ℕ,
    quotientPiece (k := k) B α p →ₗ[k] quotientPiece (k := k) B α p.pred
  | 0 => 0
  | p+1 => quotientHomogeneousDifferential (k := k) B α p

lemma quotientFineDifferential_comp (B : Family V) (α : Exponent V) (p : ℕ) :
    (quotientFinePrevious (k := k) B α p).comp (quotientHomogeneousDifferential (k := k) B α p) = 0 := by
  cases p with
  | zero => simp only [quotientFinePrevious, LinearMap.zero_comp]
  | succ p => exact quotientHomogeneousDifferential_comp (k := k) B α p

abbrev quotientFineHomologyAt (B : Family V) (α : Exponent V) (p : ℕ) :=
  FourPapers.FilteredHomology.Homology (K := k)
    (X := quotientPiece (k := k) B α (p+1))
    (Y := quotientPiece (k := k) B α p)
    (Z := quotientPiece (k := k) B α p.pred)
    (quotientHomogeneousDifferential (k := k) B α p)
    (quotientFinePrevious (k := k) B α p) (quotientFineDifferential_comp (k := k) B α p)

def ordinaryQuotientPieceEquivPi (B : Family V) (q p : ℕ) :
    ordinaryQuotientPiece (k := k) B q p ≃ₗ[k]
      ∀ α : OrdinaryFineIndex V q, quotientPiece (k := k) B α.val p where
  toFun x α := ⟨quotientProjection (k := k) B α.val p x.val,
    quotientProjection_mem (k := k) B α.val p x.val⟩
  invFun y := ⟨∑ α, (y α).val, by
    apply Submodule.sum_mem
    intro α _
    apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) (y α).property
    change quotientDegree i = α.val at hi
    change (quotientDegree i).degree = q
    rw [hi, α.property]⟩
  left_inv x := by
    apply Subtype.ext
    apply (quotientCoefficientBasis (k := k) B p).repr.injective
    ext i
    simp only [map_sum, Finsupp.finset_sum_apply, quotientProjection,
      Grading.projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Grading.filterMap_apply, Finsupp.filter_apply]
    by_cases hz : (quotientCoefficientBasis (k := k) B p).repr x.val i = 0
    · simp only [hz, ite_self, Finset.sum_const_zero]
    · have hi := (Grading.mem_piece (quotientCoefficientBasis (k := k) B p) (fun i => (quotientDegree i).degree) q x.val).mp
        x.property i hz
      let α : OrdinaryFineIndex V q := ⟨quotientDegree i, hi⟩
      rw [Finset.sum_eq_single α]
      · simp only [α, ite_true]
      · intro β _ hβα
        apply if_neg
        intro he
        exact hβα (Subtype.ext he.symm)
      · simp
  right_inv y := by
    funext α
    apply Subtype.ext
    change quotientProjection (k := k) B α.val p (∑ β, (y β).val) = (y α).val
    rw [map_sum, Finset.sum_eq_single α]
    · exact Grading.projection_eq_self (y α).property
    · intro β _ hβα
      apply Grading.projection_eq_zero _ (y β).property
      intro he
      exact hβα (Subtype.ext he.symm)
    · simp
  map_add' x y := by
    funext α
    apply Subtype.ext
    exact map_add (quotientProjection (k := k) B α.val p) x.val y.val
  map_smul' r x := by
    funext α
    apply Subtype.ext
    exact map_smul (quotientProjection (k := k) B α.val p) r x.val

lemma ordinaryQuotientPieceEquivPi_differential (B : Family V) (q p : ℕ)
    (x : ordinaryQuotientPiece (k := k) B q (p+1)) (α : OrdinaryFineIndex V q) :
    ordinaryQuotientPieceEquivPi (k := k) B q p (ordinaryQuotientDifferential (k := k) B q p x) α =
      quotientHomogeneousDifferential (k := k) B α.val p (ordinaryQuotientPieceEquivPi (k := k) B q (p+1) x α) := by
  apply Subtype.ext
  change quotientProjection (k := k) B α.val p
    (quotientDifferential (k := k) B p x.val) =
      quotientDifferential (k := k) B p
        (quotientProjection (k := k) B α.val (p+1) x.val)
  exact LinearMap.congr_fun (quotientProjection_differential (k := k) B α.val p) x.val

lemma ordinaryQuotientPieceEquivPi_previous (B : Family V) (q p : ℕ)
    (x : ordinaryQuotientPiece (k := k) B q p) (α : OrdinaryFineIndex V q) :
    ordinaryQuotientPieceEquivPi (k := k) B q p.pred (ordinaryQuotientPrevious (k := k) B q p x) α =
      quotientFinePrevious (k := k) B α.val p (ordinaryQuotientPieceEquivPi (k := k) B q p x α) := by
  cases p with
  | zero =>
      apply Subtype.ext
      change Grading.projection (quotientCoefficientBasis (k := k) B 0)
        quotientDegree α.val 0 = 0
      exact map_zero _
  | succ p => exact ordinaryQuotientPieceEquivPi_differential (k := k) B q p x α

/-- The literal ordinary cycle/boundary quotient is the finite product of
the literal fine cycle/boundary quotients, including homological degree zero. -/
def ordinaryQuotientHomologyEquivPi (B : Family V) (q p : ℕ) :
    ordinaryQuotientHomology (k := k) B q p ≃ₗ[k]
      ∀ α : OrdinaryFineIndex V q, quotientFineHomologyAt (k := k) B α.val p := by
  let f := fun α : OrdinaryFineIndex V q => quotientHomogeneousDifferential (k := k) B α.val p
  let g := fun α : OrdinaryFineIndex V q => quotientFinePrevious (k := k) B α.val p
  let hfg := fun α : OrdinaryFineIndex V q => quotientFineDifferential_comp (k := k) B α.val p
  refine (threeTermHomologyEquiv (R := k)
    (X := ordinaryQuotientPiece (k := k) B q (p+1))
    (Y := ordinaryQuotientPiece (k := k) B q p)
    (Z := ordinaryQuotientPiece (k := k) B q p.pred)
    (X' := ∀ α : OrdinaryFineIndex V q, quotientPiece (k := k) B α.val (p+1))
    (Y' := ∀ α : OrdinaryFineIndex V q, quotientPiece (k := k) B α.val p)
    (Z' := ∀ α : OrdinaryFineIndex V q, quotientPiece (k := k) B α.val p.pred)
    (ordinaryQuotientDifferential (k := k) B q p) (ordinaryQuotientPrevious (k := k) B q p)
    (ordinaryQuotientDifferential_comp (k := k) B q p)
    (componentwiseMap f) (componentwiseMap g) (componentwiseMap_comp f g hfg)
    (ordinaryQuotientPieceEquivPi (k := k) B q (p+1)) (ordinaryQuotientPieceEquivPi (k := k) B q p)
    (ordinaryQuotientPieceEquivPi (k := k) B q p.pred) ?_ ?_).trans
      (componentwiseHomologyEquiv f g hfg)
  · intro x
    funext α
    exact ordinaryQuotientPieceEquivPi_differential (k := k) B q p x α
  · intro x
    funext α
    exact ordinaryQuotientPieceEquivPi_previous (k := k) B q p x α

/-- The three-term definition is exactly the categorical homology of the
genuine fine Koszul subcomplex; degree zero is not shifted or discarded. -/
def quotientFineCategoricalHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B α).homology p ≃ₗ[k] quotientFineHomologyAt (k := k) B α p := by
  let C := quotientHomogeneousComplex (k := k) B α
  let T := C.sc' (p+1) p p.pred
  have hfg : T.g.hom.comp T.f.hom = 0 := by
    apply LinearMap.ext
    intro x
    exact T.moduleCat_zero_apply x
  refine (((C.homologyIsoSc' (p+1) p p.pred (by simp) (by cases p <;> simp)) ≪≫
    T.moduleCatHomologyIso).toLinearEquiv).trans
      (threeTermHomologyEquiv T.f.hom T.g.hom hfg
        (quotientHomogeneousDifferential (k := k) B α p) (quotientFinePrevious (k := k) B α p)
        (quotientFineDifferential_comp (k := k) B α p)
        (LinearEquiv.refl k _) (LinearEquiv.refl k _) (LinearEquiv.refl k _) ?_ ?_)
  · intro x
    change ((quotientHomogeneousComplex (k := k) B α).d (p+1) p).hom x = quotientHomogeneousDifferential (k := k) B α p x
    rw [quotientHomogeneousComplex_d]
    rfl
  · intro x
    cases p with
    | zero =>
        change (C.d 0 0).hom x = 0
        rw [C.shape 0 0 (by simp)]
        rfl
    | succ p =>
        change ((quotientHomogeneousComplex (k := k) B α).d (p+1) p).hom x = quotientHomogeneousDifferential (k := k) B α p x
        rw [quotientHomogeneousComplex_d]
        rfl

end General
section Field
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance quotientFineHomologyAt_finite (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.Finite k (quotientFineHomologyAt (k := k) B α p) :=
  Module.Finite.equiv (quotientFineCategoricalHomologyEquiv (k := k) B α p)

lemma quotientFineHomologyAt_finrank (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.finrank k (quotientFineHomologyAt (k := k) B α p) = quotientBettiNumber (k := k) B α p :=
  (quotientFineCategoricalHomologyEquiv (k := k) B α p).finrank_eq.symm.trans
    (quotientGradedTorIso (k := k) B α p).toLinearEquiv.finrank_eq

/-- Ordinary Betti numbers are dimensions of actual ordinary Koszul
homology. The following theorem, rather than the definition, computes them
as the sum of the fine derived-Tor dimensions. -/
def ordinaryQuotientBettiNumber (B : Family V) (q p : ℕ) : ℕ :=
  Module.finrank k (ordinaryQuotientHomology (k := k) B q p)

theorem ordinaryQuotientBettiNumber_eq_sum (B : Family V) (q p : ℕ) :
    ordinaryQuotientBettiNumber (k := k) B q p =
      ∑ α : OrdinaryFineIndex V q, quotientBettiNumber (k := k) B α.val p := by
  rw [ordinaryQuotientBettiNumber, (ordinaryQuotientHomologyEquivPi (k := k) B q p).finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro α _
  exact quotientFineHomologyAt_finrank (k := k) B α.val p

end Field
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.ordinaryQuotientHomologyEquivPi
#print axioms FourPapers.Sublattice.ordinaryQuotientBettiNumber_eq_sum

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.StrictSupportBetti -/
section

/-!
# The strict-support formula for ordinary Betti numbers

First sum the proved fine Tor formula in a fixed ordinary degree. An explicit
bijection removes the chain's monomial shift. Then group weak chains by their
nonempty strict support; the generic positive-multiplicity theorem supplies
the binomial coefficient in Corollary 5.1.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid CommAlg.Koszul
open FourPapers.MultichainCounting
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Remove the fixed degree of the product indexing a chain. -/
def ordinaryAdmissibleChainEquiv (m q : ℕ) :
    (Σ α : OrdinaryFineIndex (FiniteVariable.{u} n) (m*d+q),
      AdmissibleChain n E m α.val) ≃
        (FiniteMultichain n E m × OrdinaryFineIndex (FiniteVariable.{u} n) q) where
  toFun x := ⟨x.2.val, ⟨x.1.val-finiteChainShift n x.2.val, by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le x.2.property)
    rw [map_add, finiteChainShift_degree, x.1.property] at h
    omega⟩⟩
  invFun x := ⟨⟨x.2.val+finiteChainShift n x.1, by
    rw [map_add, finiteChainShift_degree, x.2.property]
    omega⟩, ⟨x.1, by
      intro v
      simp only [Finsupp.add_apply]
      omega⟩⟩
  left_inv x := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact tsub_add_cancel_of_le x.2.property
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact add_tsub_cancel_right _ _

/-- The ordinary-degree specialization of the all-powers fine Tor formula. -/
theorem ordinaryPowerBetti_chain_sum {k : Type u} [Field k]
    (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) (m*d+q) p =
      ∑ w : FiniteMultichain n E m,
        ordinaryQuotientBettiNumber (k := k) (finiteChainCoefficientFamily n w) q p := by
  rw [ordinaryMonomialBettiNumber_eq_sum]
  simp_rw [allPowerBetti_admissible hE m hm p, ordinaryQuotientBettiNumber_eq_sum]
  rw [← Fintype.sum_sigma (f := fun x :
    Σ α : OrdinaryFineIndex (FiniteVariable.{u} n) (m*d+q), AdmissibleChain n E m α.val =>
      quotientBettiNumber (k := k) (finiteChainCoefficientFamily n x.2.val)
        (x.1.val-finiteChainShift n x.2.val) p)]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (ordinaryAdmissibleChainEquiv (E := E) m q) _ _ (fun _ => rfl)

/-- The omitted negative normalized degrees vanish in the actual ideal Tor. -/
theorem ordinaryPowerBetti_eq_zero_below {k : Type u} [Field k]
    (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) (Q p : ℕ)
    (hQ : Q < m*d) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) Q p = 0 := by
  rw [ordinaryMonomialBettiNumber_eq_sum]
  apply Finset.sum_eq_zero
  intro α _
  rw [allPowerBetti_admissible hE m hm p α.val]
  apply Finset.sum_eq_zero
  intro w _
  have h := Finsupp.degree_mono w.property
  rw [finiteChainShift_degree, α.property] at h
  omega

/-- Explicitly compare the paper's tuple type with the counting type. -/
def finiteMultichainTupleEquiv (m : ℕ) :
    FiniteMultichain n E m ≃ MonotoneTuple E m where
  toFun w := ⟨w.val, fun i j hij => w.property hij⟩
  invFun w := ⟨w.val, fun i j hij => w.property hij⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coefficient ideal depends only on the set of values of a chain. -/
def strictSupportCoefficientFamily (s : StrictSupport E) : Family (FiniteVariable.{u} n) :=
  s.val.biUnion fun a => finitePredecessorFamily n E a.val

lemma finiteChainCoefficientFamily_support {m : ℕ} (hm : 0 < m)
    (w : FiniteMultichain n E m) :
    finiteChainCoefficientFamily.{u} n w =
      strictSupportCoefficientFamily (tupleSupport hm w) := by
  ext g
  constructor
  · intro hg
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
    apply Finset.mem_biUnion.mpr
    exact ⟨w.val i, (tupleSupport_mem hm w _).mpr ⟨i, rfl⟩, hi⟩
  · intro hg
    obtain ⟨a, ha, hg⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨i, rfl⟩ := (tupleSupport_mem hm w a).mp ha
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hg⟩

lemma finiteMultichain_sum_by_support {m : ℕ} (hm : 0 < m)
    (f : StrictSupport E → ℕ) :
    (∑ w : FiniteMultichain n E m, f (tupleSupport hm w)) =
      ∑ s : StrictSupport E, (m-1).choose (s.val.card-1) * f s := by
  calc
    _ = ∑ w : MonotoneTuple E m, f (tupleSupport hm w) :=
      Fintype.sum_equiv (finiteMultichainTupleEquiv (n := n) (E := E) m) _ _ (fun _ => rfl)
    _ = _ := by
      convert sum_by_strict_support hm f using 1 <;> congr 1
      ext w
      simp

attribute [local irreducible] ordinaryQuotientBettiNumber

/-- Corollary 5.1, coefficient by coefficient in the ordinary Betti polynomial.
Both sides are dimensions of the actual cycle/boundary quotients. -/
theorem corollary51 {k : Type u} [Field k]
    (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) (m*d+q) p =
      ∑ s : StrictSupport E, (m-1).choose (s.val.card-1) *
        ordinaryQuotientBettiNumber (k := k) (strictSupportCoefficientFamily s) q p := by
  rw [ordinaryPowerBetti_chain_sum hE m hm]
  simp_rw [finiteChainCoefficientFamily_support hm]
  exact finiteMultichain_sum_by_support hm
    (fun s => ordinaryQuotientBettiNumber (k := k) (strictSupportCoefficientFamily s) q p)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.corollary51

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiPolynomial -/
section

/-!
# Polynomial Betti entries and all forward differences

The parameter of `normalizedBettiSequence` is one less than the power, so
its domain starts at zero and every value refers to a positive ideal power.
The polynomial assertion itself uses the original power parameter `m`.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
open FourPapers.MultichainCounting
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type u} [Field k]

def normalizedBettiSequence (q p t : ℕ) : ℕ :=
  ordinaryMonomialBettiNumber (k := k)
    (exponentPowerFamily (finiteRowFamily n E) (t+1)) ((t+1)*d+q) p

def strictSupportBettiCoefficient (q p : ℕ) (s : StrictSupport E) : ℕ :=
  ordinaryQuotientBettiNumber (k := k) (strictSupportCoefficientFamily s) q p

theorem normalizedBettiSequence_eq (hE : finiteLatticeClosed n E) (q p t : ℕ) :
    normalizedBettiSequence (k := k) (E := E) q p t =
      PositiveBinomialPolynomial.sequence
        (strictSupportBettiCoefficient (k := k) (E := E) q p) (fun s => s.val.card-1) t := by
  rw [normalizedBettiSequence, corollary51 hE (t+1) (Nat.zero_lt_succ t)]
  simp only [Nat.add_sub_cancel, PositiveBinomialPolynomial.sequence,
    strictSupportBettiCoefficient, mul_comm]

/-- A specific rational polynomial, with nonnegative binomial coefficients,
whose value is the normalized Betti entry at every positive power. -/
def normalizedBettiPolynomial (q p : ℕ) : Polynomial ℚ :=
  (PositiveBinomialPolynomial.polynomial
    (strictSupportBettiCoefficient (k := k) (E := E) q p)
    (fun s => s.val.card-1)).comp (Polynomial.X-Polynomial.C 1)

theorem corollary52_polynomial (hE : finiteLatticeClosed n E)
    (q p m : ℕ) (hm : 0 < m) :
    (normalizedBettiPolynomial (k := k) (E := E) q p).eval (m : ℚ) =
      (ordinaryMonomialBettiNumber (k := k)
        (exponentPowerFamily (finiteRowFamily n E) m) (m*d+q) p : ℚ) := by
  rw [normalizedBettiPolynomial, PositiveBinomialPolynomial.shifted_polynomial_eval _ _ m hm,
    ← normalizedBettiSequence_eq hE q p (m-1), normalizedBettiSequence,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]

/-- Corollary 5.2: every order of forward difference is nonnegative, with
ordinary integer subtraction throughout. -/
theorem corollary52_forward_differences (hE : finiteLatticeClosed n E)
    (q p j t : ℕ) :
    0 ≤ ((fwdDiff (1 : ℕ))^[j]
      (fun a => (normalizedBettiSequence (k := k) (E := E) q p a : ℤ))) t := by
  simp_rw [normalizedBettiSequence_eq hE q p]
  exact PositiveBinomialPolynomial.sequence_forward_differences_nonnegative _ _ j t

theorem normalizedBettiSequence_monotone (hE : finiteLatticeClosed n E) (q p : ℕ) :
    Monotone (normalizedBettiSequence (k := k) (E := E) q p) := by
  apply monotone_nat_of_le_succ
  intro t
  have h := corollary52_forward_differences (k := k) hE q p 1 t
  simp only [Function.iterate_one, fwdDiff] at h
  exact_mod_cast (sub_nonneg.mp h)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.corollary52_polynomial
#print axioms FourPapers.Sublattice.corollary52_forward_differences

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerQuotientHomology -/
section

/-! # Literal integer ordinary strands of coefficient quotients

Integer degree is obtained by regrading the polynomial-plus-exterior basis
along the inclusion of natural degrees into the integers. Both differentials
are restrictions of the original quotient Koszul differential. Negative
strands vanish because their chain modules have no basis vectors.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma integerRegrade_map_mem {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module k A] [Module k B] (f : A →ₗ[k] B) (P : ℕ → Submodule k A)
    (Q : ℕ → Submodule k B) (hf : ∀ n, ∀ x ∈ P n, f x ∈ Q n)
    (q : ℤ) {x : A} (hx : x ∈ ordinaryIntegerRegrade P q) :
    f x ∈ ordinaryIntegerRegrade Q q := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [ordinaryIntegerRegrade_nat] at hx ⊢
    exact hf n x hx
  · have hneg : q < 0 := lt_of_not_ge hq
    rw [ordinaryIntegerRegrade_negative _ _ hneg, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _

def integerOrdinaryQuotientPiece (B : Family V) (q : ℤ) (p : ℕ) :
    Submodule k (Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) :=
  ordinaryIntegerRegrade (fun n => ordinaryQuotientPiece (k := k) B n p) q

theorem integerOrdinaryQuotientPiece_eq (B : Family V) (q : ℤ) (p : ℕ) :
    integerOrdinaryQuotientPiece (k := k) B q p =
      Grading.Piece (quotientCoefficientBasis (k := k) B p)
        (fun a => ((quotientDegree a).degree : ℤ)) q :=
  ordinaryIntegerRegrade_basisPiece _ _ _

@[simp] theorem integerOrdinaryQuotientPiece_nat (B : Family V) (q p : ℕ) :
    integerOrdinaryQuotientPiece (k := k) B (q : ℤ) p = ordinaryQuotientPiece B q p :=
  ordinaryIntegerRegrade_nat _ _

def integerOrdinaryQuotientDifferential (B : Family V) (q : ℤ) (p : ℕ) :
    integerOrdinaryQuotientPiece (k := k) B q (p+1) →ₗ[k]
      integerOrdinaryQuotientPiece (k := k) B q p :=
  ((quotientDifferential (k := k) B p).domRestrict _).codRestrict _
    (fun x => integerRegrade_map_mem (quotientDifferential (k := k) B p)
      (fun n => ordinaryQuotientPiece B n (p+1))
      (fun n => ordinaryQuotientPiece B n p)
      (fun n _ hx => quotientDifferential_ordinary B n p hx) q x.property)

def integerOrdinaryQuotientPrevious (B : Family V) (q : ℤ) : ∀ p : ℕ,
    integerOrdinaryQuotientPiece (k := k) B q p →ₗ[k]
      integerOrdinaryQuotientPiece (k := k) B q p.pred
  | 0 => 0
  | p+1 => integerOrdinaryQuotientDifferential B q p

lemma integerOrdinaryQuotientDifferential_comp (B : Family V) (q : ℤ) (p : ℕ) :
    (integerOrdinaryQuotientPrevious (k := k) B q p).comp
      (integerOrdinaryQuotientDifferential B q p) = 0 := by
  cases p with
  | zero => simp only [integerOrdinaryQuotientPrevious, LinearMap.zero_comp]
  | succ p =>
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (quotientDifferential_comp (k := k) B p) x.val

abbrev integerOrdinaryQuotientHomology (B : Family V) (q : ℤ) (p : ℕ) :=
  Homology (K := k)
    (X := integerOrdinaryQuotientPiece (k := k) B q (p+1))
    (Y := integerOrdinaryQuotientPiece (k := k) B q p)
    (Z := integerOrdinaryQuotientPiece (k := k) B q p.pred)
    (integerOrdinaryQuotientDifferential (k := k) B q p)
    (integerOrdinaryQuotientPrevious B q p)
    (integerOrdinaryQuotientDifferential_comp B q p)

def integerOrdinaryQuotientPieceNatEquiv (B : Family V) (q p : ℕ) :
    integerOrdinaryQuotientPiece (k := k) B (q : ℤ) p ≃ₗ[k]
      ordinaryQuotientPiece (k := k) B q p :=
  LinearEquiv.ofEq _ _ (integerOrdinaryQuotientPiece_nat B q p)

def integerOrdinaryQuotientHomologyNatEquiv (B : Family V) (q p : ℕ) :
    integerOrdinaryQuotientHomology (k := k) B (q : ℤ) p ≃ₗ[k]
      ordinaryQuotientHomology (k := k) B q p := by
  apply threeTermHomologyEquiv (R := k)
    (X := integerOrdinaryQuotientPiece (k := k) B (q : ℤ) (p+1))
    (Y := integerOrdinaryQuotientPiece (k := k) B (q : ℤ) p)
    (Z := integerOrdinaryQuotientPiece (k := k) B (q : ℤ) p.pred)
    (X' := ordinaryQuotientPiece (k := k) B q (p+1))
    (Y' := ordinaryQuotientPiece (k := k) B q p)
    (Z' := ordinaryQuotientPiece (k := k) B q p.pred)
    (integerOrdinaryQuotientDifferential B (q : ℤ) p)
    (integerOrdinaryQuotientPrevious B (q : ℤ) p)
    (integerOrdinaryQuotientDifferential_comp B (q : ℤ) p)
    (ordinaryQuotientDifferential B q p) (ordinaryQuotientPrevious B q p)
    (ordinaryQuotientDifferential_comp B q p)
    (integerOrdinaryQuotientPieceNatEquiv B q (p+1))
    (integerOrdinaryQuotientPieceNatEquiv B q p)
    (integerOrdinaryQuotientPieceNatEquiv B q p.pred)
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    cases p <;> rfl

theorem integerOrdinaryQuotientHomology_negative (B : Family V) (q : ℤ)
    (hq : q < 0) (p : ℕ) :
    Subsingleton (integerOrdinaryQuotientHomology (k := k) B q p) := by
  have he : integerOrdinaryQuotientPiece (k := k) B q p = ⊥ :=
    ordinaryIntegerRegrade_negative _ _ hq
  letI : Subsingleton (integerOrdinaryQuotientPiece (k := k) B q p) := by
    rw [he]
    infer_instance
  unfold integerOrdinaryQuotientHomology Homology
  infer_instance

section Field
variable {K : Type u} [Field K]

def integerOrdinaryQuotientBettiNumber (B : Family V) (q : ℤ) (p : ℕ) : ℕ :=
  Module.finrank K (integerOrdinaryQuotientHomology (k := K) B q p)

@[simp] theorem integerOrdinaryQuotientBettiNumber_nat (B : Family V) (q p : ℕ) :
    integerOrdinaryQuotientBettiNumber (K := K) B (q : ℤ) p =
      ordinaryQuotientBettiNumber (k := K) B q p :=
  (integerOrdinaryQuotientHomologyNatEquiv (k := K) B q p).finrank_eq

theorem integerOrdinaryQuotientBettiNumber_negative (B : Family V) (q : ℤ)
    (hq : q < 0) (p : ℕ) : integerOrdinaryQuotientBettiNumber (K := K) B q p = 0 := by
  letI := integerOrdinaryQuotientHomology_negative (k := K) B q hq p
  exact Module.finrank_zero_of_subsingleton

end Field
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.integerOrdinaryQuotientHomologyNatEquiv
#print axioms FourPapers.Sublattice.integerOrdinaryQuotientHomology_negative

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialTorBetti -/
section

/-! # The canonical Tor coordinates of a monomial ideal

These general identifications do not depend on regularity, support bounds,
or graph resolutions. Every number below is a genuine derived-Tor dimension.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem monomialIdeal_isOrdinaryHomogeneous (B : Family V) :
    (monomialIdeal k B).IsHomogeneous
      (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))) := by
  apply Ideal.homogeneous_span
  rintro f ⟨a, ha, rfl⟩
  exact ⟨Finsupp.weight (fun _ : V => (1 : ℕ)) a,
    isWeightedHomogeneous_monomial _ a (1 : k) rfl⟩

/-- The ordinary graded Tor dimension of the literal monomial ideal.
The order is only used to choose its proved coordinate presentation. -/
def monomialTorBettiNumber (o : MonomialOrder V) (B : Family V) (p q : ℕ) : ℕ :=
  ordinaryIdealBettiNumber (canonicalQuotientGroebnerData o (monomialIdeal k B))
    (monomialIdeal_isOrdinaryHomogeneous B) p q

theorem monomialTorBettiNumber_eq (o : MonomialOrder V) (B : Family V) (p q : ℕ) :
    monomialTorBettiNumber (k := k) o B p q = ordinaryMonomialBettiNumber (k := k) B q p :=
  canonicalMonomialBettiNumber_eq o B (monomialIdeal_isOrdinaryHomogeneous B) q p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerMonomialTorBetti -/
section

/-! # Actual monomial Tor in every integer ordinary degree

The natural-degree formula and the vanishing in negative degrees are
proved for the literal monomial ideal. No Betti-polynomial machinery is
needed for these grading interfaces.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

/-- Genuine integer ordinary Tor dimension of the literal monomial ideal. -/
def integerMonomialTorBettiNumber (o : MonomialOrder V) (B : Family V)
    (p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber
    (canonicalQuotientGroebnerData o (monomialIdeal K B))
    (monomialIdeal_isOrdinaryHomogeneous B) p q

@[simp] theorem integerMonomialTorBettiNumber_nat (o : MonomialOrder V) (B : Family V)
    (p q : ℕ) : integerMonomialTorBettiNumber (K := K) o B p (q : ℤ) =
      ordinaryMonomialBettiNumber (k := K) B q p :=
  (ordinaryIntegerIdealBettiNumber_nat
    (canonicalQuotientGroebnerData o (monomialIdeal K B))
    (monomialIdeal_isOrdinaryHomogeneous B) p q).trans
      (monomialTorBettiNumber_eq o B p q)

theorem integerMonomialTorBettiNumber_negative (o : MonomialOrder V) (B : Family V)
    (p : ℕ) (q : ℤ) (hq : q < 0) :
    integerMonomialTorBettiNumber (K := K) o B p q = 0 :=
  ordinaryIntegerIdealBettiNumber_negative _ _ p q hq

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerBettiPolynomial -/
section

/-! # The finite Betti formula in every integer internal degree

The left side is a homogeneous submodule of genuine derived Tor. The
coefficient quotients use their literal integer-graded Koszul complexes.
Consequently the negative normalized degrees are proved to vanish; no
parameter range is silently removed from Corollaries 5.1 and 5.2.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid FourPapers.MultichainCounting MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (o : MonomialOrder (FiniteVariable.{u} n))

lemma integerPowerBetti_eq_zero_below (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) (hq : q < (m*d : ℕ)) :
    integerMonomialTorBettiNumber (K := K) o
      (exponentPowerFamily (finiteRowFamily n E) m) p q = 0 := by
  by_cases hq0 : 0 ≤ q
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
    rw [integerMonomialTorBettiNumber_nat]
    exact ordinaryPowerBetti_eq_zero_below hE m hm a p (by exact_mod_cast hq)
  · exact integerMonomialTorBettiNumber_negative o _ p q (lt_of_not_ge hq0)

/-- Corollary 5.1, with its original integer degree quantifier. -/
theorem corollary51_integer (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    integerMonomialTorBettiNumber (K := K) o
      (exponentPowerFamily (finiteRowFamily n E) m) p ((m*d : ℕ)+q) =
      ∑ s : StrictSupport E, (m-1).choose (s.val.card-1) *
        integerOrdinaryQuotientBettiNumber (K := K) (strictSupportCoefficientFamily s) q p := by
  by_cases hq : 0 ≤ q
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [← Nat.cast_add, integerMonomialTorBettiNumber_nat]
    simp only [integerOrdinaryQuotientBettiNumber_nat]
    exact corollary51 hE m hm a p
  · have hneg : q < 0 := lt_of_not_ge hq
    rw [integerPowerBetti_eq_zero_below o hE m hm p _ (by omega)]
    simp only [integerOrdinaryQuotientBettiNumber_negative _ q hneg p,
      mul_zero, Finset.sum_const_zero]

def integerStrictSupportBettiCoefficient (q : ℤ) (p : ℕ) (s : StrictSupport E) : ℕ :=
  integerOrdinaryQuotientBettiNumber (K := K) (strictSupportCoefficientFamily s) q p

def integerNormalizedBettiSequence (q : ℤ) (p t : ℕ) : ℕ :=
  integerMonomialTorBettiNumber (K := K) o
    (exponentPowerFamily (finiteRowFamily n E) (t+1)) p (((t+1)*d : ℕ)+q)

theorem integerNormalizedBettiSequence_eq (hE : finiteLatticeClosed n E)
    (q : ℤ) (p t : ℕ) : integerNormalizedBettiSequence (K := K) o (E := E) q p t =
      PositiveBinomialPolynomial.sequence
        (integerStrictSupportBettiCoefficient (K := K) (E := E) q p)
        (fun s => s.val.card-1) t := by
  rw [integerNormalizedBettiSequence, corollary51_integer o hE (t+1) (by omega)]
  simp only [Nat.add_sub_cancel, PositiveBinomialPolynomial.sequence,
    integerStrictSupportBettiCoefficient, mul_comm]

def integerNormalizedBettiPolynomial (q : ℤ) (p : ℕ) : Polynomial ℚ :=
  (PositiveBinomialPolynomial.polynomial
    (integerStrictSupportBettiCoefficient (K := K) (E := E) q p)
    (fun s => s.val.card-1)).comp (Polynomial.X-Polynomial.C 1)

/-- Every integer normalized entry is the indicated polynomial at all
positive powers, with nonnegative binomial coefficients. -/
theorem corollary52_integer_polynomial (hE : finiteLatticeClosed n E)
    (q : ℤ) (p m : ℕ) (hm : 0 < m) :
    (integerNormalizedBettiPolynomial (K := K) (E := E) q p).eval (m : ℚ) =
      (integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) m) p ((m*d : ℕ)+q) : ℚ) := by
  rw [integerNormalizedBettiPolynomial,
    PositiveBinomialPolynomial.shifted_polynomial_eval _ _ m hm,
    ← integerNormalizedBettiSequence_eq o hE q p (m-1), integerNormalizedBettiSequence,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]

/-- All orders of forward difference use integer subtraction and are
nonnegative, for every integer normalized degree q. -/
theorem corollary52_integer_forward_differences (hE : finiteLatticeClosed n E)
    (q : ℤ) (p j t : ℕ) :
    0 ≤ ((fwdDiff (1 : ℕ))^[j]
      (fun a => (integerNormalizedBettiSequence (K := K) o (E := E) q p a : ℤ))) t := by
  simp_rw [integerNormalizedBettiSequence_eq o hE q p]
  exact PositiveBinomialPolynomial.sequence_forward_differences_nonnegative _ _ j t

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary51_integer
#print axioms FourPapers.Sublattice.corollary52_integer_polynomial
#print axioms FourPapers.Sublattice.corollary52_integer_forward_differences

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesHomogeneous -/
section

/-! # The actual auxiliary, ordinary, and exterior gradings

Ordinary homogeneity is proved from homogeneity of the given ideal; it is
not inferred from a monomial-order bound. The exterior degree is recorded
in the integers so that its differential shift is injective, including at
degree zero where the differential vanishes.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg FourPapers.Sublattice MvPolynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m ((powerProduct J s)) = (powerProduct I s))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

def reesKoszulOrdinaryDegree (a : IdealReesKoszulIndex m J) : ℕ :=
  a.1.2.val.degree + a.2.card

def reesKoszulStrand (a : IdealReesKoszulIndex m J) : (C →₀ ℕ) × ℕ :=
  (a.1.1, reesKoszulOrdinaryDegree m J a)

def reesKoszulFullDegree (a : IdealReesKoszulIndex m J) : ((C →₀ ℕ) × ℕ) × ℤ :=
  (reesKoszulStrand m J a, a.2.card)

def koszulDegreeShift (a : ((C →₀ ℕ) × ℕ) × ℤ) : ((C →₀ ℕ) × ℕ) × ℤ := (a.1, a.2-1)

theorem koszulDegreeShift_injective : Function.Injective (koszulDegreeShift (C := C)) := by
  rintro ⟨a,p⟩ ⟨b,q⟩ h
  have hab : a=b := congrArg Prod.fst h
  have he : p-1=q-1 := congrArg Prod.snd h
  have hpq : p=q := by omega
  exact Prod.ext hab hpq

theorem groebnerReesBasis_product_auxiliary
    (a b c : GroebnerReesIndex J m)
    (hc : (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c ≠ 0) :
    c.1 = a.1+b.1 := by
  rw [groebnerReesBasis_repr, groebnerReesBasis_apply, groebnerReesBasis_apply] at hc
  change ((AddMonoidAlgebra.single a.1
    (idealLift m (powerProduct J a.1) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m (powerProduct J b.1) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val ≠ 0 at hc
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at hc
  by_contra h
  simp only [if_neg (Ne.symm h), MvPolynomial.coeff_zero] at hc
  exact hc rfl

theorem groebnerReesKoszul_d_auxiliary_exterior
    (a z : IdealReesKoszulIndex m J)
    (hz : (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a)) z ≠ 0) :
    z.1.1 = a.1.1 ∧ z.2.card + 1 = a.2.card := by
  rw [groebnerReesKoszul_d_basis, map_sum, Finsupp.finsetSum_apply] at hz
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  rw [Simplicial.contraction_basis] at hv
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, map_zsmul_unit,
      Finsupp.smul_apply, groebnerReesKoszulBasis, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at hv
    have hF : a.2.erase v = z.2 := by
      by_contra h
      simp [h] at hv
    rw [if_pos hF, one_smul, idealReesBaseVariable_basis m J G hG hu v] at hv
    have hc : (groebnerReesBasis J m G hG hu).repr
        (groebnerReesBasis J m G hG hu (idealReesZeroIndex m J (Finsupp.single v 1)) *
          groebnerReesBasis J m G hG hu a.1) z.1 ≠ 0 := by
      intro h
      simp only [h, smul_zero] at hv
      exact hv rfl
    refine ⟨?_, ?_⟩
    · simpa only [idealReesZeroIndex, zero_add] using
        groebnerReesBasis_product_auxiliary m J G hG hu _ _ _ hc
    · rw [← hF, Finset.card_erase_of_mem hvF]
      have hp := Finset.card_pos.mpr ⟨v,hvF⟩
      omega
  · rw [if_neg hvF, TensorProduct.tmul_zero, map_zero, Finsupp.zero_apply] at hv
    exact (hv rfl).elim

theorem initialReesKoszul_d_auxiliary_exterior
    (a z : IdealReesKoszulIndex m J)
    (hz : (initialReesKoszulBasis m J I hinit G hG hu).repr
      ((idealReesKoszulDGA I).d (initialReesKoszulBasis m J I hinit G hG hu a)) z ≠ 0) :
    z.1.1 = a.1.1 ∧ z.2.card + 1 = a.2.card := by
  have hf := initialReesKoszul_d_fine m J I hinit G hG hu a z hz
  have hw : reesKoszulWeight m J a ≤ reesKoszulWeight m J z := by
    simp only [reesKoszulWeight, hf, le_refl]
  apply groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z
  rwa [OrderedRees.differential_leading m J I hinit G hG hu a z hw]

variable (hJ : ∀ s, ((powerProduct J s)).IsHomogeneous
  (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 300000 in
set_option diagnostics true in
include hJ in
theorem groebnerReesBasis_product_ordinary
    (a b c : GroebnerReesIndex J m)
    (hc : (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c ≠ 0) :
    c.2.val.degree = a.2.val.degree + b.2.val.degree := by
  have hs := groebnerReesBasis_product_auxiliary m J G hG hu a b c hc
  rw [groebnerReesBasis_repr, groebnerReesBasis_apply, groebnerReesBasis_apply] at hc
  change ((AddMonoidAlgebra.single a.1
    (idealLift m (powerProduct J a.1) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m (powerProduct J b.1) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val ≠ 0 at hc
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, if_pos hs.symm] at hc
  have he : Finsupp.weight (fun _ : V => (1 : ℕ)) c.2.val =
      Finsupp.weight (fun _ : V => (1 : ℕ)) a.2.val +
        Finsupp.weight (fun _ : V => (1 : ℕ)) b.2.val :=
    idealLift_product_weight_withNatModule m (powerProduct J a.1) (powerProduct J b.1)
      (G a.1) (G b.1) (hG a.1) (hG b.1) (hu a.1) (hu b.1)
      (fun _ : V => (1 : ℕ)) (hJ a.1) (hJ b.1) a.2 b.2 c.2.val hc
  simpa only [← Finsupp.degree_eq_weight_one] using he

include hJ in
theorem groebnerReesKoszul_d_ordinary
    (a z : IdealReesKoszulIndex m J)
    (hz : (groebnerReesKoszulBasis m J G hG hu).repr
      ((idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a)) z ≠ 0) :
    reesKoszulOrdinaryDegree m J z = reesKoszulOrdinaryDegree m J a := by
  have hcard := (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).2
  rw [groebnerReesKoszul_d_basis, map_sum, Finsupp.finsetSum_apply] at hz
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  rw [Simplicial.contraction_basis] at hv
  by_cases hvF : v ∈ a.2
  · rw [if_pos hvF, TensorProduct.tmul_smul, map_zsmul_unit,
      Finsupp.smul_apply, groebnerReesKoszulBasis, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at hv
    have hF : a.2.erase v = z.2 := by
      by_contra h
      simp [h] at hv
    rw [if_pos hF, one_smul, idealReesBaseVariable_basis m J G hG hu v] at hv
    have hc : (groebnerReesBasis J m G hG hu).repr
        (groebnerReesBasis J m G hG hu (idealReesZeroIndex m J (Finsupp.single v 1)) *
          groebnerReesBasis J m G hG hu a.1) z.1 ≠ 0 := by
      intro h
      simp only [h, smul_zero] at hv
      exact hv rfl
    have hp := groebnerReesBasis_product_ordinary m J G hG hu hJ _ _ _ hc
    simp only [idealReesZeroIndex, Finsupp.degree_single] at hp
    dsimp only [reesKoszulOrdinaryDegree]
    omega
  · rw [if_neg hvF, TensorProduct.tmul_zero, map_zero, Finsupp.zero_apply] at hv
    exact (hv rfl).elim

include hJ in
theorem groebnerReesKoszul_d_fullDegree (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu) (reesKoszulFullDegree m J)
        (koszulDegreeShift (reesKoszulFullDegree m J a)) := by
  rw [Grading.mem_piece]
  intro z hz
  have hs := groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz
  have hq := groebnerReesKoszul_d_ordinary m J G hG hu hJ a z hz
  apply Prod.ext
  · exact Prod.ext hs.1 hq
  · dsimp only [reesKoszulFullDegree, koszulDegreeShift]
    omega

include hJ in
theorem groebnerReesKoszul_d_strand (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu) (reesKoszulStrand m J)
        (reesKoszulStrand m J a) := by
  rw [Grading.mem_piece]
  intro z hz
  exact Prod.ext (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).1
    (groebnerReesKoszul_d_ordinary m J G hG hu hJ a z hz)

/-- Each fixed ordinary and auxiliary component has a genuinely finite
basis, uniformly over arbitrary finite variable sets and all ideal powers. -/
instance reesKoszulStrand_finite (s : C →₀ ℕ) (q : ℕ) :
    Finite {a : IdealReesKoszulIndex m J // reesKoszulStrand m J a = (s,q)} := by
  let B := {a : V →₀ ℕ // a.degree ≤ q}
  letI : Finite B := (Finsupp.finite_of_degree_le q).to_subtype
  let f : {a : IdealReesKoszulIndex m J // reesKoszulStrand m J a = (s,q)} → B × Finset V :=
    fun a => (⟨a.val.1.2.val, by
      have hq := congrArg Prod.snd a.property
      change a.val.1.2.val.degree + a.val.2.card = q at hq
      omega⟩, a.val.2)
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · have ha := congrArg Prod.fst a.property
    have hb := congrArg Prod.fst b.property
    have he : a.val.1.2.val = b.val.1.2.val := congrArg (fun z : B × Finset V => z.1.val) h
    have hs : a.val.1.1 = b.val.1.1 := ha.trans hb.symm
    cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        rcases a with ⟨⟨r,a⟩,F⟩
        rcases b with ⟨⟨t,b⟩,H⟩
        dsimp only at hs he ⊢
        subst t
        exact congrArg (Sigma.mk r) (Subtype.ext he)
  · exact congrArg (fun z : B × Finset V => z.2) h

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesCoordinateLifting -/
section

/-! # Actual ideal-power coordinate lifts and Rees cycle lifts

The coordinate modules contain coefficients in the literal ideals `(powerProduct J s)`.
Their inclusions are the ordinary tensor Koszul inclusions followed by the
actual auxiliary-degree inclusion into the Rees algebra.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg CommAlg.Koszul FourPapers.Sublattice MvPolynomial FilteredHomology
open scoped TensorProduct

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : C → Ideal (MvPolynomial V K))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev PowerIdealIndex (s : C →₀ ℕ) (p : ℕ) := Σ F : Set.powersetCard V p, NonstandardIndex m ((powerProduct J s))
abbrev PowerIdealCoordinates (s : C →₀ ℕ) (p : ℕ) := Set.powersetCard V p →₀ idealPowerPiece J s

def powerIdealCoefficientBasis (s : C →₀ ℕ) (p : ℕ) :
    Module.Basis (PowerIdealIndex m J s p) K (PowerIdealCoordinates J s p) :=
  Finsupp.basis (fun _ => groebnerPowerBasis J m G hG hu s)

def powerIdealReesIndex (s : C →₀ ℕ) (p : ℕ) (a : PowerIdealIndex m J s p) : IdealReesKoszulIndex m J :=
  (⟨s,a.2⟩,a.1.val)

theorem powerIdealReesIndex_injective (s : C →₀ ℕ) (p : ℕ) :
    Function.Injective (powerIdealReesIndex m J s p) := by
  rintro ⟨F,a⟩ ⟨H,b⟩ h
  have hF : F=H := Subtype.ext (congrArg Prod.snd h)
  subst H
  have hab : a.val=b.val := congrArg (fun t : IdealReesKoszulIndex m J => t.1.2.val) h
  exact congrArg (Sigma.mk F) (Subtype.ext hab)

def powerCoordinateInclusion (s : C →₀ ℕ) (p : ℕ) :
    PowerIdealCoordinates J s p →ₗ[K] IdealReesKoszul J :=
  (powerKoszulInclusion J s).comp (TensorExteriorKoszul.lift (K:=K) (M:=idealPowerPiece J s) p)

theorem powerCoordinateInclusion_basis (s : C →₀ ℕ) (p : ℕ) (a : PowerIdealIndex m J s p) :
    powerCoordinateInclusion J s p (powerIdealCoefficientBasis m J G hG hu s p a) =
      groebnerReesKoszulBasis m J G hG hu (powerIdealReesIndex m J s p a) := by
  rw [powerCoordinateInclusion,LinearMap.comp_apply,powerIdealCoefficientBasis,
    Finsupp.coe_basis,TensorExteriorKoszul.lift_single]
  simpa only [idealPowerKoszulBasis, Module.Basis.tensorProduct_apply', powerIdealReesIndex] using
    powerKoszulInclusion_basis m J G hG hu s (a.2,a.1.val)

def powerPreviousDifferential (s : C →₀ ℕ) : ∀ p : ℕ,
    PowerIdealCoordinates J s p →ₗ[K] PowerIdealCoordinates J s p.pred
  | 0 => 0
  | p+1 => (CommAlg.Koszul.coordinateDifferential (X : V → MvPolynomial V K)
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s)) p).restrictScalars K

theorem powerCoordinateInclusion_d (s : C →₀ ℕ) (p : ℕ) (x : PowerIdealCoordinates J s p) :
    (idealReesKoszulDGA J).d (powerCoordinateInclusion J s p x) =
      powerCoordinateInclusion J s p.pred (powerPreviousDifferential J s p x) := by
  rw [powerCoordinateInclusion,LinearMap.comp_apply,powerKoszulInclusion_d]
  cases p with
  | zero =>
    have he : (idealPowerKoszulDifferential J s).comp
        (TensorExteriorKoszul.lift (K:=K) (M:=idealPowerPiece J s) 0) = 0 := by
      apply Finsupp.lhom_ext
      intro F a
      simp only [LinearMap.comp_apply,TensorExteriorKoszul.lift_single,
        LinearMap.zero_apply,idealPowerKoszulDifferential,
        TensorExteriorKoszul.differential_tmul]
      have hF : F.val=∅ := Finset.card_eq_zero.mp F.property
      simp only [hF,Simplicial.contraction_basis,Finset.notMem_empty,if_false,
        TensorProduct.tmul_zero,Finset.sum_const_zero]
    have hz := LinearMap.congr_fun he x
    change idealPowerKoszulDifferential J s (TensorExteriorKoszul.lift 0 x)=0 at hz
    simp only [hz,map_zero,powerPreviousDifferential,LinearMap.zero_apply]
  | succ p =>
    have he := TensorExteriorKoszul.differential_lift (K:=K) (R:=MvPolynomial V K)
      (M:=idealPowerPiece J s) (X : V → MvPolynomial V K) p x
    exact congrArg (powerKoszulInclusion J s) he

/-- The original monomial-order degree is pulled back by the literal
mixed-power coordinate inclusion. -/
theorem powerIdealReesIndex_order_weight (s : C →₀ ℕ) (p : ℕ)
    (a : PowerIdealIndex m J s p) :
    reesKoszulWeight m J (powerIdealReesIndex m J s p a) =
      m.toSyn (a.2.val + faceExponent a.1.val) := rfl

theorem powerIdealReesIndex_range (s : C →₀ ℕ) (p : ℕ) :
    Set.range (powerIdealReesIndex m J s p) =
      {a : IdealReesKoszulIndex m J | a.1.1=s ∧ (a.2.card : ℤ)=p} := by
  ext a
  constructor
  · rintro ⟨⟨F,b⟩,rfl⟩
    exact ⟨rfl,by exact_mod_cast F.property⟩
  · rintro ⟨hs,hp⟩
    rcases a with ⟨⟨t,a⟩,F⟩
    dsimp only at hs hp
    subst t
    exact ⟨⟨⟨F,by exact_mod_cast hp⟩,a⟩,rfl⟩

theorem basisSpan_inf_piece {A : Type*} (S : Set (IdealReesKoszulIndex m J))
    (deg : IdealReesKoszulIndex m J → A) (a : A) :
    Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) '' S) ⊓
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu) deg a =
    Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) '' {i | i∈S ∧ deg i=a}) := by
  ext x
  simp only [Submodule.mem_inf,Grading.Piece,Module.Basis.mem_span_image,
    Set.subset_def,Finset.mem_coe,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hS,ha⟩ i hi
    exact ⟨hS i hi,ha i hi⟩
  · intro h
    exact ⟨fun i hi => (h i hi).1,fun i hi => (h i hi).2⟩

theorem groebnerReesKoszul_d_exterior (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu)
        (fun z => (z.2.card : ℤ)) ((a.2.card : ℤ)-1) := by
  rw [Grading.mem_piece]
  intro z hz
  have he := (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).2
  omega

/-- Full first-power coordinate lifting, in every exterior degree, gives
the exact relative lifting hypothesis consumed by multiplicative propagation. -/
theorem powerIdealReesIndex_range_degree (s : C →₀ ℕ) (p : ℕ) :
    Set.range (powerIdealReesIndex m J s p) =
      {a : IdealReesKoszulIndex m J | (a.1.1,(a.2.card : ℤ))=(s,(p : ℤ))} := by
  rw [powerIdealReesIndex_range]
  ext a
  change (a.1.1 = s ∧ (a.2.card : ℤ) = (p : ℤ)) ↔
    (a.1.1,(a.2.card : ℤ)) = (s,(p : ℤ))
  exact ⟨fun h => Prod.ext h.1 h.2,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem groebnerReesKoszul_d_auxiliary_exterior_piece (a : IdealReesKoszulIndex m J) :
    (idealReesKoszulDGA J).d (groebnerReesKoszulBasis m J G hG hu a) ∈
      Grading.Piece (groebnerReesKoszulBasis m J G hG hu)
        (fun z => (z.1.1,(z.2.card : ℤ))) (a.1.1,(a.2.card : ℤ)-1) := by
  rw [Grading.mem_piece]
  intro z hz
  have he := groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz
  exact Prod.ext he.1 (by omega)

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesOrderCoordinateLifting -/
section

/-! # Coordinate lifting in the original term order -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg CommAlg.Koszul FourPapers.Sublattice MvPolynomial FilteredHomology

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : C → Ideal (MvPolynomial V K))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s,m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g,g∈G s → g≠0 → IsUnit (m.leadingCoeff g))

def PowerOrderedCoordinateLifts (s : C →₀ ℕ) (p : ℕ) : Prop :=
  BasisCycleLifting.LinearLifts (K := K)
    (X := PowerIdealCoordinates J s p) (Y := PowerIdealCoordinates J s p.pred)
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred) (Γ := m.syn)
    (powerIdealCoefficientBasis m J G hG hu s p)
    (powerIdealCoefficientBasis m J G hG hu s p.pred)
    (fun a : PowerIdealIndex m J s p => m.toSyn (a.2.val + faceExponent a.1.val))
    (fun b : PowerIdealIndex m J s p.pred => m.toSyn (b.2.val + faceExponent b.1.val))
    (powerPreviousDifferential J s p)

section
attribute [local irreducible] powerIdealCoefficientBasis groebnerReesKoszulBasis
  idealReesKoszulDGA

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
theorem power_ordered_coordinate_lifts_iff (s : C →₀ ℕ) (p : ℕ) :
    PowerOrderedCoordinateLifts m J G hG hu s p ↔
      BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
        (reesKoszulWeight m J) (idealReesKoszulDGA J).d
        (Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) ''
          Set.range (powerIdealReesIndex m J s p))) := by
  have he := BasisEmbedding.ordered_coordinate_lifts_iff (K := K)
    (X := PowerIdealCoordinates J s p) (Y := PowerIdealCoordinates J s p.pred)
    (M := IdealReesKoszul J)
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred)
    (T := IdealReesKoszulIndex m J) (Γ := m.syn)
    (powerIdealCoefficientBasis m J G hG hu s p)
    (powerIdealCoefficientBasis m J G hG hu s p.pred)
    (groebnerReesKoszulBasis m J G hG hu)
    (powerIdealReesIndex m J s p) (powerIdealReesIndex_injective m J s p)
    (powerIdealReesIndex m J s p.pred) (powerIdealReesIndex_injective m J s p.pred)
    (powerCoordinateInclusion J s p) (powerCoordinateInclusion J s p.pred)
    (powerCoordinateInclusion_basis m J G hG hu s p)
    (powerCoordinateInclusion_basis m J G hG hu s p.pred)
    (reesKoszulWeight m J) (powerPreviousDifferential J s p)
    (idealReesKoszulDGA J).d (powerCoordinateInclusion_d J s p)

  simpa only [PowerOrderedCoordinateLifts, Function.comp_def,
    powerIdealReesIndex_order_weight] using he

end

theorem auxiliary_ordered_basis_lifts (s : C →₀ ℕ)
    (hlift : ∀ p,PowerOrderedCoordinateLifts m J G hG hu s p) :
    BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
      (reesKoszulWeight m J) (idealReesKoszulDGA J).d
      (Auxiliary.auxiliaryPiece m J G hG hu s) := by
  apply BasisCycleLifting.liftsOn_of_homogeneous_lifts
    (K := K) (M := IdealReesKoszul J) (I := IdealReesKoszulIndex m J)
    (A := ℤ) (Γ := m.syn)
    (groebnerReesKoszulBasis m J G hG hu) (reesKoszulWeight m J)
    (idealReesKoszulDGA J).d {a | a.1.1=s} (fun a => (a.2.card : ℤ))
    (fun p : ℤ => p-1) (by
      intro r t h
      change r - 1 = t - 1 at h
      omega)
    (groebnerReesKoszul_d_exterior m J G hG hu)
  intro p
  by_cases hp : 0≤p
  · obtain ⟨r,rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [basisSpan_inf_piece]
    simpa only [powerIdealReesIndex_range, Set.mem_setOf_eq] using
      (power_ordered_coordinate_lifts_iff m J G hG hu s r).mp (hlift r)
  · intro n x hx hxF hdx
    have hx0 : x=0 := by
      apply (groebnerReesKoszulBasis m J G hG hu).repr.injective
      ext a
      rw [map_zero,Finsupp.zero_apply]
      by_contra ha
      have he := (Grading.mem_piece _ _ p x).mp hx.2 a ha
      exact hp (he ▸ Int.natCast_nonneg a.2.card)
    refine ⟨0,Submodule.zero_mem _,Submodule.zero_mem _,map_zero _,?_⟩
    rw [hx0,sub_self]
    exact Submodule.zero_mem _

/-- Reassemble lifts in any set of actual color components.  The selected
submodule is the span of precisely those components, and every vector has
only finitely many nonzero color coordinates. -/
theorem selected_ordered_basis_lifts (U : Set (C →₀ ℕ))
    (hlift : ∀ s ∈ U, ∀ p, PowerOrderedCoordinateLifts m J G hG hu s p) :
    BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
      (reesKoszulWeight m J) (idealReesKoszulDGA J).d
      (Auxiliary.selectedPiece m J G hG hu U) := by
  apply BasisCycleLifting.liftsOn_of_homogeneous_lifts
    (K := K) (M := IdealReesKoszul J) (I := IdealReesKoszulIndex m J)
    (A := C →₀ ℕ) (Γ := m.syn)
    (groebnerReesKoszulBasis m J G hG hu) (reesKoszulWeight m J)
    (idealReesKoszulDGA J).d {a | a.1.1 ∈ U} (fun a => a.1.1)
    id Function.injective_id
  · intro a
    rw [Grading.mem_piece]
    intro z hz
    exact (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a z hz).1
  · intro s
    rw [basisSpan_inf_piece]
    simp only [Set.mem_setOf_eq]
    by_cases hs : s ∈ U
    · have he : {a : IdealReesKoszulIndex m J | a.1.1 ∈ U ∧ a.1.1 = s} =
          {a | a.1.1 = s} := by
        ext a
        constructor
        · exact And.right
        · intro ha
          exact ⟨ha ▸ hs, ha⟩
      rw [he]
      exact auxiliary_ordered_basis_lifts m J G hG hu s (hlift s hs)
    · have he : {a : IdealReesKoszulIndex m J | a.1.1 ∈ U ∧ a.1.1 = s} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hs (ha.2 ▸ ha.1)
      rw [he, Set.image_empty, Submodule.span_empty]
      intro n x hx hxF hdx
      have hx0 : x = 0 := (Submodule.mem_bot K).mp hx
      subst x
      exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, map_zero _,
        by simpa only [sub_self] using (Submodule.zero_mem
          (BasisCycleLifting.lower (groebnerReesKoszulBasis m J G hG hu)
            (reesKoszulWeight m J) n))⟩

variable (I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s,initialIdealForBasis m ((powerProduct J s))=(powerProduct I s))

local notation "F" => idealReesKoszulFiltration m J I hinit G hG hu
local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "w" => reesKoszulWeight m J
local notation "hOne" => (fun a ha =>
  le_of_eq (groebnerReesKoszul_one_weight m J G hG hu a ha))
local notation "hProduct" => OrderedBasis.product_nonincreasing b
  (initialReesKoszulBasis m J I hinit G hG hu) w
  (initialReesKoszul_product_homogeneous m J I hinit G hG hu)
  (groebnerReesKoszul_product_leading m J I hinit G hG hu)

theorem ordered_relative_lifts_of_power_coordinate_lifts (s : C →₀ ℕ)
    (hlift : ∀ p,PowerOrderedCoordinateLifts m J G hG hu s p) :
    (F).RelativeLiftsCycles (idealReesKoszulDGA J) (Auxiliary.auxiliaryPiece m J G hG hu s) := by
  apply (OrderedBasis.relativeLiftsCycles_iff_basisLifts b w hOne hProduct
    (idealReesKoszulDGA J) (Auxiliary.auxiliaryPiece m J G hG hu s)).mpr
  exact auxiliary_ordered_basis_lifts m J G hG hu s hlift

set_option backward.isDefEq.respectTransparency true in
theorem ordered_power_coordinate_lifts_of_all_lifts
    (hlift : (F).LiftsCycles (idealReesKoszulDGA J)) (s : C →₀ ℕ) (p : ℕ) :
    PowerOrderedCoordinateLifts m J G hG hu s p := by
  apply (power_ordered_coordinate_lifts_iff m J G hG hu s p).mpr
  rw [powerIdealReesIndex_range_degree]
  let deg := fun a : IdealReesKoszulIndex m J => (a.1.1,(a.2.card : ℤ))
  let shift := fun a : (C →₀ ℕ) × ℤ => (a.1,a.2-1)
  have hshift : Function.Injective shift := by
    rintro ⟨a,r⟩ ⟨a',t⟩ h
    have hq : r-1=t-1 := congrArg Prod.snd h
    have ha : a=a' := congrArg Prod.fst h
    exact Prod.ext ha (by omega)
  have hD : ∀ a,(idealReesKoszulDGA J).d (b a)∈Grading.Piece b deg (shift (deg a)) :=
    groebnerReesKoszul_d_auxiliary_exterior_piece m J G hG hu
  intro n x hx hxF hdx
  have hdx' : (idealReesKoszulDGA J).d x∈(F).lower n := by
    rw [idealReesKoszulFiltration, OrderedBasis.comparisonFiltration,
      OrderedBasis.filtration_lower]
    exact hdx
  obtain ⟨y,hyF,hdy,herr⟩ := hlift n x hxF hdx'
  have herr' : x-y∈BasisCycleLifting.lower b w n := by
    rw [idealReesKoszulFiltration, OrderedBasis.comparisonFiltration,
      OrderedBasis.filtration_lower] at herr
    exact herr
  have hxPiece : x ∈ Grading.Piece b deg (s,(p:ℤ)) := hx
  let z := Grading.projection b deg (s,(p:ℤ)) y
  refine ⟨z,Grading.projection_mem b deg (s,(p:ℤ)) y,
    projection_preserves_basisSpan b deg (s,(p:ℤ)) {a | w a≤n} y hyF,?_,?_⟩
  · have hcomm :
        (idealReesKoszulDGA J).d.comp (Grading.projection b deg (s,(p:ℤ))) =
          (Grading.projection b deg (shift (s,(p:ℤ)))).comp (idealReesKoszulDGA J).d := by
      apply (groebnerReesKoszulBasis m J G hG hu).ext
      intro a
      simp only [LinearMap.comp_apply, Grading.projection_basis]
      by_cases ha : deg a = (s,(p:ℤ))
      · rw [if_pos ha]
        exact (Grading.projection_eq_self (ha ▸ hD a)).symm
      · rw [if_neg ha, map_zero]
        exact (Grading.projection_eq_zero
          (show shift (s,(p:ℤ)) ≠ shift (deg a) from
            fun h => ha (hshift h).symm) (hD a)).symm
    have he := LinearMap.congr_fun hcomm y
    simpa only [LinearMap.comp_apply,hdy,map_zero] using he
  · have he := projection_preserves_basisSpan b deg (s,(p:ℤ)) {a | w a<n} (x-y) herr'
    simpa only [z, BasisCycleLifting.lower, map_sub,
      Grading.projection_eq_self hxPiece] using he

/-- Multiplicative propagation from the chosen color components, followed
by projection back to the literal mixed-ideal Koszul coordinates. -/
theorem all_mixed_ordered_coordinate_lifts (U : Set (C →₀ ℕ))
    (hgen : Algebra.adjoin K
      (FourPapers.IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses
        (idealReesKoszulDGA I) (Auxiliary.initialSelectedPiece m J I hinit G hG hu U)) = ⊤)
    (hlift : ∀ s ∈ U, ∀ p, PowerOrderedCoordinateLifts m J G hG hu s p)
    (s : C →₀ ℕ) (p : ℕ) : PowerOrderedCoordinateLifts m J G hG hu s p := by
  have hrel : (F).RelativeLiftsCycles (idealReesKoszulDGA J)
      (Auxiliary.selectedPiece m J G hG hu U) :=
    (OrderedBasis.relativeLiftsCycles_iff_basisLifts b w hOne hProduct
      (idealReesKoszulDGA J) (Auxiliary.selectedPiece m J G hG hu U)).mpr
        (selected_ordered_basis_lifts m J G hG hu U hlift)
  exact ordered_power_coordinate_lifts_of_all_lifts m J G hG hu I hinit
    (OrderedRees.all_cycle_lifts m J I hinit G hG hu U hgen hrel) s p

theorem mixed_homology_generated_of_selected_lifts (U : Set (C →₀ ℕ))
    (hgen : Algebra.adjoin K
      (FourPapers.IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses
        (idealReesKoszulDGA I) (Auxiliary.initialSelectedPiece m J I hinit G hG hu U)) = ⊤)
    (hlift : ∀ s ∈ U, ∀ p, PowerOrderedCoordinateLifts m J G hG hu s p) :
    Algebra.adjoin K
      (FourPapers.IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses
        (idealReesKoszulDGA J) (Auxiliary.selectedPiece m J G hG hu U)) = ⊤ := by
  apply OrderedRees.homology_generated_in_degree_one m J I hinit G hG hu U hgen
  apply (OrderedBasis.relativeLiftsCycles_iff_basisLifts b w hOne hProduct
    (idealReesKoszulDGA J) (Auxiliary.selectedPiece m J G hG hu U)).mpr
  exact selected_ordered_basis_lifts m J G hG hu U hlift

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.IdealPowerCoordinateTransport -/
section

/-!
# Native mixed-ideal coordinates and scalar-restricted Rees coefficients

For each color exponent, the two presentations have identical underlying polynomials.  Their scalar
module dictionaries need not be definitionally equal.  The explicit
identity maps below retain the coordinates, differential, and basis, and
therefore retain the complete original-order cycle-lifting statement.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.MixedTransfer
open Classical CommAlg CommAlg.Koszul FourPapers.Sublattice MvPolynomial

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : C → Ideal (MvPolynomial V K))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (powerProduct J s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

def nativePowerCoefficientBasis (s : C →₀ ℕ) (p : ℕ) :
    Module.Basis (PowerIdealIndex m J s p) K (Set.powersetCard V p →₀ ↥(powerProduct J s)) :=
  Finsupp.basis (fun _ => groebnerIdealBasis m (powerProduct J s) (G s) (hG s) (hu s))

def powerIdealCoordinateEquiv (s : C →₀ ℕ) (p : ℕ) :
    (Set.powersetCard V p →₀ ↥(powerProduct J s)) ≃ₗ[K] PowerIdealCoordinates J s p :=
  Finsupp.mapRange.linearEquiv (idealScalarRestrictionEquiv (powerProduct J s))

@[simp] theorem powerIdealCoordinateEquiv_apply (s : C →₀ ℕ) (p : ℕ)
    (x : Set.powersetCard V p →₀ ↥(powerProduct J s)) (F : Set.powersetCard V p) :
    (powerIdealCoordinateEquiv J s p x F).val = (x F).val := rfl

/-- The same coefficient identity as a map over the polynomial ring. -/
def idealPowerRestrictionLinear (s : C →₀ ℕ) : ↥(powerProduct J s) →ₗ[MvPolynomial V K] idealPowerPiece J s where
  toFun x := ⟨x.val, x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem powerIdealCoordinateEquiv_basis (s : C →₀ ℕ) (p : ℕ) (a : PowerIdealIndex m J s p) :
    powerIdealCoordinateEquiv J s p (nativePowerCoefficientBasis m J G hG hu s p a) =
      powerIdealCoefficientBasis m J G hG hu s p a := by
  rw [nativePowerCoefficientBasis, powerIdealCoefficientBasis, Finsupp.coe_basis,
    Finsupp.coe_basis]
  change Finsupp.mapRange (idealScalarRestrictionEquiv (powerProduct J s))
      (idealScalarRestrictionEquiv (powerProduct J s)).map_zero
      (Finsupp.single a.1 (groebnerIdealBasis m (powerProduct J s) (G s) (hG s) (hu s) a.2)) = _
  rw [Finsupp.mapRange_single]
  rfl

theorem powerIdealCoordinateEquiv_differential (s : C →₀ ℕ) (p : ℕ)
    (x : Set.powersetCard V p →₀ ↥(powerProduct J s)) :
    powerPreviousDifferential J s p (powerIdealCoordinateEquiv J s p x) =
      powerIdealCoordinateEquiv J s p.pred (actualIdealPreviousDifferential (powerProduct J s) p x) := by
  cases p with
  | zero => exact (powerIdealCoordinateEquiv J s 0).map_zero.symm
  | succ p =>
    exact coordinateDifferential_mapRange (X : V → MvPolynomial V K)
      (ModuleCat.of (MvPolynomial V K) ↥(powerProduct J s))
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))
      (idealPowerRestrictionLinear J s) p x

def NativePowerOrderedLifts (s : C →₀ ℕ) (p : ℕ) : Prop :=
  BasisCycleLifting.LinearLifts (K := K)
    (X := Set.powersetCard V p →₀ ↥(powerProduct J s))
    (Y := Set.powersetCard V p.pred →₀ ↥(powerProduct J s))
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred) (Γ := m.syn)
    (nativePowerCoefficientBasis m J G hG hu s p)
    (nativePowerCoefficientBasis m J G hG hu s p.pred)
    (fun a : PowerIdealIndex m J s p => m.toSyn (a.2.val + faceExponent a.1.val))
    (fun a : PowerIdealIndex m J s p.pred => m.toSyn (a.2.val + faceExponent a.1.val))
    (actualIdealPreviousDifferential (powerProduct J s) p)

section
attribute [local irreducible] nativePowerCoefficientBasis powerIdealCoefficientBasis
  powerIdealCoordinateEquiv actualIdealPreviousDifferential powerPreviousDifferential

set_option diagnostics true in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
/-- Exact equivalence, including every filtration index and every cycle. -/
theorem nativePowerOrderedLifts_iff (s : C →₀ ℕ) (p : ℕ) :
    NativePowerOrderedLifts m J G hG hu s p ↔ PowerOrderedCoordinateLifts m J G hG hu s p := by
  unfold NativePowerOrderedLifts PowerOrderedCoordinateLifts
  apply BasisCycleLifting.linearLifts_iff_of_equiv
    (e := powerIdealCoordinateEquiv J s p)
    (f := powerIdealCoordinateEquiv J s p.pred)
  · exact powerIdealCoordinateEquiv_basis m J G hG hu s p
  · exact powerIdealCoordinateEquiv_basis m J G hG hu s p.pred
  · exact powerIdealCoordinateEquiv_differential J s p

end

end FourPapers.MixedTransfer

end
end
end


end
