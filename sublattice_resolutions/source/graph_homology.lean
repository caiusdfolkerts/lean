module
public import graph_foundation

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealGradedHomology -/
section

/-! # Associated homology of the actual ordinary ideal strands

The associated chain groups are finite products of genuine fine monomial
Koszul groups. The comparison includes homological degree zero and retains
ordinary degree and variable weight separately. Freeness, finite generation,
and the explicit vanishing bounds therefore concern the original ideal's
literal cycle/boundary quotient.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

abbrev IdealOrdinaryFineIndex (w : V → ℕ) (q n : ℕ) :=
  {α : Exponent V // (α.degree, Finsupp.weight w α) = (q,n)}

instance idealOrdinaryFineIndex_finite (w : V → ℕ) (q n : ℕ) :
    Finite (IdealOrdinaryFineIndex w q n) := by
  let Q := {α : Exponent V // α.degree ≤ q}
  letI : Finite Q := (Finsupp.finite_of_degree_le q).to_subtype
  exact Finite.of_injective
    (fun α : IdealOrdinaryFineIndex w q n =>
      (⟨α.val, (congrArg Prod.fst α.property).le⟩ : Q))
    (fun α β h => Subtype.ext (congrArg (fun z : Q => z.val) h))

/-- Compose the two basis restrictions and the model map while the
ambient modules and bases are abstract. Component equivalences are built
inside the construction, so specialization only supplies ambient data. -/
def ordinaryWeightFineEquiv
    {R X Y I J Γ : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (degree : I → Γ) (modelDegree : J → Γ) (e : X ≃ₗ[R] Y)
    (he : ∀ α x, e x ∈ Grading.Piece c modelDegree α ↔
      x ∈ Grading.Piece b degree α)
    (ordinary weight : Γ → ℕ) (q n : ℕ)
    [Finite {α : Γ // (ordinary α, weight α) = (q, n)}] :=
  let f (α : Γ) : Grading.Piece b degree α ≃ₗ[R] Grading.Piece c modelDegree α :=
    { toFun := fun x => ⟨e x.val, (he α x.val).mpr x.property⟩
      invFun := fun y => ⟨e.symm y.val, (he α (e.symm y.val)).mp (by
        simpa only [e.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val)
      map_add' := fun x y => Subtype.ext (e.map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext (e.map_smul r x.val) }
  (basisGradeEquiv (Grading.restrictedBasis b (fun i => ordinary (degree i) = q))
    (fun i => weight (degree i.val)) n).trans
    ((basisIteratedPieceEquiv b (fun i => ordinary (degree i))
      (fun i => weight (degree i)) q n).trans
      ((basisCoarseningEquivPi b degree (fun α => (ordinary α, weight α)) (q, n)).trans
        (LinearEquiv.piCongrRight (fun α : {α : Γ // (ordinary α, weight α) = (q, n)} =>
          f α.val))))

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
/-- The associated weight quotient of the actual ordinary ideal strand is
its family of genuine fine monomial pieces. This specializes the abstract
construction to the proved monic coefficient basis and actual model map. -/
def actualIdealOrdinaryGradeEquiv (P : QuotientGroebnerData V k)
    (w : V → ℕ) (q p n : ℕ) :=
  ordinaryWeightFineEquiv (R := k) (X := Set.powersetCard V p →₀ P.ideal)
    (Y := Set.powersetCard V p →₀ monomialIdeal k P.family)
    (I := ActualIdealIndex P p) (J := MonomialIndex P.family p) (Γ := Exponent V)
    (actualIdealCoefficientBasis P p) (monomialCoefficientBasis (k := k) P.family p)
    (actualIdealDegree (P := P) (p := p)) (monomialDegree (B := P.family) (i := p))
    (actualIdealMonomialEquiv P p)
    (fun α x => actualIdealMonomialEquiv_piece_iff P p id α x)
    Finsupp.degree (Finsupp.weight w) q n

@[simp] theorem actualIdealOrdinaryGradeEquiv_apply (P : QuotientGroebnerData V k)
    (w : V → ℕ) (q p n : ℕ)
    (x : Grade (actualIdealOrdinaryFiltration P w q p) n)
    (α : IdealOrdinaryFineIndex w q n) :
    (actualIdealOrdinaryGradeEquiv P w q p n x α).val =
      actualIdealMonomialEquiv P p
        (Grading.projection (actualIdealCoefficientBasis P p) actualIdealDegree α.val
          ((basisGradeEquiv (actualIdealOrdinaryBasis P q p)
            (fun a => Finsupp.weight w (actualIdealDegree a.val)) n x).val.val)) := rfl

def homogeneousIdealPrevious (B : Family V) (α : Exponent V) : ∀ p : ℕ,
    homogeneousPiece (k := k) B α p →ₗ[k] homogeneousPiece (k := k) B α p.pred
  | 0 => 0
  | p+1 => homogeneousDifferential B α p

theorem homogeneousIdealPrevious_comp (B : Family V) (α : Exponent V) (p : ℕ) :
    (homogeneousIdealPrevious (k := k) B α p).comp
      (homogeneousDifferential B α p) = 0 := by
  cases p with
  | zero => simp only [homogeneousIdealPrevious, LinearMap.zero_comp]
  | succ p => exact homogeneousDifferential_comp B α p

abbrev homogeneousIdealHomology (B : Family V) (α : Exponent V) (p : ℕ) :=
  Homology (homogeneousDifferential (k := k) B α p)
    (homogeneousIdealPrevious B α p) (homogeneousIdealPrevious_comp B α p)

/-- The three-term quotient is exactly the usual categorical fine
homology, including the zero outgoing differential in homological degree zero. -/
def homogeneousIdealHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    homogeneousIdealHomology (k := k) B α p ≃ₗ[k]
      (homogeneousComplex (k := k) B α).homology p := by
  let C := homogeneousComplex (k := k) B α
  let S := C.sc' (p+1) p p.pred
  have hS : S.g.hom.comp S.f.hom = 0 := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom S.zero
  let e := threeTermHomologyEquiv
    (homogeneousDifferential (k := k) B α p) (homogeneousIdealPrevious B α p)
    (homogeneousIdealPrevious_comp B α p) S.f.hom S.g.hom hS
    (LinearEquiv.refl k _) (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (fun x => by
      change homogeneousDifferential B α p x = (C.d (p+1) p).hom x
      rw [homogeneousComplex_d]
      rfl)
    (fun x => by
      cases p with
      | zero =>
          change (0 : homogeneousPiece (k := k) B α 0) = (C.d 0 0).hom x
          rw [C.shape 0 0 (by simp)]
          rfl
      | succ p =>
          change homogeneousDifferential B α p x = (C.d (p+1) p).hom x
          rw [homogeneousComplex_d]
          rfl)
  exact e.trans (S.moduleCatHomologyIso.toLinearEquiv.symm.trans
    (C.homologyIsoSc' (p+1) p p.pred (by simp) (by cases p <;> simp)).toLinearEquiv.symm)

variable (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (w : V → ℕ)
  (htail : ∀ g ∈ P.generators, g ≠ 0 →
    ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
  (hstrict : ∀ p (a : ActualIdealIndex P p) (b : ActualIdealIndex P p.pred),
    Finsupp.weight w (actualIdealDegree a) ≤ Finsupp.weight w (actualIdealDegree b) →
    (actualIdealCoefficientBasis P p.pred).repr
      (actualIdealPreviousDifferential P.ideal p (actualIdealCoefficientBasis P p a) -
        initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a)) b = 0)

include hstrict in
theorem actualIdealOrdinaryGradeEquiv_previous (q p n : ℕ)
    (x : Grade (actualIdealOrdinaryFiltration P w q p) n)
    (α : IdealOrdinaryFineIndex w q n) :
    actualIdealOrdinaryGradeEquiv P w q p.pred n
        (actualIdealGradePrevious P hJ w htail q p n x) α =
      homogeneousIdealPrevious P.family α.val p
        (actualIdealOrdinaryGradeEquiv P w q p n x α) := by
  apply Subtype.ext
  rw [actualIdealOrdinaryGradeEquiv_apply]
  have hd := basisGradeEquiv_differential_of_lower
    (actualIdealOrdinaryBasis P q p) (actualIdealOrdinaryBasis P q p.pred)
    (fun a => Finsupp.weight w (actualIdealDegree a.val))
    (fun a => Finsupp.weight w (actualIdealDegree a.val))
    (actualIdealOrdinaryPrevious P hJ q p) (initialActualIdealOrdinaryPrevious P q p)
    (initialActualIdealOrdinaryPrevious_basis_weight P w q p)
    (actualIdealOrdinaryPrevious_strictly_lowers P hJ w hstrict q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p) n x
  have hdv := congrArg Subtype.val hd
  change ((basisGradeEquiv (actualIdealOrdinaryBasis P q p.pred)
      (fun a => Finsupp.weight w (actualIdealDegree a.val)) n
      (actualIdealGradePrevious P hJ w htail q p n x)).val.val) =
    (initialActualIdealOrdinaryPrevious P q p
      ((basisGradeEquiv (actualIdealOrdinaryBasis P q p)
        (fun a => Finsupp.weight w (actualIdealDegree a.val)) n x).val)).val at hdv
  change actualIdealMonomialEquiv P p.pred
      (Grading.projection (actualIdealCoefficientBasis P p.pred) actualIdealDegree α.val
        ((basisGradeEquiv (actualIdealOrdinaryBasis P q p.pred)
          (fun a => Finsupp.weight w (actualIdealDegree a.val)) n
          (actualIdealGradePrevious P hJ w htail q p n x)).val.val)) = _
  rw [hdv, initialActualIdealOrdinaryPrevious_val]
  have hc := LinearMap.congr_fun (fineProjection_commutes
    (R := k) (X := Set.powersetCard V p →₀ P.ideal)
    (Y := Set.powersetCard V p.pred →₀ P.ideal)
    (I := ActualIdealIndex P p) (J := ActualIdealIndex P p.pred) (Γ := Exponent V)
    (actualIdealCoefficientBasis P p) (actualIdealCoefficientBasis P p.pred)
    (actualIdealDegree (P := P) (p := p))
    (actualIdealDegree (P := P) (p := p.pred)) (initialActualIdealPrevious P p)
    (by
      intro a
      simpa only [id_def] using initialActualIdealPrevious_basis_regrade P id p a) α.val)
      ((basisGradeEquiv (actualIdealOrdinaryBasis P q p)
        (fun a => Finsupp.weight w (actualIdealDegree a.val)) n x).val.val)
  simp only [LinearMap.comp_apply] at hc
  cases p with
  | zero => simp only [initialActualIdealOrdinaryPrevious, initialActualIdealPrevious, LinearMap.zero_apply,
      ZeroMemClass.coe_zero, map_zero, homogeneousIdealPrevious]
  | succ p =>
      rw [← hc]
      change actualIdealMonomialEquiv P p (initialActualIdealDifferential P p _) =
        monomialDifferential (k := k) P.family p
          ((actualIdealOrdinaryGradeEquiv P w q (p+1) n x α).val)
      rw [actualIdealMonomialEquiv_differential, actualIdealOrdinaryGradeEquiv_apply]

abbrev filtrationGradeAddCommGroup
    {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    (F : Filtration (K := R) X) (n : ℕ) : AddCommGroup (Grade F n) := inferInstance

abbrev filtrationGradeModule
    {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    (F : Filtration (K := R) X) (n : ℕ) : Module R (Grade F n) := inferInstance

/-- Transparent names for the existing quotient structures prevent instance
search from expanding the concrete polynomial basis and its nested spans. -/
abbrev actualIdealOrdinaryGradeAddCommGroup (q p n : ℕ) :
    AddCommGroup (Grade (actualIdealOrdinaryFiltration P w q p) n) :=
  filtrationGradeAddCommGroup (R := k) (X := actualIdealOrdinaryPiece P q p)
    (actualIdealOrdinaryFiltration P w q p) n

abbrev actualIdealOrdinaryGradeModule (q p n : ℕ) :
    Module k (Grade (actualIdealOrdinaryFiltration P w q p) n) :=
  filtrationGradeModule (R := k) (X := actualIdealOrdinaryPiece P q p)
    (actualIdealOrdinaryFiltration P w q p) n

attribute [instance 100] actualIdealOrdinaryGradeAddCommGroup actualIdealOrdinaryGradeModule

abbrev actualIdealGradedHomologyAddCommGroup (q p n : ℕ) :
    AddCommGroup (actualIdealGradedHomology P hJ w htail q p n) :=
  Submodule.Quotient.addCommGroup (R := k)
    (M := ↥(LinearMap.ker (actualIdealGradePrevious P hJ w htail q p n)))
    (LinearMap.range (boundaryMap (actualIdealGradeDifferential P hJ w htail q p n)
      (actualIdealGradePrevious P hJ w htail q p n)
      (actualIdealGradeDifferential_comp P hJ w htail q p n)))

abbrev actualIdealGradedHomologyModule (q p n : ℕ) :
    Module k (actualIdealGradedHomology P hJ w htail q p n) :=
  Submodule.Quotient.module (R := k)
    (M := ↥(LinearMap.ker (actualIdealGradePrevious P hJ w htail q p n)))
    (LinearMap.range (boundaryMap (actualIdealGradeDifferential P hJ w htail q p n)
      (actualIdealGradePrevious P hJ w htail q p n)
      (actualIdealGradeDifferential_comp P hJ w htail q p n)))

attribute [instance 100] actualIdealGradedHomologyAddCommGroup actualIdealGradedHomologyModule

@[simp] theorem actualIdealGradePrevious_succ (q p n : ℕ) :
    actualIdealGradePrevious P hJ w htail q (p+1) n =
      actualIdealGradeDifferential P hJ w htail q p n := rfl

include hstrict in
theorem actualIdealOrdinaryGradeEquiv_differential (q p n : ℕ)
    (x : Grade (actualIdealOrdinaryFiltration P w q (p+1)) n)
    (α : IdealOrdinaryFineIndex w q n) :
    actualIdealOrdinaryGradeEquiv P w q p n
        (actualIdealGradeDifferential P hJ w htail q p n x) α =
      homogeneousDifferential (k := k) P.family α.val p
        (actualIdealOrdinaryGradeEquiv P w q (p+1) n x α) := by
  have h := actualIdealOrdinaryGradeEquiv_previous P hJ w htail hstrict q (p+1) n x α
  rw [actualIdealGradePrevious_succ] at h
  simpa only [Nat.pred_succ, homogeneousIdealPrevious] using h

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
include hstrict in
/-- The genuine associated homology is a finite product of genuine fine
monomial Koszul homologies. No dimension argument is used. -/
def actualIdealGradedHomologyEquiv (q p n : ℕ) :
    actualIdealGradedHomology P hJ w htail q p n ≃ₗ[k]
      ∀ α : IdealOrdinaryFineIndex w q n,
        (homogeneousComplex (k := k) P.family α.val).homology p :=
  threeTermProductHomologyEquiv (R := k)
    (X := Grade (actualIdealOrdinaryFiltration P w q (p+1)) n)
    (Y := Grade (actualIdealOrdinaryFiltration P w q p) n)
    (Z := Grade (actualIdealOrdinaryFiltration P w q p.pred) n)
    (I := IdealOrdinaryFineIndex w q n)
    (X' := fun α => homogeneousPiece (k := k) P.family α.val (p+1))
    (Y' := fun α => homogeneousPiece (k := k) P.family α.val p)
    (Z' := fun α => homogeneousPiece (k := k) P.family α.val p.pred)
    (H' := fun α => (homogeneousComplex (k := k) P.family α.val).homology p)
    (actualIdealGradeDifferential P hJ w htail q p n)
    (actualIdealGradePrevious P hJ w htail q p n)
    (actualIdealGradeDifferential_comp P hJ w htail q p n)
    (fun α => homogeneousDifferential (k := k) P.family α.val p)
    (fun α => homogeneousIdealPrevious (k := k) P.family α.val p)
    (fun α => homogeneousIdealPrevious_comp (k := k) P.family α.val p)
    (actualIdealOrdinaryGradeEquiv P w q (p+1) n)
    (actualIdealOrdinaryGradeEquiv P w q p n)
    (actualIdealOrdinaryGradeEquiv P w q p.pred n)
    (fun x α => actualIdealOrdinaryGradeEquiv_differential P hJ w htail hstrict q p n x α)
    (fun x α => actualIdealOrdinaryGradeEquiv_previous P hJ w htail hstrict q p n x α)
    (fun α => homogeneousIdealHomologyEquiv (k := k) P.family α.val p)


include htail hstrict in
theorem actualIdealOrdinaryHomology_free_of_monomial (M : ℕ) (hM : ∀ v, w v ≤ M)
    (hlift : ∀ p, LiftsCycles (actualIdealCoordinateFiltration P w p)
      (actualIdealCoordinateFiltration P w p.pred) (actualIdealPreviousDifferential P.ideal p))
    (q p : ℕ)
    (hfree : ∀ α : Exponent V, Module.Free k
      ((homogeneousComplex (k := k) P.family α).homology p)) :
    Module.Free k (actualIdealOrdinaryHomology P hJ q p) := by
  apply homology_free_of_leading_free
    (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
    (actualIdealOrdinaryFiltration P w q p.pred)
    (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_preserves P hJ w htail q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p)
    (M*q+1) (actualIdealOrdinaryFiltration_top P w M hM q p)
    (actualIdealOrdinaryPrevious_lifts P hJ w q (p+1) (hlift (p+1)))
    (actualIdealOrdinaryPrevious_lifts P hJ w q p (hlift p))
  intro n hn
  letI : ∀ α : IdealOrdinaryFineIndex w q n,
      Module.Free k ((homogeneousComplex (k := k) P.family α.val).homology p) :=
    fun α => hfree α.val
  exact Module.Free.of_equiv (actualIdealGradedHomologyEquiv P hJ w htail hstrict q p n).symm

include htail hstrict in
theorem actualIdealOrdinaryHomology_finite_of_monomial (M : ℕ) (hM : ∀ v, w v ≤ M)
    (hlift : ∀ p, LiftsCycles (actualIdealCoordinateFiltration P w p)
      (actualIdealCoordinateFiltration P w p.pred) (actualIdealPreviousDifferential P.ideal p))
    (q p : ℕ)
    (hfree : ∀ α : Exponent V, Module.Free k
      ((homogeneousComplex (k := k) P.family α).homology p))
    (hfinite : ∀ α : Exponent V, Module.Finite k
      ((homogeneousComplex (k := k) P.family α).homology p)) :
    Module.Finite k (actualIdealOrdinaryHomology P hJ q p) := by
  apply homology_finite_of_leading_finite_free
    (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
    (actualIdealOrdinaryFiltration P w q p.pred)
    (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_preserves P hJ w htail q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p)
    (M*q+1) (actualIdealOrdinaryFiltration_top P w M hM q p)
    (actualIdealOrdinaryPrevious_lifts P hJ w q (p+1) (hlift (p+1)))
    (actualIdealOrdinaryPrevious_lifts P hJ w q p (hlift p))
  · intro n hn
    letI : ∀ α : IdealOrdinaryFineIndex w q n,
        Module.Free k ((homogeneousComplex (k := k) P.family α.val).homology p) :=
      fun α => hfree α.val
    exact Module.Free.of_equiv (actualIdealGradedHomologyEquiv P hJ w htail hstrict q p n).symm
  · intro n hn
    letI : ∀ α : IdealOrdinaryFineIndex w q n,
        Module.Finite k ((homogeneousComplex (k := k) P.family α.val).homology p) :=
      fun α => hfinite α.val
    exact Module.Finite.equiv (actualIdealGradedHomologyEquiv P hJ w htail hstrict q p n).symm

include htail hstrict in
/-- Vanishing of the literal monomial strands forces vanishing of the
actual ordinary strand. This follows by finite downward filling and does
not require choosing a homology basis. -/
theorem actualIdealOrdinaryHomology_subsingleton_of_monomial (q p : ℕ)
    (hzero : ∀ α : Exponent V, α.degree=q →
      Subsingleton ((homogeneousComplex (k := k) P.family α).homology p)) :
    Subsingleton (actualIdealOrdinaryHomology P hJ q p) := by
  let F := actualIdealOrdinaryFiltration P w q (p+1)
  let H := actualIdealOrdinaryFiltration P w q p
  let L := actualIdealOrdinaryFiltration P w q p.pred
  let f := actualIdealOrdinaryDifferential P hJ q p
  let g := actualIdealOrdinaryPrevious P hJ q p
  let hf := actualIdealOrdinaryDifferential_preserves P hJ w htail q p
  let hg := actualIdealOrdinaryPrevious_preserves P hJ w htail q p
  let hfg := actualIdealOrdinaryDifferential_comp P hJ q p
  have hgrade (n : ℕ) : Subsingleton (GradedHomology F H L f g hf hg hfg n) := by
    letI : ∀ α : IdealOrdinaryFineIndex w q n,
        Subsingleton ((homogeneousComplex (k := k) P.family α.val).homology p) :=
      fun α => hzero α.val (congrArg Prod.fst α.property)
    exact ⟨fun x y => (actualIdealGradedHomologyEquiv P hJ w htail hstrict q p n).injective
      (Subsingleton.elim _ _)⟩
  apply homology_subsingleton_of_cycle_filling f g hfg
  intro y hy
  obtain ⟨n, hn⟩ := H.exhaustive y
  obtain ⟨x, hx, he⟩ := filtered_boundary_of_gradedHomology_subsingleton F H L f g
    hf hg hfg hgrade n y hn hy
  exact ⟨x, he⟩

end FourPapers.Sublattice

end
end
end

#print axioms FourPapers.Sublattice.actualIdealGradedHomologyEquiv
#print axioms FourPapers.Sublattice.actualIdealOrdinaryHomology_free_of_monomial
#print axioms FourPapers.Sublattice.actualIdealOrdinaryHomology_finite_of_monomial
#print axioms FourPapers.Sublattice.actualIdealOrdinaryHomology_subsingleton_of_monomial

end
