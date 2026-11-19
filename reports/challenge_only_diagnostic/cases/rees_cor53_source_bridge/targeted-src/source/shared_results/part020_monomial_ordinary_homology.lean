module
public import graph_foundation.part014
public import shared_results.part020_closed_graph_ideal_betti_comparison

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialOrdinaryHomology -/
section

/-!
# The actual ordinary monomial Koszul homology and its fine decomposition

The ordinary complex is the homogeneous subcomplex of the literal ideal
Koszul complex. Its degree-zero outgoing differential is zero. The finite
coarsening equivalence acts by the actual fine projections and commutes
with both adjacent differentials. Consequently its homology, and hence
its Betti number, is the sum of the genuine fine derived-Tor components.
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

abbrev OrdinaryFineIndex (V : Type u) [Fintype V] (q : ℕ) :=
  {α : Exponent V // α.degree = q}

instance ordinaryFineIndex_finite (q : ℕ) : Finite (OrdinaryFineIndex V q) := by
  let Q := {α : Exponent V // α.degree ≤ q}
  letI : Finite Q := (Finsupp.finite_of_degree_le q).to_subtype
  exact Finite.of_injective (fun α : OrdinaryFineIndex V q =>
    (⟨α.val, α.property.le⟩ : Q))
      (fun α β h => Subtype.ext (congrArg (fun z : Q => z.val) h))

instance ordinaryFineIndex_fintype (q : ℕ) : Fintype (OrdinaryFineIndex V q) :=
  Fintype.ofFinite _

lemma monomialDifferential_ordinary (B : Family V) (q p : ℕ)
    {x : Set.powersetCard V (p+1) →₀ monomialIdeal k B}
    (hx : x ∈ ordinaryMonomialPiece (k := k) B q (p+1)) :
    monomialDifferential (k := k) B p x ∈ ordinaryMonomialPiece (k := k) B q p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have hf := monomialDifferential_homogeneous (k := k) B (monomialDegree a) p
        (Grading.basis_mem_piece (monomialCoefficientBasis (k := k) B (p+1)) monomialDegree a)
      apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) hf
      change monomialDegree i = monomialDegree a at hi
      change (monomialDegree i).degree = q
      change (monomialDegree a).degree = q at ha
      rw [hi, ha]
  | zero => simpa only [map_zero] using
      (Submodule.zero_mem (ordinaryMonomialPiece (k := k) B q p))
  | add x y hx hy ihx ihy => simpa only [map_add] using
      (Submodule.add_mem (ordinaryMonomialPiece (k := k) B q p) ihx ihy)
  | smul r x hx ih => simpa only [map_smul] using
      (Submodule.smul_mem (ordinaryMonomialPiece (k := k) B q p) r ih)

def ordinaryMonomialDifferential (B : Family V) (q p : ℕ) :
    ordinaryMonomialPiece (k := k) B q (p+1) →ₗ[k] ordinaryMonomialPiece (k := k) B q p :=
  ((monomialDifferential (k := k) B p).domRestrict _).codRestrict _
    (fun x => monomialDifferential_ordinary (k := k) B q p x.property)

def ordinaryMonomialPrevious (B : Family V) (q : ℕ) : ∀ p : ℕ,
    ordinaryMonomialPiece (k := k) B q p →ₗ[k] ordinaryMonomialPiece (k := k) B q p.pred
  | 0 => 0
  | p+1 => ordinaryMonomialDifferential (k := k) B q p

@[simp] lemma ordinaryMonomialPrevious_val (B : Family V) (q p : ℕ)
    (x : ordinaryMonomialPiece (k := k) B q p) :
    (ordinaryMonomialPrevious (k := k) B q p x).val = monomialPreviousDifferential (k := k) B p x.val := by
  cases p <;> rfl

lemma ordinaryMonomialDifferential_comp (B : Family V) (q p : ℕ) :
    (ordinaryMonomialPrevious (k := k) B q p).comp
      (ordinaryMonomialDifferential (k := k) B q p) = 0 := by
  cases p with
  | zero => simp only [ordinaryMonomialPrevious, LinearMap.zero_comp]
  | succ p =>
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (monomialDifferential_comp (k := k) B p) x.val

abbrev ordinaryMonomialHomology (B : Family V) (q p : ℕ) :=
  FourPapers.FilteredHomology.Homology (K := k)
    (X := ordinaryMonomialPiece (k := k) B q (p+1))
    (Y := ordinaryMonomialPiece (k := k) B q p)
    (Z := ordinaryMonomialPiece (k := k) B q p.pred)
    (ordinaryMonomialDifferential (k := k) B q p)
    (ordinaryMonomialPrevious (k := k) B q p) (ordinaryMonomialDifferential_comp (k := k) B q p)

def monomialFinePrevious (B : Family V) (α : Exponent V) : ∀ p : ℕ,
    homogeneousPiece (k := k) B α p →ₗ[k] homogeneousPiece (k := k) B α p.pred
  | 0 => 0
  | p+1 => homogeneousDifferential (k := k) B α p

lemma monomialFineDifferential_comp (B : Family V) (α : Exponent V) (p : ℕ) :
    (monomialFinePrevious (k := k) B α p).comp (homogeneousDifferential (k := k) B α p) = 0 := by
  cases p with
  | zero => simp only [monomialFinePrevious, LinearMap.zero_comp]
  | succ p => exact homogeneousDifferential_comp (k := k) B α p

abbrev monomialFineHomology (B : Family V) (α : Exponent V) (p : ℕ) :=
  FourPapers.FilteredHomology.Homology (K := k)
    (X := homogeneousPiece (k := k) B α (p+1))
    (Y := homogeneousPiece (k := k) B α p)
    (Z := homogeneousPiece (k := k) B α p.pred)
    (homogeneousDifferential (k := k) B α p)
    (monomialFinePrevious (k := k) B α p) (monomialFineDifferential_comp (k := k) B α p)

def ordinaryMonomialPieceEquivPi (B : Family V) (q p : ℕ) :
    ordinaryMonomialPiece (k := k) B q p ≃ₗ[k]
      ∀ α : OrdinaryFineIndex V q, homogeneousPiece (k := k) B α.val p where
  toFun x α := ⟨homogeneousProjection (k := k) B α.val p x.val,
    homogeneousProjection_mem (k := k) B α.val p x.val⟩
  invFun y := ⟨∑ α, (y α).val, by
    apply Submodule.sum_mem
    intro α _
    apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) (y α).property
    change monomialDegree i = α.val at hi
    change (monomialDegree i).degree = q
    rw [hi, α.property]⟩
  left_inv x := by
    apply Subtype.ext
    apply (monomialCoefficientBasis (k := k) B p).repr.injective
    ext i
    simp only [map_sum, Finsupp.finset_sum_apply, homogeneousProjection,
      Grading.projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Grading.filterMap_apply, Finsupp.filter_apply]
    by_cases hz : (monomialCoefficientBasis (k := k) B p).repr x.val i = 0
    · simp only [hz, ite_self, Finset.sum_const_zero]
    · have hi := (Grading.mem_piece (monomialCoefficientBasis (k := k) B p) (fun i => (monomialDegree i).degree) q x.val).mp
        x.property i hz
      let α : OrdinaryFineIndex V q := ⟨monomialDegree i, hi⟩
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
    change homogeneousProjection (k := k) B α.val p (∑ β, (y β).val) = (y α).val
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
    exact map_add (homogeneousProjection (k := k) B α.val p) x.val y.val
  map_smul' r x := by
    funext α
    apply Subtype.ext
    exact map_smul (homogeneousProjection (k := k) B α.val p) r x.val

lemma ordinaryMonomialPieceEquivPi_differential (B : Family V) (q p : ℕ)
    (x : ordinaryMonomialPiece (k := k) B q (p+1)) (α : OrdinaryFineIndex V q) :
    ordinaryMonomialPieceEquivPi (k := k) B q p (ordinaryMonomialDifferential (k := k) B q p x) α =
      homogeneousDifferential (k := k) B α.val p (ordinaryMonomialPieceEquivPi (k := k) B q (p+1) x α) := by
  apply Subtype.ext
  change homogeneousProjection (k := k) B α.val p
    (monomialDifferential (k := k) B p x.val) =
      monomialDifferential (k := k) B p
        (homogeneousProjection (k := k) B α.val (p+1) x.val)
  exact LinearMap.congr_fun (homogeneousProjection_differential (k := k) B α.val p) x.val

lemma ordinaryMonomialPieceEquivPi_previous (B : Family V) (q p : ℕ)
    (x : ordinaryMonomialPiece (k := k) B q p) (α : OrdinaryFineIndex V q) :
    ordinaryMonomialPieceEquivPi (k := k) B q p.pred (ordinaryMonomialPrevious (k := k) B q p x) α =
      monomialFinePrevious (k := k) B α.val p (ordinaryMonomialPieceEquivPi (k := k) B q p x α) := by
  cases p with
  | zero =>
      apply Subtype.ext
      change Grading.projection (monomialCoefficientBasis (k := k) B 0)
        monomialDegree α.val 0 = 0
      exact map_zero _
  | succ p => exact ordinaryMonomialPieceEquivPi_differential (k := k) B q p x α

/-- The literal ordinary cycle/boundary quotient is the finite product of
the literal fine cycle/boundary quotients, including homological degree zero. -/
def ordinaryMonomialHomologyEquivPi (B : Family V) (q p : ℕ) :
    ordinaryMonomialHomology (k := k) B q p ≃ₗ[k]
      ∀ α : OrdinaryFineIndex V q, monomialFineHomology (k := k) B α.val p := by
  let f := fun α : OrdinaryFineIndex V q => homogeneousDifferential (k := k) B α.val p
  let g := fun α : OrdinaryFineIndex V q => monomialFinePrevious (k := k) B α.val p
  let hfg := fun α : OrdinaryFineIndex V q => monomialFineDifferential_comp (k := k) B α.val p
  refine (threeTermHomologyEquiv (R := k)
    (X := ordinaryMonomialPiece (k := k) B q (p+1))
    (Y := ordinaryMonomialPiece (k := k) B q p)
    (Z := ordinaryMonomialPiece (k := k) B q p.pred)
    (X' := ∀ α : OrdinaryFineIndex V q, homogeneousPiece (k := k) B α.val (p+1))
    (Y' := ∀ α : OrdinaryFineIndex V q, homogeneousPiece (k := k) B α.val p)
    (Z' := ∀ α : OrdinaryFineIndex V q, homogeneousPiece (k := k) B α.val p.pred)
    (ordinaryMonomialDifferential (k := k) B q p) (ordinaryMonomialPrevious (k := k) B q p)
    (ordinaryMonomialDifferential_comp (k := k) B q p)
    (componentwiseMap f) (componentwiseMap g) (componentwiseMap_comp f g hfg)
    (ordinaryMonomialPieceEquivPi (k := k) B q (p+1)) (ordinaryMonomialPieceEquivPi (k := k) B q p)
    (ordinaryMonomialPieceEquivPi (k := k) B q p.pred) ?_ ?_).trans
      (componentwiseHomologyEquiv f g hfg)
  · intro x
    funext α
    exact ordinaryMonomialPieceEquivPi_differential (k := k) B q p x α
  · intro x
    funext α
    exact ordinaryMonomialPieceEquivPi_previous (k := k) B q p x α

/-- The three-term definition is exactly the categorical homology of the
genuine fine Koszul subcomplex; degree zero is not shifted or discarded. -/
def monomialFineCategoricalHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    (homogeneousComplex (k := k) B α).homology p ≃ₗ[k] monomialFineHomology (k := k) B α p := by
  let C := homogeneousComplex (k := k) B α
  let T := C.sc' (p+1) p p.pred
  have hfg : T.g.hom.comp T.f.hom = 0 := by
    apply LinearMap.ext
    intro x
    exact T.moduleCat_zero_apply x
  refine (((C.homologyIsoSc' (p+1) p p.pred (by simp) (by cases p <;> simp)) ≪≫
    T.moduleCatHomologyIso).toLinearEquiv).trans
      (threeTermHomologyEquiv T.f.hom T.g.hom hfg
        (homogeneousDifferential (k := k) B α p) (monomialFinePrevious (k := k) B α p)
        (monomialFineDifferential_comp (k := k) B α p)
        (LinearEquiv.refl k _) (LinearEquiv.refl k _) (LinearEquiv.refl k _) ?_ ?_)
  · intro x
    change ((homogeneousComplex (k := k) B α).d (p+1) p).hom x = homogeneousDifferential (k := k) B α p x
    rw [homogeneousComplex_d]
    rfl
  · intro x
    cases p with
    | zero =>
        change (C.d 0 0).hom x = 0
        rw [C.shape 0 0 (by simp)]
        rfl
    | succ p =>
        change ((homogeneousComplex (k := k) B α).d (p+1) p).hom x = homogeneousDifferential (k := k) B α p x
        rw [homogeneousComplex_d]
        rfl

theorem ordinaryMonomialHomology_subsingleton_of_exact (B : Family V) (q p : ℕ)
    (hexact : MonomialOrdinaryExact (k := k) B q p) :
    Subsingleton (ordinaryMonomialHomology (k := k) B q p) := by
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (boundaryMap
    (ordinaryMonomialDifferential (k := k) B q p) (ordinaryMonomialPrevious (k := k) B q p)
    (ordinaryMonomialDifferential_comp (k := k) B q p))).mkQ_surjective z
  have hx : monomialPreviousDifferential (k := k) B p x.val.val = 0 := by
    simpa only [ordinaryMonomialPrevious_val, Submodule.coe_zero] using congrArg Subtype.val x.property
  obtain ⟨y, hy, hdy⟩ := hexact x.val.val x.val.property hx
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext hdy)⟩

end General
section Field
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance monomialFineHomology_finite (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.Finite k (monomialFineHomology (k := k) B α p) :=
  Module.Finite.equiv (monomialFineCategoricalHomologyEquiv (k := k) B α p)

lemma monomialFineHomology_finrank (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.finrank k (monomialFineHomology (k := k) B α p) = bettiNumber (k := k) B α p :=
  (monomialFineCategoricalHomologyEquiv (k := k) B α p).finrank_eq.symm.trans
    (gradedTorIso (k := k) B α p).toLinearEquiv.finrank_eq

/-- Ordinary Betti numbers are dimensions of actual ordinary Koszul
homology. The following theorem, rather than the definition, computes them
as the sum of the fine derived-Tor dimensions. -/
def ordinaryMonomialBettiNumber (B : Family V) (q p : ℕ) : ℕ :=
  Module.finrank k (ordinaryMonomialHomology (k := k) B q p)

theorem ordinaryMonomialBettiNumber_eq_sum (B : Family V) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := k) B q p =
      ∑ α : OrdinaryFineIndex V q, bettiNumber (k := k) B α.val p := by
  rw [ordinaryMonomialBettiNumber, (ordinaryMonomialHomologyEquivPi (k := k) B q p).finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro α _
  exact monomialFineHomology_finrank (k := k) B α.val p

end Field
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.ordinaryMonomialHomologyEquivPi
#print axioms FourPapers.Sublattice.ordinaryMonomialBettiNumber_eq_sum

end
end


end
