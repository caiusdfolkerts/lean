module

public import PaperVerification.PluckerWeightOrder
public import PaperVerification.ProjSurjectionRange
public import PaperVerification.IsotropicAttractingEmpty

/-!
# A finite filtration of the actual common-isotropic projective scheme

The stage at `m` is the original homogeneous quotient with the first `m`
Plücker coordinates set to zero. Its inclusion is a genuine closed
immersion. The next complement is its genuine pivot basic open, whose
full coordinate ring was computed in the preceding files. Independent
pivots give affine spaces, and every other pivot gives an empty scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PaperVerification.IsotropicAttractingCharts

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

/-- The actual projective scheme at a set of vanishing original
homogeneous coordinates. -/
def filtrationScheme (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) : Scheme :=
  Proj (HomogeneousQuotientProjective.grading (filtrationIdeal (K := K) E c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂))

theorem originalIdeal_le_filtrationIdeal
    (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    isotropicPluckerIdeal (t := t) (canonicalForms (K := K) (n := n) c₁ c₂) ≤
      filtrationIdeal E c₁ c₂ := le_sup_left

/-- Inclusion into the original common-isotropic projective scheme. -/
def filtrationToOriginal (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) E c₁ c₂ ⟶
      Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂)) :=
  HomogeneousQuotientProjective.quotientProjMap
    (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (filtrationIdeal E c₁ c₂)
    (isotropicPluckerIdeal_isHomogeneous (canonicalForms (K := K) (n := n) c₁ c₂))
    (filtrationIdeal_isHomogeneous E c₁ c₂) (originalIdeal_le_filtrationIdeal E c₁ c₂)

instance filtrationToOriginal_isClosedImmersion
    (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosedImmersion (filtrationToOriginal (K := K) E c₁ c₂) :=
  inferInstanceAs (IsClosedImmersion (HomogeneousQuotientProjective.quotientProjMap _ _ _ _ _))

/-- Inclusion of a later filtration stage into an earlier stage. -/
def filtrationInclusion {E F : Set (PluckerIndex (t+2) n)} (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) F c₁ c₂ ⟶ filtrationScheme (K := K) E c₁ c₂ :=
  HomogeneousQuotientProjective.quotientProjMap
    (filtrationIdeal E c₁ c₂) (filtrationIdeal F c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂)
    (filtrationIdeal_isHomogeneous F c₁ c₂) (filtrationIdeal_mono hEF c₁ c₂)

instance filtrationInclusion_isClosedImmersion
    {E F : Set (PluckerIndex (t+2) n)} (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    IsClosedImmersion (filtrationInclusion (K := K) hEF c₁ c₂) :=
  inferInstanceAs (IsClosedImmersion (HomogeneousQuotientProjective.quotientProjMap _ _ _ _ _))

/-- The exact underlying prime-ideal condition on the actual stage image. -/
theorem filtrationToOriginal_range
    (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ)
    (x : Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))) :
    x ∈ Set.range (filtrationToOriginal E c₁ c₂) ↔
      ∀ I ∈ E, Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (X I)
        ∈ x.asHomogeneousIdeal.toIdeal := by
  have hr := HomogeneousQuotientProjective.quotientProjMap_range
    (isotropicPluckerIdeal (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))
    (filtrationIdeal (K := K) E c₁ c₂)
    (isotropicPluckerIdeal_isHomogeneous (canonicalForms (K := K) (n := n) c₁ c₂))
    (filtrationIdeal_isHomogeneous E c₁ c₂) (originalIdeal_le_filtrationIdeal E c₁ c₂) x
  refine hr.trans ?_
  rw [filtrationIdeal, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨_, hE⟩ I hI
    exact hE ⟨I, hI, rfl⟩
  · intro hE
    constructor
    · intro f hf
      change Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) f ∈
        x.asHomogeneousIdeal.toIdeal
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hf).symm ▸ Ideal.zero_mem _
    · rintro _ ⟨I, hI, rfl⟩
      exact hE I hI

/-- The actual pivot basic open in a homogeneous filtration stage. -/
def filtrationChart (E : Set (PluckerIndex (t+2) n)) (p : PluckerIndex (t+2) n)
    (c₁ c₂ : ℕ) : (filtrationScheme (K := K) E c₁ c₂).Opens :=
  Proj.basicOpen
    (HomogeneousQuotientProjective.grading (filtrationIdeal E c₁ c₂)
      (filtrationIdeal_isHomogeneous E c₁ c₂))
    (Ideal.Quotient.mk (filtrationIdeal E c₁ c₂) (X p))

/-- The stratum is an actual locally closed subscheme of the original
common-isotropic scheme, with its original full quotient structure. -/
def filtrationChartToOriginal (E : Set (PluckerIndex (t+2) n))
    (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ) :
    (filtrationChart (K := K) E p c₁ c₂).toScheme ⟶
      Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂)) :=
  (filtrationChart E p c₁ c₂).ι ≫ filtrationToOriginal E c₁ c₂

/-- The affine chart of the actual homogeneous filtration has precisely
the original full echelon coordinate ring. -/
def filtrationChartIsoCell (E : Set (PluckerIndex (t+2) n))
    (p : PluckerIndex (t+2) n) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (filtrationChart (K := K) E p c₁ c₂).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
        isotropyIdeal (indexEmbedding p) c₁ c₂)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
    (filtrationIdeal E c₁ c₂) (filtrationIdeal_isHomogeneous E c₁ c₂) p ≪≫
      Scheme.Spec.mapIso (normalizedFiltrationCellEquiv p E hE c₁ c₂).symm.toRingEquiv.toCommRingCatIso.op

/-- Each permitted stratum is an actual affine space. Its coordinate set
is finite because it is a subset of the original finite matrix entries. -/
def filtrationChartIsoAffine {k : ℕ} (E : Set (PluckerIndex (t+2) (2*k+1)))
    (p : PluckerIndex (t+2) (2*k+1)) (hE : EarlierSet p E)
    (hp : IndependentPivots (indexEmbedding p)) :
    (filtrationChart (K := K) E p (2*k+1) (2*k)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {i : Coordinate (indexEmbedding p) //
        i ∉ Set.range (pivotEmbedding hp)} K)) :=
  filtrationChartIsoCell E p hE (2*k+1) (2*k) ≪≫
    Scheme.Spec.mapIso (attractingCoordinateRingEquiv hp).symm.toRingEquiv.toCommRingCatIso.op

/-- A forbidden pivot gives the empty actual stratum. -/
theorem filtrationChart_isEmpty_of_not_independent {k : ℕ}
    (E : Set (PluckerIndex (t+2) (2*k+1))) (p : PluckerIndex (t+2) (2*k+1))
    (hE : EarlierSet p E) (hp : ¬ IndependentPivots (indexEmbedding p)) :
    IsEmpty (filtrationChart (K := K) E p (2*k+1) (2*k)).toScheme := by
  have htop := isotropyIdeal_eq_top_of_not_independent (R := K) hp
  let e := filtrationChartIsoCell (K := K) E p hE (2*k+1) (2*k)
  have hsub : Subsingleton (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
      isotropyIdeal (indexEmbedding p) (2*k+1) (2*k)) := by
    rw [htop]
    infer_instance
  letI := hsub
  letI : IsEmpty (Spec (CommRingCat.of (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
      isotropyIdeal (indexEmbedding p) (2*k+1) (2*k)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  exact Function.isEmpty e.hom

/-- Every finite stage is a genuine closed subset of the same original
projective scheme. -/
theorem isClosed_filtration_image (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    IsClosed (Set.range (filtrationToOriginal (K := K) E c₁ c₂)) :=
  (IsClosedImmersion.isClosedEmbedding (filtrationToOriginal E c₁ c₂)).isClosed_range

/-- The zero-th stage is the whole original projective scheme. -/
theorem filtration_image_zero (c₁ c₂ : ℕ) :
    Set.range (filtrationToOriginal (K := K) (pivotPrefix (t+2) n 0) c₁ c₂) = Set.univ := by
  ext x
  simp only [filtrationToOriginal_range, pivotPrefix_zero, Set.mem_empty_iff_false,
    IsEmpty.forall_iff, implies_true, Set.mem_univ]

/-- The actual affine stratum at a position in the finite weight order. -/
def orderedFiltrationCell (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) : Scheme :=
  (filtrationChart (K := K) (pivotPrefix (t+2) n i.val)
    (weightOrderedPivots (t+2) n i) c₁ c₂).toScheme

/-- Uniform affine-space description for every nonempty cell, including
the zero-dimensional cell whose polynomial coordinate type is empty. -/
def orderedFiltrationCellIsoAffine {k : ℕ}
    (i : Fin (pivotCount (t+2) (2*k+1)))
    (hp : IndependentPivots (indexEmbedding (weightOrderedPivots (t+2) (2*k+1) i))) :
    orderedFiltrationCell (K := K) i (2*k+1) (2*k) ≅
      Spec (CommRingCat.of (MvPolynomial {v : Coordinate
        (indexEmbedding (weightOrderedPivots (t+2) (2*k+1) i)) //
          v ∉ Set.range (pivotEmbedding hp)} K)) :=
  filtrationChartIsoAffine _ _ (pivotPrefix_earlier (t+2) (2*k+1) i) hp


/-- The underlying image of the actual basic-open stratum adds exactly
nonvanishing of its pivot coordinate to the closed-stage conditions. -/
theorem filtrationChartToOriginal_range
    (E : Set (PluckerIndex (t+2) n)) (p : PluckerIndex (t+2) n) (c₁ c₂ : ℕ)
    (x : Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))) :
    x ∈ Set.range (filtrationChartToOriginal E p c₁ c₂) ↔
      x ∈ Set.range (filtrationToOriginal E c₁ c₂) ∧
      Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (X p)
        ∉ x.asHomogeneousIdeal.toIdeal := by
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · exact ⟨y.val, rfl⟩
    · exact y.property
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The next stage adds precisely the next pivot coordinate. -/
theorem ordered_filtration_successor_mem
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ)
    (x : Proj (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))) :
    x ∈ Set.range (filtrationToOriginal (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) ↔
      x ∈ Set.range (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂) ∧
      Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂))
        (X (weightOrderedPivots (t+2) n i)) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [filtrationToOriginal_range, filtrationToOriginal_range,
    pivotPrefix_successor]
  constructor
  · intro h
    exact ⟨fun I hI => h I (Set.mem_insert_of_mem _ hI), h _ (Set.mem_insert _ _)⟩
  · rintro ⟨h, hp⟩ I hI
    rcases Set.mem_insert_iff.mp hI with rfl | hI
    · exact hp
    · exact h I hI

/-- Every displayed affine cell is exactly one difference of successive
actual closed-stage images. -/
theorem ordered_filtration_stratum
    (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    Set.range (filtrationChartToOriginal (K := K)
      (pivotPrefix (t+2) n i.val) (weightOrderedPivots (t+2) n i) c₁ c₂) =
      Set.range (filtrationToOriginal (pivotPrefix (t+2) n i.val) c₁ c₂) \
        Set.range (filtrationToOriginal (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) := by
  ext x
  rw [filtrationChartToOriginal_range, Set.mem_sdiff, ordered_filtration_successor_mem]
  tauto

/-- The closed-stage images form a finite decreasing filtration. -/
theorem ordered_filtration_antitone (c₁ c₂ : ℕ) :
    Antitone (fun m => Set.range
      (filtrationToOriginal (K := K) (pivotPrefix (t+2) n m) c₁ c₂)) := by
  intro a b hab x hx
  rw [filtrationToOriginal_range] at hx ⊢
  intro I hI
  exact hx I (pivotPrefix_mono (t+2) n hab hI)

/-- After the last Plücker coordinate vanishes, no projective point
remains. The proof uses the original actual basic-open cover. -/
theorem filtration_image_final (c₁ c₂ : ℕ) :
    Set.range (filtrationToOriginal (K := K)
      (pivotPrefix (t+2) n (pivotCount (t+2) n)) c₁ c₂) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [filtrationToOriginal_range, pivotPrefix_all] at hx
  have hcover := isotropicProjBasicOpen_cover (t := t) (canonicalForms (K := K) (n := n) c₁ c₂)
  have hm : x ∈ (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) (canonicalForms (K := K) (n := n) c₁ c₂))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (canonicalForms (K := K) (n := n) c₁ c₂)) (X p))) := by
    rw [hcover]
    trivial
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  exact hp (hx p (Set.mem_univ _))

end PaperVerification.IsotropicAttractingCharts
