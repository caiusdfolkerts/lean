module

public import Continuation.Runtime.AmpleDegreeOneFoundations

/-!
# Descending a section embedding from a positive power

The affine map of a pure-power chart factors through the degree-one ratio
chart. The factor is an actual morphism between affine schemes, so the
closed-immersion cancellation theorem applies. This avoids assuming a
Veronese theorem or identifying normal generation with very ampleness.

All morphisms below are the recovered actual glued section morphisms.
The construction uses the original section morphism throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u
namespace PaperVerification.ToricSchemes.RationalCartierCocycle
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped Classical BaseSections
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)
  {ι κ : Type u} (s : ι → Γ(C.sheaf, ⊤))

/-- The affine part of the genuine section chart. -/
def sectionAffineChart (i : ι) :
    (C.nonvanishingOpen (s i)).toScheme ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X i))) :=
  (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))

/-- The projective chart factors through its affine chart. Associativity
is proved explicitly, so no scheme composition is unfolded to guess it. -/
theorem sectionProjectiveChart_eq_affine (i : ι) :
    C.sectionProjectiveChart k s i = C.sectionAffineChart k s i ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide) := by
  dsimp only [sectionProjectiveChart, sectionAffineChart,
    sectionProjectiveChartCoordinates]
  exact (Category.assoc _ _ _).symm

/-- Restricting an actual closed section embedding to a standard target
chart gives a closed affine chart map. -/
theorem sectionAffineChart_isClosedImmersion
    (hcover : (⨆ i, C.nonvanishingOpen (s i)) = ⊤)
    [IsClosedImmersion (C.sectionProjectiveMap k s hcover)] (i : ι) :
    IsClosedImmersion (C.sectionAffineChart k s i) := by
  let f := C.sectionProjectiveMap k s hcover
  let U := C.nonvanishingOpen (s i)
  let V := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
  have hUV : f ⁻¹ᵁ V = U := C.sectionProjectiveMap_preimage k s hcover i
  let e := X.isoOfEq hUV.symm
  let a := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.X i) (polynomialVariable_mem_degreeOne k i) (by decide)
  let q := e.hom ≫ (f ∣_ V) ≫ a.hom
  letI : IsClosedImmersion (f ∣_ V) := by
    dsimp only [f]
    infer_instance
  letI : IsClosedImmersion q := by dsimp only [q]; infer_instance
  have hq : q ≫ Proj.awayι (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i) (polynomialVariable_mem_degreeOne k i) (by decide) =
        U.ι ≫ f := by
    change (e.hom ≫ (f ∣_ V) ≫ a.hom) ≫ (a.inv ≫ V.ι) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
    exact Scheme.isoOfEq_hom_ι_assoc X hUV.symm f
  have heq : q = C.sectionAffineChart k s i := by
    apply (cancel_mono (Proj.awayι (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i) (polynomialVariable_mem_degreeOne k i) (by decide))).mp
    exact hq.trans ((C.sectionProjectiveMap_chart k s hcover i).trans
      (C.sectionProjectiveChart_eq_affine k s i))
  exact heq ▸ (inferInstance : IsClosedImmersion q)

/-- Polynomials in the degree-one coordinate ratios lift to the actual
degree-zero homogeneous localization of their projective chart. -/
def polynomialChartLift (i : ι) :
    MvPolynomial ι k →+* HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom (C.sectionProjectiveChartConstant k s i)
    (fun j => HomogeneousLocalization.Away.isLocalizationElem
      (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j))

@[simp] theorem polynomialChartLift_self (i : ι) :
    C.polynomialChartLift k s i (MvPolynomial.X i) = 1 := by
  rw [polynomialChartLift, MvPolynomial.eval₂Hom_X']
  apply HomogeneousLocalization.val_injective
    (𝒜 := MvPolynomial.homogeneousSubmodule ι k)
    (Submonoid.powers (MvPolynomial.X i))
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, pow_one, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨MvPolynomial.X i, 1, pow_one _⟩ :
      Submonoid.powers (MvPolynomial.X i : MvPolynomial ι k))

theorem polynomialChartLift_coordinates (i : ι) :
    (C.sectionProjectiveChartCoordinates k s i).comp
      (C.polynomialChartLift k s i) = C.sectionProjectiveChartRingMap k s i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, polynomialChartLift, MvPolynomial.eval₂Hom_C,
      C.sectionProjectiveChartCoordinates_constant k s i a,
      sectionProjectiveChartRingMap]
  · intro j
    simp only [RingHom.comp_apply, polynomialChartLift, MvPolynomial.eval₂Hom_X',
      C.sectionProjectiveChartCoordinates_variable k s i j,
      C.sectionProjectiveChartRingMap_X k s i j]

variable (N : ℕ) (p : κ → MvPolynomial ι k) (j : ι) (i : κ)
  (hbase : p i = MvPolynomial.X j ^ N)

/-- The chart substitution sends a high-power coordinate to the polynomial
in the degree-one ratios which represents that section. -/
def powerChartPolynomialMap :
    MvPolynomial κ k →+* HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) :=
  (C.polynomialChartLift k s j).comp (MvPolynomial.eval₂Hom MvPolynomial.C p)

include hbase in
theorem powerChartPolynomialMap_base :
    C.powerChartPolynomialMap k s p j (MvPolynomial.X i) = 1 := by
  rw [powerChartPolynomialMap, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hbase,
    map_pow, C.polynomialChartLift_self k s j, one_pow]

/-- A genuine homomorphism of the two homogeneous affine chart rings. -/
def powerChartMap :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule κ k)
      (MvPolynomial.X i) →+*
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X j) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule κ k)
    (C.powerChartPolynomialMap k s p j) (MvPolynomial.X i)
    ((C.powerChartPolynomialMap_base k s N p j i hbase) ▸ isUnit_one)

variable (t : κ → Γ((C.pow N).sheaf, ⊤))
  (hp : ∀ a, (p a).IsHomogeneous N)
  (hvalue : ∀ a, C.sectionProjectiveFieldMap k s (p a) =
    (C.pow N).toCartierData.sectionValue ⊤ (t a))
  (ht : t i = C.sectionPow N (s j))

include hp hvalue ht in
/-- The chart substitution agrees with both genuine function-field
evaluations. Homogeneity is used in its literal degree N. -/
theorem powerChartMap_functionField
    [Nonempty (C.nonvanishingOpen (s j))]
    [Nonempty ((C.pow N).nonvanishingOpen (t i))] :
    ((X.germToFunctionField (C.nonvanishingOpen (s j))).hom.comp
      (C.sectionProjectiveChartCoordinates k s j)).comp
        (C.powerChartMap k s N p j i hbase) =
    (X.germToFunctionField ((C.pow N).nonvanishingOpen (t i))).hom.comp
      ((C.pow N).sectionProjectiveChartCoordinates k t i) := by
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v : ι → X.functionField := fun a => C.toCartierData.sectionValue ⊤ (s a)
  have hpoly : ((X.germToFunctionField (C.nonvanishingOpen (s j))).hom.comp
      (C.sectionProjectiveChartCoordinates k s j)).comp
        (C.powerChartPolynomialMap k s p j) =
      (X.germToFunctionField ((C.pow N).nonvanishingOpen (t i))).hom.comp
        ((C.pow N).sectionProjectiveChartRingMap k t i) := by
    change ((X.germToFunctionField (C.nonvanishingOpen (s j))).hom.comp
      ((C.sectionProjectiveChartCoordinates k s j).comp
        (C.polynomialChartLift k s j))).comp (MvPolynomial.eval₂Hom MvPolynomial.C p) = _
    rw [C.polynomialChartLift_coordinates k s j,
      C.sectionProjectiveChartRingMap_germ k s j,
      (C.pow N).sectionProjectiveChartRingMap_germ k t i]
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change (p a).eval₂ F (fun b => (v j)⁻¹ * v b) =
        ((C.pow N).toCartierData.sectionValue ⊤ (t i))⁻¹ *
          (C.pow N).toCartierData.sectionValue ⊤ (t a)
      rw [homogeneous_eval_scaled F v (v j)⁻¹ (p a) N (hp a), ht, C.sectionPow_value,
        ← hvalue a, inv_pow]
      rfl
  have heval (F₁ F₂ : MvPolynomial κ k →+* X.functionField)
      (h : F₁ = F₂) (h₁ : IsUnit (F₁ (MvPolynomial.X i)))
      (h₂ : IsUnit (F₂ (MvPolynomial.X i))) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule κ k)
        F₁ (MvPolynomial.X i) h₁ =
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule κ k)
        F₂ (MvPolynomial.X i) h₂ := by
    subst F₂
    rfl
  unfold powerChartMap
  rw [unitHomogeneousAwayEvaluation_map]
  exact (heval _ _ hpoly _ _).trans (unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule κ k)
    ((C.pow N).sectionProjectiveChartRingMap k t i)
    (X.germToFunctionField ((C.pow N).nonvanishingOpen (t i))).hom
    (MvPolynomial.X i) _).symm

include hp hvalue in
/-- The affine factorization is an equality of actual scheme morphisms.
It is proved on the dominant generic point, where the preceding rational
coordinate identity applies. -/
theorem powerChart_factorization (hN : 0 < N) :
    let hU : (C.pow N).nonvanishingOpen (t i) = C.nonvanishingOpen (s j) := by
      rw [ht]
      exact C.nonvanishingOpen_sectionPow N hN (s j)
    (X.isoOfEq hU.symm).hom ≫ (C.pow N).sectionAffineChart k t i =
      C.sectionAffineChart k s j ≫
        Spec.map (CommRingCat.ofHom (C.powerChartMap k s N p j i hbase)) := by
  dsimp only
  let hU : (C.pow N).nonvanishingOpen (t i) = C.nonvanishingOpen (s j) := by
    rw [ht]
    exact C.nonvanishingOpen_sectionPow N hN (s j)
  by_cases hne : Nonempty (C.nonvanishingOpen (s j))
  · letI := hne
    letI : Nonempty ((C.pow N).nonvanishingOpen (t i)) := hU.symm ▸ hne
    have hη := genericPoint_mem_open X (C.nonvanishingOpen (s j))
    have hη' := genericPoint_mem_open X ((C.pow N).nonvanishingOpen (t i))
    let η := (C.nonvanishingOpen (s j)).fromSpecStalkOfMem (genericPoint X) hη
    let η' := ((C.pow N).nonvanishingOpen (t i)).fromSpecStalkOfMem (genericPoint X) hη'
    letI : IsDominant η := genericStalkMapToOpen_isDominant _ hη
    have hηe : η ≫ (X.isoOfEq hU.symm).hom = η' := by
      apply (cancel_mono ((C.pow N).nonvanishingOpen (t i)).ι).mp
      simp only [Category.assoc, Scheme.isoOfEq_hom_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, η, η']
    apply ext_of_isDominant η
    rw [← Category.assoc, hηe]
    dsimp only [η, η']
    simp only [sectionAffineChart, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
    simp only [← Spec.map_comp, Category.assoc]
    congr 1
    exact congrArg CommRingCat.ofHom
      (C.powerChartMap_functionField k s N p j i hbase t hp hvalue ht).symm
  · letI : IsEmpty (C.nonvanishingOpen (s j)) := not_nonempty_iff.mp hne
    exact isInitialOfIsEmpty.hom_ext _ _

include hbase hp hvalue ht in
/-- A pure-power chart of an actual positive-power closed embedding forces
the degree-one affine chart itself to be a closed immersion. -/
theorem sectionAffineChart_isClosedImmersion_of_power (hN : 0 < N)
    (hcover : (⨆ a, (C.pow N).nonvanishingOpen (t a)) = ⊤)
    [IsClosedImmersion ((C.pow N).sectionProjectiveMap k t hcover)] :
    IsClosedImmersion (C.sectionAffineChart k s j) := by
  let hU : (C.pow N).nonvanishingOpen (t i) = C.nonvanishingOpen (s j) := by
    rw [ht]
    exact C.nonvanishingOpen_sectionPow N hN (s j)
  letI := (C.pow N).sectionAffineChart_isClosedImmersion k t hcover i
  letI : IsClosedImmersion ((X.isoOfEq hU.symm).hom ≫
      (C.pow N).sectionAffineChart k t i) := inferInstance
  have he := C.powerChart_factorization k s N p j i hbase t hp hvalue ht hN
  letI : IsClosedImmersion (C.sectionAffineChart k s j ≫
      Spec.map (CommRingCat.ofHom (C.powerChartMap k s N p j i hbase))) := he ▸ inferInstance
  exact IsClosedImmersion.of_comp (C.sectionAffineChart k s j)
    (Spec.map (CommRingCat.ofHom (C.powerChartMap k s N p j i hbase)))

/-- Gluing the actual closed affine ratio charts gives a preimmersion;
properness over the base field makes the image closed. -/
theorem sectionProjectiveMap_isClosedImmersion_of_affineCharts
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i, C.nonvanishingOpen (s i)) = ⊤)
    (hcharts : ∀ i, IsClosedImmersion (C.sectionAffineChart k s i)) :
    IsClosedImmersion (C.sectionProjectiveMap k s hcover) := by
  let f := C.sectionProjectiveMap k s hcover
  let U (i : ι) := C.nonvanishingOpen (s i)
  let V (i : ι) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.X i)
  have hlocal (i : ι) : IsPreimmersion ((U i).ι ≫ f) := by
    change IsPreimmersion ((C.nonvanishingOpen (s i)).ι ≫
      C.sectionProjectiveMap k s hcover)
    rw [C.sectionProjectiveMap_chart k s hcover i,
      C.sectionProjectiveChart_eq_affine k s i]
    letI := hcharts i
    infer_instance
  letI : SurjectiveOnStalks f :=
    IsZariskiLocalAtSource.of_iSup_eq_top U hcover (fun i => by
      letI := hlocal i
      infer_instance)
  letI : IsPreimmersion f := by
    refine { isEmbedding := ?_ }
    apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
      (V := fun i => (U i).toScheme) (iV := fun i => (U i).ι)
    · rintro y ⟨x, rfl⟩
      have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
      apply Opens.mem_iSup.mpr
      refine ⟨i, ?_⟩
      change x ∈ C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
      rw [C.sectionProjectiveMap_preimage k s hcover i]
      exact hxi
    · exact fun i => (U i).ι.continuous
    · intro i x hx
      have hxi : x ∈ U i := by
        change x ∈ C.nonvanishingOpen (s i)
        rw [← C.sectionProjectiveMap_preimage k s hcover i]
        exact hx
      exact ⟨⟨x, hxi⟩, rfl⟩
    · intro i
      letI := hlocal i
      exact ((U i).ι ≫ f).isEmbedding
  letI : IsProper f := C.sectionProjectiveMap_isProper k s hcover
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

/-- Actual affine chart generators for an embedding section system.
Every field is geometric or algebraic data; existence will be proved from
the ordinary ampleness criterion. -/
structure SectionEmbeddingData where
  index : Type u
  finiteIndex : Fintype index
  sections : index → Γ(C.sheaf, ⊤)
  chartIndex : Type u
  chooseChart : chartIndex → index
  cover : (⨆ i, C.nonvanishingOpen (sections i)) = ⊤
  chosenCover : (⨆ i, C.nonvanishingOpen (sections (chooseChart i))) = ⊤
  affine : ∀ i, IsAffineOpen (C.nonvanishingOpen (sections (chooseChart i)))
  generators : ∀ i, Function.Surjective
    (C.sectionProjectiveChartCoordinates k sections (chooseChart i))

/-- The recovered finite-power embedding construction is used with its
exact affine coordinate generators; iterated powers are flattened by the
proved equality of actual Cartier cocycles. -/
theorem exists_power_sectionEmbeddingData
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hC : Unimodular.NefBig.IsAmpleModule C.sheaf) :
    ∃ N : ℕ, 0 < N ∧ Nonempty ((C.pow N).SectionEmbeddingData k) := by
  have h := Unimodular.NefBig.isAmple_cocycle_of_isAmpleModule C hC
  letI : CompactSpace X := h.1
  obtain ⟨a, ha, I, hI, r, hnonempty, haff, hcover⟩ :=
    h.exists_common_power_nonempty_affine_cover
  letI : Fintype I := hI
  obtain ⟨b, hb, J, hJ, t, chooseChart, _, hall, hchosen, haff', hgen⟩ :=
    (C.pow a).exists_power_chart_generators k r hnonempty haff hcover
  refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [← C.pow_pow_eq a b]
  exact ⟨{
    index := J
    finiteIndex := hJ
    sections := t
    chartIndex := I
    chooseChart := chooseChart
    cover := hall
    chosenCover := hchosen
    affine := haff'
    generators := hgen
  }⟩

/-- Ordinary ampleness together with proved homogeneous generation gives
an actual closed immersion by the original degree-one section family.
The proof augments one genuine power embedding with the pure powers of
these sections, then descends chart by chart through an affine factor. -/
theorem degreeOneSectionMorphism_isClosedImmersion
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hC : Unimodular.NefBig.IsAmpleModule C.sheaf)
    (hgen : ∀ (N : ℕ) (t : Γ((C.pow N).sheaf, ⊤)),
      ∃ p : MvPolynomial ι k, p.IsHomogeneous N ∧
        C.sectionProjectiveFieldMap k s p =
          (C.pow N).toCartierData.sectionValue ⊤ t) :
    IsClosedImmersion (C.degreeOneSectionMorphism k s hC hgen) := by
  obtain ⟨N, hN, ⟨A⟩⟩ := C.exists_power_sectionEmbeddingData k hC
  letI : Fintype A.index := A.finiteIndex
  let q : ι ⊕ A.index → Γ((C.pow N).sheaf, ⊤) :=
    Sum.elim (fun j => C.sectionPow N (s j)) A.sections
  let c (a : A.index) : (ι ⊕ A.index) →₀ k := Finsupp.single (Sum.inr a) 1
  have hc (a : A.index) : Finsupp.linearCombination k q (c a) = A.sections a := by
    simp [c, q]
  have hqcover : (⨆ a, (C.pow N).nonvanishingOpen (q a)) = ⊤ := by
    apply top_unique
    rw [← A.cover]
    exact iSup_le fun a => le_iSup_of_le (Sum.inr a) le_rfl
  letI : IsClosedImmersion ((C.pow N).sectionProjectiveMap k q hqcover) :=
    (C.pow N).sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
      k A.sections q c hc hqcover A.chooseChart A.chosenCover A.affine A.generators
  choose r hr hvalue using fun a => hgen N (A.sections a)
  let p : ι ⊕ A.index → MvPolynomial ι k :=
    Sum.elim (fun j => MvPolynomial.X j ^ N) r
  have hp (a : ι ⊕ A.index) : (p a).IsHomogeneous N := by
    cases a with
    | inl j => exact MvPolynomial.isHomogeneous_X_pow j N
    | inr a => exact hr a
  have hv (a : ι ⊕ A.index) : C.sectionProjectiveFieldMap k s (p a) =
      (C.pow N).toCartierData.sectionValue ⊤ (q a) := by
    cases a with
    | inl j =>
        simp only [p, q, Sum.elim_inl, map_pow, sectionProjectiveFieldMap,
          MvPolynomial.eval₂Hom_X', C.sectionPow_value]
    | inr a => exact hvalue a
  apply C.sectionProjectiveMap_isClosedImmersion_of_affineCharts k s
    (C.nonvanishing_cover_of_homogeneous_generation k s hC hgen)
  intro j
  exact C.sectionAffineChart_isClosedImmersion_of_power k s N p j (Sum.inl j)
    rfl q hp hv rfl hN hqcover

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionAffineChart_isClosedImmersion
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.powerChartMap_functionField
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.powerChart_factorization
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionAffineChart_isClosedImmersion_of_power
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.degreeOneSectionMorphism_isClosedImmersion

end
