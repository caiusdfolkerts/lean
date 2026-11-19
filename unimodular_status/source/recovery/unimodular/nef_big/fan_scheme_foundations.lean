module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part11
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation
public import TauCeti.Topology.KrullDimension.Basic

@[expose] public section

/-! Actual smoothness, dimension and separatedness of fan schemes.
Source assembly only; native verification remains a separate gate. -/

section
-- BEGIN Recovery.Unimodular.NefBig.FanSchemeSmooth


/-!
# Smoothness and dimension of the actual scheme of a smooth complete fan

For each full cone, the integral dual basis identifies its actual chart
subalgebra with a polynomial algebra in exactly `n` variables. The Laurent
factor in the general smooth-chart equivalence has an empty coordinate set
and therefore equals the coefficient field. The previously proved purity
theorem supplies a cover of the glued scheme by these full-cone charts.

The conclusions are Mathlib's scheme-theoretic `SmoothOfRelativeDimension`
and `Smooth` predicates for the specified structure morphism, and the
topological Krull dimension of the actual scheme. Smoothness, purity, and
dimension are not hypotheses. Every field and every natural dimension,
including zero, are covered.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- Every full chart has precisely the ordinary polynomial coordinate
algebra in `n` variables, over the original coefficient field. -/
def fullChartPolynomialEquiv (s : F.fullCones) :
    monoidChartAlgebra k (dualConeMonoid s.val) ≃ₐ[k]
      MvPolynomial (Fin n) k := by
  classical
  let I : Finset (Fin n) := Finset.univ
  letI : IsEmpty (FreeCoordinate I) :=
    ⟨fun i => i.property (Finset.mem_univ i.val)⟩
  letI : Subsingleton (FreeCoordinate I → ℤ) :=
    ⟨fun _ _ => funext fun i => isEmptyElim i⟩
  let coefficientEquiv : AddMonoidAlgebra k (FreeCoordinate I → ℤ) ≃ₐ[k] k :=
    AddMonoidAlgebra.uniqueAlgEquiv k (FreeCoordinate I → ℤ)
  let indexEquiv : I ≃ Fin n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have hcone : dualConeMonoid s.val =
      coordinateConeMonoid (integralDualBasis (F.fullConeBasis s)) I := by
    rw [F.fullConeBasis_ray_set s, dualConeMonoid_basis_eq]
  exact (Subalgebra.equivOfEq _ _ (congrArg (monoidChartAlgebra k) hcone)).trans
    ((smoothChartAlgebraEquiv k (integralDualBasis (F.fullConeBasis s)) I).trans
      ((MvPolynomial.mapAlgEquiv I coefficientEquiv).trans
        (MvPolynomial.renameEquiv k indexEquiv)))

/-- Full cones exist even in dimension zero. This is a consequence of
completeness and the derived purity theorem. -/
theorem fullCones_nonempty : Nonempty F.fullCones := by
  classical
  obtain ⟨s, hs, _⟩ := F.complete 0
  obtain ⟨t, ht, _, hcard⟩ := F.isPure s hs
  exact ⟨⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩⟩

/-- The actual full-cone affine charts form an open cover of the fan scheme. -/
def fullFanSchemeOpenCover : (F.fanScheme k).OpenCover where
  I₀ := F.fullCones
  X s := coneChart k s.val
  f s := F.fanChartMap k (F.fullConeIndex s)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨F.fullChartOpen_cover k F.isPure, fun _ => inferInstance⟩

/-- The specified base-field map on each full chart is standard smooth of
relative dimension `n`; the assertion concerns the actual chart algebra. -/
theorem fullChart_isStandardSmoothOfRelativeDimension (s : F.fullCones) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val))) := by
  let e := fullChartPolynomialEquiv F k s
  have hp : RingHom.IsStandardSmoothOfRelativeDimension n
      (algebraMap k (MvPolynomial (Fin n) k)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
  have hcomp : e.symm.toRingEquiv.toRingHom.comp
      (algebraMap k (MvPolynomial (Fin n) k)) =
      algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) := by
    exact RingHom.ext (fun c => e.symm.commutes c)
  rw [← hcomp]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left
    (algebraMap k (MvPolynomial (Fin n) k)) e.symm.toRingEquiv hp

/-- Each full affine chart is smooth of relative dimension `n` over the
original field, using its existing specified structure morphism. -/
theorem fullChart_smoothOfRelativeDimension (s : F.fullCones) :
    SmoothOfRelativeDimension n
      (coneChart k s.val ↘ Spec (CommRingCat.of k)) := by
  change SmoothOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom
      (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)))))
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
  exact RingHom.locally_of
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)) _
    (fullChart_isStandardSmoothOfRelativeDimension F k s)

/-- The actual glued smooth complete fan scheme is smooth of relative
dimension `n` over every field. No smoothness assumption is added. -/
theorem fanScheme_smoothOfRelativeDimension :
    SmoothOfRelativeDimension n
      (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SmoothOfRelativeDimension n) (fullFanSchemeOpenCover F k)
  intro s
  change SmoothOfRelativeDimension n
    (F.fanChartMap k (F.fullConeIndex s) ≫
      (F.fanScheme k ↘ Spec (CommRingCat.of k)))
  rw [comp_over (F.fanChartMap k (F.fullConeIndex s)) (Spec (CommRingCat.of k))]
  exact fullChart_smoothOfRelativeDimension F k s

/-- In particular the original structure morphism is smooth. -/
theorem fanScheme_smooth : Smooth
    (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  let := fanScheme_smoothOfRelativeDimension F k
  exact SmoothOfRelativeDimension.smooth n _

/-- The actual scheme is quasi-compact, since the full-cone affine cover
has finitely many members. -/
theorem fanScheme_compactSpace : CompactSpace (F.fanScheme k) := by
  let : ∀ s : (fullFanSchemeOpenCover F k).I₀,
      CompactSpace ((fullFanSchemeOpenCover F k).X s) := by
    change ∀ s : F.fullCones, CompactSpace (coneChart k s.val)
    intro s
    change CompactSpace (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val)))
    infer_instance
  let : Finite (fullFanSchemeOpenCover F k).I₀ := by
    change Finite F.fullCones
    infer_instance
  exact (fullFanSchemeOpenCover F k).compactSpace

/-- The specified structure morphism is quasi-compact. -/
theorem fanScheme_quasiCompact :
    QuasiCompact (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  let := fanScheme_compactSpace F k
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

/-- In Mathlib's standard predicates, the actual fan scheme is of finite
type over the original field: its structure morphism is locally of finite
type and quasi-compact. -/
theorem fanScheme_finiteType :
    LocallyOfFiniteType (F.fanScheme k ↘ Spec (CommRingCat.of k)) ∧
      QuasiCompact (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  let := fanScheme_smooth F k
  exact ⟨inferInstance, fanScheme_quasiCompact F k⟩

/-- The absolute Krull dimension of each actual full affine chart is `n`. -/
theorem fullChart_topologicalKrullDim (s : F.fullCones) :
    topologicalKrullDim (coneChart k s.val) = n := by
  change topologicalKrullDim
    (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val))) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (fullChartPolynomialEquiv F k s).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp

/-- The actual fan scheme has absolute topological Krull dimension `n`.
The result includes dimension zero and does not assume any dimension bound. -/
theorem fanScheme_topologicalKrullDim :
    topologicalKrullDim (F.fanScheme k) = n := by
  let := fullCones_nonempty F
  calc
    topologicalKrullDim (F.fanScheme k) =
        ⨆ s : F.fullCones, topologicalKrullDim (coneChart k s.val) :=
      TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding
        (fun s : F.fullCones =>
          (F.fanChartMap k (F.fullConeIndex s) : coneChart k s.val → F.fanScheme k))
        (fun s => (F.fanChartMap k (F.fullConeIndex s)).isOpenEmbedding)
        (F.fullChartOpen_cover k F.isPure)
    _ = n := by simp only [fullChart_topologicalKrullDim, iSup_const]

#print axioms fullChartPolynomialEquiv
#print axioms fullCones_nonempty
#print axioms fullFanSchemeOpenCover
#print axioms fullChart_isStandardSmoothOfRelativeDimension
#print axioms fullChart_smoothOfRelativeDimension
#print axioms fanScheme_smoothOfRelativeDimension
#print axioms fanScheme_smooth
#print axioms fanScheme_compactSpace
#print axioms fanScheme_quasiCompact
#print axioms fanScheme_finiteType
#print axioms fullChart_topologicalKrullDim
#print axioms fanScheme_topologicalKrullDim

end Unimodular.NefBig

#check Unimodular.NefBig.fanScheme_topologicalKrullDim
end
-- END Recovery.Unimodular.NefBig.FanSchemeSmooth
end

section
-- BEGIN Recovery.Unimodular.NefBig.FanSchemeSeparated


/-!
# Separatedness of the actual fan scheme

The genuine common-face chart embeds as a closed subscheme of the product
of the two affine charts. The ring map is the ordinary tensor-product map
induced by their literal inclusions in the common-face algebra. Its
surjectivity follows from the integral separation lemma: every character
nonnegative on the common face is a sum of characters nonnegative on the
two cones. This proves Mathlib's actual scheme-theoretic separatedness.

This source does not assert properness. In particular, finite affine covers
or topological quasi-compactness are not used as substitutes for properness.
The file remains a source candidate until its separate Lean audit passes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped BigOperators TensorProduct

variable {n : ℕ}

/-- The coordinate lattice is the genuine integral lattice in its real span. -/
def dictionaryIntegralLattice :
    TauCeti.Toric.IsIntegralLattice (PaperVerification.ToricGeometry.embed n) := by
  change TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).compLeft (Fin n))
  exact TauCeti.Toric.isIntegralLattice_intCast n

/-- All integral additive characters are represented by the coordinate
dot product; no finite-index character sublattice is substituted. -/
def coordinateCharacterEquiv :
    Lattice n ≃ₗ[ℤ] (Lattice n →+ ℤ) :=
  (dotProductEquiv ℤ (Fin n)).trans (addMonoidHomLequivInt ℤ).symm

@[simp] theorem coordinateCharacterEquiv_apply (m v : Lattice n) :
    coordinateCharacterEquiv m v = integerPairing v m := by
  change dotProduct m v = ∑ i, v i * m i
  simp only [dotProduct, mul_comm]

/-- The dictionary's concrete nonnegative span is the library's ordinary
conic hull of the same embedded lattice vectors. -/
theorem latticeRayCone_eq_integralHull (s : Finset (Lattice n)) :
    latticeRayCone s = PointedCone.hull ℝ
      (PaperVerification.ToricGeometry.embed n '' (s : Set (Lattice n))) := by
  simp only [latticeRayCone, finiteRayCone_eq_hull, Finset.coe_image]

theorem coordinateCharacter_mem_dualSemigroup (s : Finset (Lattice n)) (m : Lattice n) :
    coordinateCharacterEquiv m ∈
        TauCeti.Toric.dualSemigroup dictionaryIntegralLattice (latticeRayCone s) ↔
      m ∈ dualConeMonoid s := by
  rw [latticeRayCone_eq_integralHull,
    TauCeti.Toric.mem_dualSemigroup_hull_image]
  simp only [coordinateCharacterEquiv_apply]
  rfl

variable (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

/-- Every actual integral character on a common-face chart splits as a
sum of characters from the two neighboring charts. -/
theorem dualConeMonoid_inter_decomposition
    (s t : Finset (Lattice n)) (hs : s ∈ F.cones) (ht : t ∈ F.cones)
    (m : Lattice n) (hm : m ∈ dualConeMonoid (s ∩ t)) :
    ∃ a ∈ dualConeMonoid s, ∃ b ∈ dualConeMonoid t, a + b = m := by
  classical
  have hrat (v : Finset (Lattice n)) :
      TauCeti.Toric.IsLatticeRational (PaperVerification.ToricGeometry.embed n)
        (latticeRayCone v) :=
    TauCeti.Toric.isLatticeRational_iff.mpr ⟨v, latticeRayCone_eq_integralHull v⟩
  have hface_s : (latticeRayCone s ⊓ latticeRayCone t).IsFaceOf
      (latticeRayCone s) := by
    rw [F.intersection s hs t ht]
    exact F.cone_subset_isFaceOf hs Finset.inter_subset_left
  have hface_t : (latticeRayCone s ⊓ latticeRayCone t).IsFaceOf
      (latticeRayCone t) := by
    rw [F.intersection s hs t ht]
    exact F.cone_subset_isFaceOf ht Finset.inter_subset_right
  have hsum := TauCeti.Toric.dualSemigroup_inf_eq_sup
    dictionaryIntegralLattice (hrat s) (hrat t) hface_s hface_t
  rw [F.intersection s hs t ht] at hsum
  have hchar := (coordinateCharacter_mem_dualSemigroup (s ∩ t) m).mpr hm
  rw [hsum] at hchar
  obtain ⟨a, ha, b, hb, hab⟩ := AddSubmonoid.mem_sup.mp hchar
  refine ⟨coordinateCharacterEquiv.symm a, ?_, coordinateCharacterEquiv.symm b, ?_, ?_⟩
  · exact (coordinateCharacter_mem_dualSemigroup s _).mp (by simpa using ha)
  · exact (coordinateCharacter_mem_dualSemigroup t _).mp (by simpa using hb)
  · apply coordinateCharacterEquiv.injective
    simpa only [map_add, LinearEquiv.apply_symm_apply] using hab

/-- The equality is in the full character lattice, not merely after
extension of scalars or saturation. -/
theorem dualConeMonoid_inter_eq_sup
    (s t : Finset (Lattice n)) (hs : s ∈ F.cones) (ht : t ∈ F.cones) :
    dualConeMonoid (s ∩ t) = dualConeMonoid s ⊔ dualConeMonoid t := by
  apply le_antisymm
  · intro m hm
    exact AddSubmonoid.mem_sup.mpr (dualConeMonoid_inter_decomposition F s t hs ht m hm)
  · exact sup_le (dualConeMonoid_antitone Finset.inter_subset_left)
      (dualConeMonoid_antitone Finset.inter_subset_right)

section ChartAlgebras

variable (k : Type u) [CommRing k] {G : Type} [AddCommGroup G]
  {S T U : AddSubmonoid G}

/-- The actual ring map from the product of two affine charts to their
common-face coordinate algebra. -/
def monoidChartProductMap (hSU : S ≤ U) (hTU : T ≤ U) :
    monoidChartAlgebra k S ⊗[k] monoidChartAlgebra k T →ₐ[k]
      monoidChartAlgebra k U :=
  Algebra.TensorProduct.productMap (monoidChartInclusion k hSU)
    (monoidChartInclusion k hTU)

theorem monoidChartProductMap_surjective (hSU : S ≤ U) (hTU : T ≤ U)
    (hdecomp : ∀ m ∈ U, ∃ a ∈ S, ∃ b ∈ T, a + b = m) :
    Function.Surjective (monoidChartProductMap k hSU hTU) := by
  classical
  let e := monoidChartAlgebraEquiv k U
  have hpre : ∀ f : AddMonoidAlgebra k U,
      ∃ x, monoidChartProductMap k hSU hTU x = e f := by
    intro f
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add f g hf hg =>
        obtain ⟨x, hx⟩ := hf
        obtain ⟨y, hy⟩ := hg
        exact ⟨x + y, by simp only [map_add, hx, hy]⟩
    | single m c =>
        obtain ⟨a, ha, b, hb, hab⟩ := hdecomp m.val m.property
        refine ⟨(c • chartCharacter k S a ha) ⊗ₜ[k] chartCharacter k T b hb, ?_⟩
        apply Subtype.ext
        change (c • AddMonoidAlgebra.single a (1 : k)) *
          AddMonoidAlgebra.single b (1 : k) =
            (monoidChartMap k U) (AddMonoidAlgebra.single m c)
        simp [AddMonoidAlgebra.smul_single, AddMonoidAlgebra.single_mul_single, hab]
  intro y
  obtain ⟨f, rfl⟩ := e.surjective y
  exact hpre f

/-- The literal spectrum map, followed by the standard spectrum/tensor
product isomorphism, has the expected two affine-chart projections. -/
def monoidChartProductSchemeMap (hSU : S ≤ U) (hTU : T ≤ U) :
    monoidChartScheme k U ⟶
      pullback (monoidChartScheme k S ↘ Spec (CommRingCat.of k))
        (monoidChartScheme k T ↘ Spec (CommRingCat.of k)) :=
  Spec.map (CommRingCat.ofHom (monoidChartProductMap k hSU hTU).toRingHom) ≫
    (pullbackSpecIso k (monoidChartAlgebra k S) (monoidChartAlgebra k T)).inv

@[reassoc (attr := simp)]
theorem monoidChartProductSchemeMap_fst (hSU : S ≤ U) (hTU : T ≤ U) :
    monoidChartProductSchemeMap k hSU hTU ≫ pullback.fst _ _ =
      monoidChartSpecMap k hSU := by
  change (Spec.map (CommRingCat.ofHom
      (monoidChartProductMap k hSU hTU).toRingHom) ≫
      (pullbackSpecIso k (monoidChartAlgebra k S) (monoidChartAlgebra k T)).inv) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap k (monoidChartAlgebra k S))))
        (Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k T)))) =
      Spec.map (CommRingCat.ofHom (monoidChartInclusion k hSU).toRingHom)
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change monoidChartProductMap k hSU hTU (x ⊗ₜ[k] 1) = monoidChartInclusion k hSU x
  simp [monoidChartProductMap]

@[reassoc (attr := simp)]
theorem monoidChartProductSchemeMap_snd (hSU : S ≤ U) (hTU : T ≤ U) :
    monoidChartProductSchemeMap k hSU hTU ≫ pullback.snd _ _ =
      monoidChartSpecMap k hTU := by
  change (Spec.map (CommRingCat.ofHom
      (monoidChartProductMap k hSU hTU).toRingHom) ≫
      (pullbackSpecIso k (monoidChartAlgebra k S) (monoidChartAlgebra k T)).inv) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom
        (algebraMap k (monoidChartAlgebra k S))))
        (Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k T)))) =
      Spec.map (CommRingCat.ofHom (monoidChartInclusion k hTU).toRingHom)
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change monoidChartProductMap k hSU hTU (1 ⊗ₜ[k] x) = monoidChartInclusion k hTU x
  simp [monoidChartProductMap]

theorem monoidChartProductSchemeMap_isClosedImmersion (hSU : S ≤ U) (hTU : T ≤ U)
    (hdecomp : ∀ m ∈ U, ∃ a ∈ S, ∃ b ∈ T, a + b = m) :
    IsClosedImmersion (monoidChartProductSchemeMap k hSU hTU) := by
  let f : CommRingCat.of (monoidChartAlgebra k S ⊗[k] monoidChartAlgebra k T) ⟶
      CommRingCat.of (monoidChartAlgebra k U) :=
    CommRingCat.ofHom (monoidChartProductMap k hSU hTU).toRingHom
  have hf : Function.Surjective f := by
    change Function.Surjective (monoidChartProductMap k hSU hTU)
    exact monoidChartProductMap_surjective k hSU hTU hdecomp
  letI : IsClosedImmersion (Spec.map f) := IsClosedImmersion.spec_of_surjective f hf
  change IsClosedImmersion (Spec.map f ≫
    (pullbackSpecIso k (monoidChartAlgebra k S) (monoidChartAlgebra k T)).inv)
  infer_instance

end ChartAlgebras

variable (k : Type u) [CommRing k]

/-- The genuine overlap of two fan charts is closed in their product over
the original base ring. The overlap is identified by the already proved
scheme-theoretic pullback, including its actual morphisms. -/
theorem fanChart_overlap_closed (s t : F.ConeIndex) :
    IsClosedImmersion (pullback.mapDesc (F.fanChartMap k t) (F.fanChartMap k s)
      (F.fanScheme k ↘ Spec (CommRingCat.of k))) := by
  let H := F.fanChart_inter_isPullback k s t
  let E := pullback.congrHom
    (comp_over (F.fanChartMap k t) (Spec (CommRingCat.of k)))
    (comp_over (F.fanChartMap k s) (Spec (CommRingCat.of k)))
  let p := monoidChartProductSchemeMap k
    (dualConeMonoid_antitone (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
    (dualConeMonoid_antitone (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))
  have hp : IsClosedImmersion p := by
    apply monoidChartProductSchemeMap_isClosedImmersion
    intro m hm
    obtain ⟨a, ha, b, hb, hab⟩ :=
      dualConeMonoid_inter_decomposition F s.val t.val s.property t.property m hm
    exact ⟨b, hb, a, ha, (add_comm b a).trans hab⟩
  have heq : H.isoPullback.hom ≫
      pullback.mapDesc (F.fanChartMap k t) (F.fanChartMap k s)
        (F.fanScheme k ↘ Spec (CommRingCat.of k)) ≫ E.hom = p := by
    apply pullback.hom_ext
    · simp [E, p, H, coneChartFaceMap, coneChart] <;>
        exact (monoidChartProductSchemeMap_fst k
          (dualConeMonoid_antitone (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
          (dualConeMonoid_antitone (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))).symm
    · simp [E, p, H, coneChartFaceMap, coneChart] <;>
        exact (monoidChartProductSchemeMap_snd k
          (dualConeMonoid_antitone (Finset.inter_subset_right : s.val ∩ t.val ⊆ t.val))
          (dualConeMonoid_antitone (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val))).symm
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom _).mp
  apply (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ E.hom).mp
  simpa only [Category.assoc, heq] using hp

/-- The actual glued fan scheme is separated over its original base ring.
No projectivity or separatedness hypothesis is imposed on the input fan. -/
theorem fanScheme_isSeparated :
    IsSeparated (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  let : ∀ s : (F.fanSchemeOpenCover k).I₀,
      IsSeparated ((F.fanSchemeOpenCover k).f s ≫
        (F.fanScheme k ↘ Spec (CommRingCat.of k))) := by
    change ∀ s : F.ConeIndex, IsSeparated (F.fanChartMap k s ≫
      (F.fanScheme k ↘ Spec (CommRingCat.of k)))
    intro s
    rw [comp_over]
    change IsSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)))))
    infer_instance
  apply IsSeparated.of_openCover _ (F.fanSchemeOpenCover k)
  intro s t _
  exact fanChart_overlap_closed F k t s

theorem fanScheme_separatedScheme : (F.fanScheme k).IsSeparated := by
  let := fanScheme_isSeparated F k
  exact Scheme.IsSeparated.of_isSeparated (F.fanScheme k ↘ Spec (CommRingCat.of k))

end Unimodular.NefBig

#print axioms Unimodular.NefBig.dualConeMonoid_inter_eq_sup
#print axioms Unimodular.NefBig.fanScheme_isSeparated
#print axioms Unimodular.NefBig.fanScheme_separatedScheme
#check Unimodular.NefBig.fanScheme_separatedScheme
end
-- END Recovery.Unimodular.NefBig.FanSchemeSeparated
end

#check Unimodular.NefBig.fanScheme_isSeparated
