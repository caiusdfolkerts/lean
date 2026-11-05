module

public import PaperVerification.ToricFanCartierCocycle

public import PaperVerification.ToricOrbitCartierCoefficients
public import PaperVerification.ToricDominantCartierPullback
public import PaperVerification.ToricAffinePullbackSections

@[expose] public section

/-!
# Actual restriction of a Cartier sheaf to an orbit closure

The normalized local characters define an actual fractional sheaf on the
quotient-star scheme. The original transition functions are regular on
their overlaps and are pulled through the actual affine quotient maps.
The independent local-frame universal property then identifies this
fractional sheaf with Mathlib's ordinary module-sheaf pullback.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fanChartMap_inter_opensRange (s t : «Σ».ConeIndex) :
    («Σ».fanChartMap k
      ⟨s.val∩t.val,«Σ».downward s.val s.property _ Finset.inter_subset_left⟩).opensRange =
      («Σ».fanChartMap k s).opensRange⊓(«Σ».fanChartMap k t).opensRange := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    constructor
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
  · rintro ⟨⟨ys,hys⟩,⟨yt,hyt⟩⟩
    obtain ⟨z,hzs,hzt⟩ := («Σ».fanChartMap_eq_iff k s t ys yt).mp (hys.trans hyt.symm)
    refine ⟨z,?_⟩
    rw [← «Σ».fanChartMap_naturality k Finset.inter_subset_left]
    change «Σ».fanChartMap k s (coneChartFaceMap k Finset.inter_subset_left z)=x
    rw [hzs,hys]

variable (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

theorem orbit_preimage_fullChart_forces (s : «Σ».fullCones)
    (x : («Σ».completeQuotientStarFan b I hF).fanScheme k)
    (hx : x∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k s) :
    I.image b⊆s.val := by
  by_contra hn
  have he := «Σ».orbitClosureMap_preimage_chart_empty k b I hF («Σ».fullConeIndex s) hn
  change x∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
    («Σ».fanChartMap k («Σ».fullConeIndex s)).opensRange at hx
  rw [he] at hx
  exact hx

theorem orbit_preimage_fullChart (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k s =
      («Σ».completeQuotientStarFan b I hF).fullChartOpen k
        («Σ».orbitFullConeIndex b I hF s hIs) :=
  «Σ».orbitClosureMap_preimage_chart k b I hF
    ⟨s.val,«Σ».fullCones_mem s,hIs⟩

variable (hpure : «Σ».IsPure) (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)

/-- Empty preimages cause no problem: arbitrary generators there have
no effect on the actual sheaf. On every nonempty preimage the generator
is the projected normalized ambient character. -/
def orbitRestrictionCocycle :
    RationalCartierCocycle ((«Σ».completeQuotientStarFan b I hF).fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure («Σ».orbitClosureMap k b I hF x)
    exact ⟨⟨s⟩,hs⟩
  generator i := («Σ».completeQuotientStarFan b I hF).rationalCharacter k
    (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀))
  transition i j x hi hj := by
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down x hi
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down x hj
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ i.down hIi,
      «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ j.down hIj]
    apply («Σ».completeQuotientStarFan b I hF).cartier_rational_transition_regular k
      («Σ».orbitRestrictionCoefficients b I hF a m₀)
      («Σ».orbitFullConeIndex b I hF i.down hIi)
      («Σ».orbitFullConeIndex b I hF j.down hIj) x
    · rwa [← «Σ».orbit_preimage_fullChart k b I hF i.down hIi]
    · rwa [← «Σ».orbit_preimage_fullChart k b I hF j.down hIj]

theorem orbitRestrictionCocycle_equivalent :
    («Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀).toCartierData.Equivalent
      ((«Σ».completeQuotientStarFan b I hF).fanCartierData k
        («Σ».completeQuotientStarFan_isPure hpure b I hF)
        («Σ».orbitRestrictionCoefficients b I hF a m₀)) := by
  let C := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  let Γ := «Σ».completeQuotientStarFan b I hF
  let E := Γ.fanCartierCocycle k («Σ».completeQuotientStarFan_isPure hpure b I hF)
    («Σ».orbitRestrictionCoefficients b I hF a m₀)
  apply C.equivalent_of_generatorRatios E
  · intro i j x hi hj
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down x hi
    change ((Γ.rationalCharacter k
      (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀)) :
        (Γ.fanScheme k).functionField) /
      (Γ.rationalCharacter k (Γ.cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) j.down) :
          (Γ.fanScheme k).functionField))∈_
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ i.down hIi]
    apply Γ.cartier_rational_transition_regular k _ _ _ x _ hj
    rwa [← «Σ».orbit_preimage_fullChart k b I hF i.down hIi]
  · intro i j x hi hj
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down x hj
    change ((Γ.rationalCharacter k (Γ.cartierLatticePoint
      («Σ».orbitRestrictionCoefficients b I hF a m₀) i.down) :
        (Γ.fanScheme k).functionField) /
      (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a j.down-m₀)) :
          (Γ.fanScheme k).functionField))∈_
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ j.down hIj]
    apply Γ.cartier_rational_transition_regular k _ _ _ x hi
    rwa [← «Σ».orbit_preimage_fullChart k b I hF j.down hIj]

/-- The actual pullback of any regular representative of an ambient
transition function has exactly the projected transition character. -/
theorem orbit_regularTransition_pullback
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val)
    (V : («Σ».fanScheme k).Opens) [Nonempty V]
    [Nonempty ((«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ V)]
    (hVs : V≤«Σ».fullChartOpen k s) (hVt : V≤«Σ».fullChartOpen k t)
    (c : Γ(«Σ».fanScheme k,V))
    (hc : («Σ».fanScheme k).germToFunctionField V c =
      («Σ».rationalCharacter k («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) :
        («Σ».fanScheme k).functionField)) :
    ((«Σ».completeQuotientStarFan b I hF).fanScheme k).germToFunctionField
      ((«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ V) ((«Σ».orbitClosureMap k b I hF).app V c) =
      ((«Σ».completeQuotientStarFan b I hF).rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) :
          ((«Σ».completeQuotientStarFan b I hF).fanScheme k).functionField) := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  let q : «Σ».OrbitConeIndex b I :=
    ⟨s.val∩t.val,«Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left,
      Finset.subset_inter hIs hIt⟩
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid q.val))
  let S := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I q.val)))
  let j : Spec R ⟶ «Σ».fanScheme k := «Σ».fanChartMap k ⟨q.val,q.property.1⟩
  let l : Spec S ⟶ Γ.fanScheme k := Γ.fanChartMap k («Σ».orbitConeQuotientIndex b I hF q)
  letI : IsOpenImmersion j := «Σ».fanChartMap_isOpenImmersion k ⟨q.val,q.property.1⟩
  letI : IsOpenImmersion l := Γ.fanChartMap_isOpenImmersion k
    («Σ».orbitConeQuotientIndex b I hF q)
  let φ : R ⟶ S := CommRingCat.ofHom
    (orbitQuotientAlgebraMap k b I q.val q.property.2).toRingHom
  let d : R := «Σ».cartierTransitionUnit k a s t
  have hpre : («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ (j ''ᵁ ⊤)=l ''ᵁ ⊤ := by
    rw [j.image_top_eq_opensRange,l.image_top_eq_opensRange]
    exact «Σ».orbitClosureMap_preimage_chart k b I hF q
  have hV : V≤j ''ᵁ ⊤ := by
    have h := «Σ».fanChartMap_inter_opensRange k («Σ».fullConeIndex s) («Σ».fullConeIndex t)
    change j.opensRange = «Σ».fullChartOpen k s ⊓ «Σ».fullChartOpen k t at h
    rw [Scheme.Hom.image_top_eq_opensRange,h]
    exact le_inf hVs hVt
  have hd : («Σ».fanScheme k).germToFunctionField V c=affineOpenCoordinateMap R j d := by
    rw [hc]
    exact («Σ».chartRationalMap_character k ⟨q.val,q.property.1⟩
      («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)
      («Σ».cartier_difference_mem_overlap a s t).1).symm
  rw [affineChartSection_pullback_value R S j l («Σ».orbitClosureMap k b I hF) φ
    («Σ».orbitClosureMap_chart k b I hF q) hpre V hV c d hd]
  have hm : faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)∈
      dualConeMonoid (orbitQuotientCone b I q.val) := by
    have h := (φ d).property
    rw [mem_monoidChartAlgebra] at h
    apply h
    change faceCharacterProjection b I
        («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) ∈
      ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
        («Σ».cartierTransitionUnit k a s t) : AddMonoidAlgebra k (Lattice (n-I.card)))).coeff.support
    rw [«Σ».orbit_cartierTransition_character b I k a s t hIs hIt]
    simp
  have hd' : φ d=chartCharacter k (dualConeMonoid (orbitQuotientCone b I q.val))
      (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) hm := by
    apply Subtype.ext
    exact «Σ».orbit_cartierTransition_character b I k a s t hIs hIt
  rw [hd']
  exact Γ.chartRationalMap_character k («Σ».orbitConeQuotientIndex b I hF q) _ hm

theorem orbitRestriction_frames_compatible :
    let C := «Σ».fanCartierCocycle k hpure a
    let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
    ModuleFrameGluing.Compatible
      (N := (Scheme.Modules.pushforward («Σ».orbitClosureMap k b I hF)).obj B.sheaf)
      C.openSet C.localFrame
      (fun i=>ModuleFrame.generator (B.localFrame i) (B.openSet i) le_rfl) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  let Γ := «Σ».completeQuotientStarFan b I hF
  let f := «Σ».orbitClosureMap k b I hF
  change ModuleFrameGluing.Compatible
    (N := (Scheme.Modules.pushforward f).obj B.sheaf)
    C.openSet C.localFrame
    (fun i=>ModuleFrame.generator (B.localFrame i) (B.openSet i) le_rfl)
  intro i j V hi hj
  let W := f ⁻¹ᵁ V
  by_cases hW : Nonempty W
  · letI := hW
    let bi : B.index := i
    let bj : B.index := j
    have hWi : W≤B.openSet bi := f.preimage_mono hi
    have hWj : W≤B.openSet bj := f.preimage_mono hj
    let y : W := Classical.choice hW
    letI : Nonempty V := ⟨⟨f y.val,y.property⟩⟩
    letI : Nonempty (B.openSet bi) := ⟨⟨y.val,hi y.property⟩⟩
    letI : Nonempty (B.openSet bj) := ⟨⟨y.val,hj y.property⟩⟩
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down y.val (hi y.property)
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down y.val (hj y.property)
    let c : Γ(«Σ».fanScheme k,V) := ModuleFrame.coordinates (C.localFrame j) V hj
      (ModuleFrame.generator (C.localFrame i) V hi)
    let d : Γ(Γ.fanScheme k,W) := f.app V c
    have hc₀ : («Σ».fanScheme k).germToFunctionField V c =
        (C.generator i : («Σ».fanScheme k).functionField) /
          (C.generator j : («Σ».fanScheme k).functionField) := by
      calc
        _ = rationalValue («Σ».fanScheme k) V
            (ModuleFrame.generator (C.localFrame i) V hi).val /
              (C.generator j : («Σ».fanScheme k).functionField) :=
          C.localCoordinates_value j V hj (ModuleFrame.generator (C.localFrame i) V hi)
        _ = C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hi) /
            (C.generator j : («Σ».fanScheme k).functionField) :=
          congrArg (fun z : («Σ».fanScheme k).functionField =>
            z / (C.generator j : («Σ».fanScheme k).functionField))
            (C.toCartierData_sectionValue V (ModuleFrame.generator (C.localFrame i) V hi)).symm
        _ = _ := congrArg (fun z : («Σ».fanScheme k).functionField =>
          z / (C.generator j : («Σ».fanScheme k).functionField))
          (C.localFrame_generator_value i V hi)
    have hc : («Σ».fanScheme k).germToFunctionField V c =
        («Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down-
          «Σ».cartierLatticePoint a j.down) : («Σ».fanScheme k).functionField) := by
      simpa only [C,fanCartierCocycle,«Σ».rationalCharacter_sub k,
        Units.val_div_eq_div_val] using hc₀
    have hpc := «Σ».orbit_regularTransition_pullback k b I hF a
      i.down j.down hIi hIj V hi hj c hc
    have hmul : (B.generator bi : (Γ.fanScheme k).functionField) =
        (Γ.fanScheme k).germToFunctionField W d *
          (B.generator bj : (Γ.fanScheme k).functionField) := by
      change (B.generator bi : (Γ.fanScheme k).functionField) =
        (Γ.fanScheme k).germToFunctionField W (f.app V c) * _
      rw [hpc]
      change (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀)) :
          (Γ.fanScheme k).functionField) =
        (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-
          «Σ».cartierLatticePoint a j.down)) : (Γ.fanScheme k).functionField) *
        (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a j.down-m₀)) :
          (Γ.fanScheme k).functionField)
      rw [← Units.val_mul,← Γ.rationalCharacter_add k,← map_add (faceCharacterProjection b I)]
      congr 3
      abel
    apply B.toCartierData.sectionValue_injective W
    change B.toCartierData.sectionValue W
      (moduleRes B.sheaf hWi
        (ModuleFrame.generator (B.localFrame bi) (B.openSet bi) le_rfl)) =
      B.toCartierData.sectionValue W (d • moduleRes B.sheaf hWj
        (ModuleFrame.generator (B.localFrame bj) (B.openSet bj) le_rfl))
    calc
      _ = B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bi) W hWi) :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W s)
          (ModuleFrame.generator_res (B.localFrame bi) le_rfl hWi)
      _ = (B.generator bi : (Γ.fanScheme k).functionField) :=
        B.localFrame_generator_value bi W hWi
      _ = (Γ.fanScheme k).germToFunctionField W d *
          (B.generator bj : (Γ.fanScheme k).functionField) := hmul
      _ = (Γ.fanScheme k).germToFunctionField W d *
          B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bj) W hWj) :=
        congrArg (fun z : (Γ.fanScheme k).functionField =>
          (Γ.fanScheme k).germToFunctionField W d * z)
          (B.localFrame_generator_value bj W hWj).symm
      _ = B.toCartierData.sectionValue W
          (d • ModuleFrame.generator (B.localFrame bj) W hWj) :=
        (B.toCartierData.sectionValue_smul W d
          (ModuleFrame.generator (B.localFrame bj) W hWj)).symm
      _ = _ := congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W (d • s))
        (ModuleFrame.generator_res (B.localFrame bj) le_rfl hWj).symm
  · have hb : W=⊥ := by
      apply le_antisymm
      · intro y hy
        exact False.elim (hW ⟨⟨y,hy⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty B.sheaf W hb
    change (_ : Γ(B.sheaf,W)) = _
    exact Subsingleton.elim _ _

/-- The actual ambient line bundle restricts to the actual fan Cartier
sheaf with the computed quotient-ray coefficients. -/
def orbitCartierPullbackIso :
    (Scheme.Modules.pullback («Σ».orbitClosureMap k b I hF)).obj
      («Σ».fanCartierData k hpure a).sheaf ≅
        ((«Σ».completeQuotientStarFan b I hF).fanCartierData k
          («Σ».completeQuotientStarFan_isPure hpure b I hF)
          («Σ».orbitRestrictionCoefficients b I hF a m₀)).sheaf := by
  let C := «Σ».fanCartierCocycle k hpure a
  let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  exact pullbackIso_of_compatible_frames («Σ».orbitClosureMap k b I hF)
    C.openSet C.covers C.localFrame B.localFrame
    («Σ».orbitRestriction_frames_compatible k b I hF hpure a m₀ hm₀) ≪≫
      («Σ».orbitRestrictionCocycle_equivalent k b I hF hpure a m₀ hm₀).choose

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitRestrictionCocycle_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_regularTransition_pullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitCartierPullbackIso
