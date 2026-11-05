module

public import PaperVerification.ToricOrbitFacePullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

/-!
# The quotient-star scheme is an actual closed subscheme

The global map constructed from the actual semigroup quotient maps is a
closed immersion. Its pullback over a cone containing the orbit cone is
exactly the corresponding quotient chart, as a scheme-theoretic pullback.
Its preimage over every other cone is empty. These facts are proved from
the real fan intersection identity and the explicit localizations.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

theorem orbitChart_jointly_surjective
    (x : («Σ».completeQuotientStarFan b I hF).fanScheme k) :
    ∃ (s : «Σ».OrbitConeIndex b I) (y : coneChart k (orbitQuotientCone b I s.val)),
      («Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s) y=x := by
  obtain ⟨t,y,hy⟩ := («Σ».completeQuotientStarFan b I hF).fanChartMap_jointly_surjective k x
  obtain ⟨s,hs⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
  subst t
  exact ⟨s,y,hy⟩

theorem orbitClosureMap_preimage_chart_empty (t : «Σ».ConeIndex)
    (hnot : ¬I.image b⊆t.val) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ («Σ».fanChartMap k t).opensRange = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨s,y,rfl⟩ := «Σ».orbitChart_jointly_surjective k b I hF x
  obtain ⟨z,hz⟩ := hx
  have heq : «Σ».fanChartMap k ⟨s.val,s.property.1⟩
        (orbitQuotientChartMap k b I s.val s.property.2 y) = «Σ».fanChartMap k t z := by
    rw [← Scheme.Hom.comp_apply]
    rw [← «Σ».orbitClosureMap_chart k b I hF s]
    exact hz.symm
  obtain ⟨w,hws,hwt⟩ := («Σ».fanChartMap_eq_iff k
    ⟨s.val,s.property.1⟩ t _ z).mp heq
  letI : IsOpenImmersion
      (coneChartFaceMap k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val)) :=
    «Σ».coneChartFaceMap_isOpenImmersion k s.val (s.val ∩ t.val)
      s.property.1 Finset.inter_subset_left
  have hface : orbitQuotientChartMap k b I s.val s.property.2 y∈
      (coneChartFaceMap k (Finset.inter_subset_left : s.val∩t.val⊆s.val)).opensRange :=
    ⟨w,hws⟩
  have hnotInter : ¬I.image b⊆s.val∩t.val := fun h => hnot
    (h.trans Finset.inter_subset_right)
  have hempty := «Σ».orbitQuotientChart_preimage_face_empty b I k s.property.1
    (Finset.inter_subset_left : s.val∩t.val⊆s.val) s.property.2 hnotInter
  have hy : y∈(orbitQuotientChartMap k b I s.val s.property.2) ⁻¹ᵁ
      (coneChartFaceMap k (Finset.inter_subset_left : s.val∩t.val⊆s.val)).opensRange := hface
  rw [hempty] at hy
  exact hy

theorem orbitClosureMap_preimage_chart (t : «Σ».OrbitConeIndex b I) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
        («Σ».fanChartMap k ⟨t.val,t.property.1⟩).opensRange =
      ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF t)).opensRange := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  ext x
  constructor
  · intro hx
    obtain ⟨s,y,rfl⟩ := «Σ».orbitChart_jointly_surjective k b I hF x
    obtain ⟨z,hz⟩ := hx
    have heq : «Σ».fanChartMap k ⟨s.val,s.property.1⟩
          (orbitQuotientChartMap k b I s.val s.property.2 y) =
        «Σ».fanChartMap k ⟨t.val,t.property.1⟩ z := by
      rw [← Scheme.Hom.comp_apply,← «Σ».orbitClosureMap_chart k b I hF s]
      exact hz.symm
    obtain ⟨w,hws,hwt⟩ := («Σ».fanChartMap_eq_iff k
      ⟨s.val,s.property.1⟩ ⟨t.val,t.property.1⟩ _ z).mp heq
    let u : «Σ».OrbitConeIndex b I :=
      ⟨s.val∩t.val,«Σ».downward s.val s.property.1 _ Finset.inter_subset_left,
        Finset.subset_inter s.property.2 t.property.2⟩
    have H := «Σ».orbitQuotientChart_face_isPullback b I k s.property.1
      (Finset.inter_subset_left : u.val⊆s.val) u.property.2
    letI := «Σ».coneChartFaceMap_isOpenImmersion k s.val u.val
      s.property.1 Finset.inter_subset_left
    have hy : y∈Set.range (pullback.snd
        (coneChartFaceMap k (Finset.inter_subset_left : u.val⊆s.val))
        (orbitQuotientChartMap k b I s.val s.property.2)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨w,hws⟩
    obtain ⟨p,hp⟩ := hy
    let r := H.isoPullback.inv p
    have hr : coneChartFaceMap k
        (orbitQuotientCone_mono b I (Finset.inter_subset_left : u.val⊆s.val)) r = y :=
      (congrArg (fun f => f p) H.isoPullback_inv_snd).trans hp
    refine ⟨coneChartFaceMap k
      (orbitQuotientCone_mono b I (Finset.inter_subset_right : u.val⊆t.val)) r,?_⟩
    have htmap := Γ.fanChartMap_naturality k
      (s := «Σ».orbitConeQuotientIndex b I hF u)
      (t := «Σ».orbitConeQuotientIndex b I hF t)
      (orbitQuotientCone_mono b I (Finset.inter_subset_right : u.val ⊆ t.val))
    have hsmap := Γ.fanChartMap_naturality k
      (s := «Σ».orbitConeQuotientIndex b I hF u)
      (t := «Σ».orbitConeQuotientIndex b I hF s)
      (orbitQuotientCone_mono b I (Finset.inter_subset_left : u.val ⊆ s.val))
    exact (congrArg (fun f => f r) htmap).trans
      ((congrArg (fun f => f r) hsmap).symm.trans
        (congrArg (Γ.fanChartMap k («Σ».orbitConeQuotientIndex b I hF s)) hr))
  · rintro ⟨y,rfl⟩
    refine ⟨orbitQuotientChartMap k b I t.val t.property.2 y,?_⟩
    exact (congrArg (fun f => f y) («Σ».orbitClosureMap_chart k b I hF t)).symm

/-- The quotient chart is the actual scheme-theoretic pullback of the
corresponding ambient chart. -/
theorem orbitClosureMap_chart_isPullback (t : «Σ».OrbitConeIndex b I) :
    IsPullback (orbitQuotientChartMap k b I t.val t.property.2)
      ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF t))
      («Σ».fanChartMap k ⟨t.val,t.property.1⟩) («Σ».orbitClosureMap k b I hF) := by
  exact @IsOpenImmersion.isPullback
    (coneChart k (orbitQuotientCone b I t.val)) (coneChart k t.val)
    ((«Σ».completeQuotientStarFan b I hF).fanScheme k) («Σ».fanScheme k)
    (orbitQuotientChartMap k b I t.val t.property.2)
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
      («Σ».orbitConeQuotientIndex b I hF t))
    («Σ».fanChartMap k ⟨t.val,t.property.1⟩) («Σ».orbitClosureMap k b I hF)
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap_isOpenImmersion k
      («Σ».orbitConeQuotientIndex b I hF t))
    («Σ».fanChartMap_isOpenImmersion k ⟨t.val,t.property.1⟩)
    («Σ».orbitClosureMap_chart k b I hF t)
    («Σ».orbitClosureMap_preimage_chart k b I hF t)

/-- Closedness is checked on the actual ambient affine open cover. -/
instance orbitClosureMap_isClosedImmersion :
    IsClosedImmersion («Σ».orbitClosureMap k b I hF) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    («Σ».fanSchemeOpenCover k)]
  intro t
  let t₀ : «Σ».ConeIndex := t
  letI : IsOpenImmersion («Σ».fanChartMap k t₀) :=
    «Σ».fanChartMap_isOpenImmersion k t₀
  change IsClosedImmersion
    (pullback.snd («Σ».orbitClosureMap k b I hF) («Σ».fanChartMap k t₀))
  by_cases hIt : I.image b ⊆ t₀.val
  · let t' : «Σ».OrbitConeIndex b I := ⟨t₀.val, t₀.property, hIt⟩
    have H := «Σ».orbitClosureMap_chart_isPullback k b I hF t'
    have hc : IsClosedImmersion
        (H.flip.isoPullback.inv ≫ orbitQuotientChartMap k b I t'.val t'.property.2) :=
      inferInstance
    exact Eq.mp (congrArg (fun f => IsClosedImmersion f) H.flip.isoPullback_inv_snd) hc
  · letI : IsEmpty ↥(pullback («Σ».orbitClosureMap k b I hF)
        («Σ».fanChartMap k t₀) : Scheme) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro x ⟨y,rfl⟩ hx
      have hy : y∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
          («Σ».fanChartMap k t₀).opensRange := hx
      rw [«Σ».orbitClosureMap_preimage_chart_empty k b I hF t₀ hIt] at hy
      exact hy
    infer_instance

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_isClosedImmersion
