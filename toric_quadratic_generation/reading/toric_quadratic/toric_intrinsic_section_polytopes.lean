module

public import PaperVerification.ToricNormalizedCharacterShift
public import PaperVerification.ToricFanSectionCoordinates
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# Intrinsic section polytopes and the proved fan dictionary

The polytope is the real convex hull of the actual Laurent characters of
the torus-normalized global-section module. Its definition contains no
chosen fan. A torus-preserving scheme isomorphism and a second choice of
torus frame change this polytope by the explicitly exhibited integral
translation, and the remaining polytope is proved to be the actual fan
halfspace polytope.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (jX : splitTorus k (Fin n→ℤ) ⟶ X)
    (jY : splitTorus k (Fin n→ℤ) ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY]
    [jX.IsOver (Spec (CommRingCat.of k))]
    [jY.IsOver (Spec (CommRingCat.of k))]
    (e : Y≅X) [e.hom.IsOver (Spec (CommRingCat.of k))]
    (he : jY≫e.hom=jX)

local instance : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

include he in
/-- A torus-preserving scheme isomorphism preserves the actual rational
Laurent characters, not merely an abstractly isomorphic character space. -/
theorem openTorusRationalAlgHom_schemeIso (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    dominantFunctionFieldMap e.hom (openTorusRationalAlgHom k n X jX f)=
      openTorusRationalAlgHom k n Y jY f := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  let jX' : Spec R ⟶ X := jX
  let jY' : Spec R ⟶ Y := jY
  letI : IsOpenImmersion jX' := ‹IsOpenImmersion jX›
  letI : IsOpenImmersion jY' := ‹IsOpenImmersion jY›
  exact dominantFunctionFieldMap_affineCoordinate R R jX' jY' e.hom (𝟙 R)
    (by rw [Spec.map_id,Category.id_comp]; exact he) f

include he in
theorem schemeIso_preimage_torusOpen :
    e.hom ⁻¹ᵁ jX.opensRange=jY.opensRange := by
  have hinj : Function.Injective e.hom := by
    intro y z h
    have hh := congrArg (fun x=>e.inv x) h
    have hcomp (w : Y) : e.inv (e.hom w)=w := by
      change (e.hom≫e.inv) w=w
      rw [e.hom_inv_id]
      rfl
    simpa only [hcomp] using hh
  ext y
  change e.hom y∈Set.range jX ↔ y∈Set.range jY
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t,hinj ?_⟩
    change (jY≫e.hom) t=e.hom y
    rw [he]
    exact ht
  · rintro ⟨t,rfl⟩
    refine ⟨t,?_⟩
    change jX t=(jY≫e.hom) t
    rw [he]

include he in
theorem torusSectionCharacters_schemeIso (D : CartierData X) :
    torusSectionCharacters k n Y jY (D.dominantPullback e.hom)=
      torusSectionCharacters k n X jX D := by
  ext f
  change openTorusRationalAlgHom k n Y jY f∈
      ((D.dominantPullback e.hom).globalSectionValue k).range ↔
    openTorusRationalAlgHom k n X jX f∈(D.globalSectionValue k).range
  rw [← openTorusRationalAlgHom_schemeIso k n X Y jX jY e he f]
  exact D.globalSectionRange_schemeIso_iff e _

include he in
theorem torusSectionExponents_schemeIso (D : CartierData X) :
    torusSectionExponents k n Y jY (D.dominantPullback e.hom)=
      torusSectionExponents k n X jX D := by
  unfold torusSectionExponents
  rw [torusSectionCharacters_schemeIso k n X Y jX jY e he D]

include he in
theorem normalizedPullback_unitFrames (D : CartierData X) :
    ((torusNormalizedCartier k n X jX D).dominantPullback e.hom).localCocycle.HasUnitFramesOn jY.opensRange := by
  have h := (torusNormalizedCartier k n X jX D).hasUnitFramesOn_dominantPullback
    (torusNormalizedCartier_unitFrames k n X jX D) e.hom
  rw [schemeIso_preimage_torusOpen k n X Y jX jY e he] at h
  exact h

include he in
/-- The exact intrinsic exponent shift under a genuine torus-preserving
scheme isomorphism. The divisor is pulled back as an actual Cartier sheaf. -/
theorem intrinsicSectionExponents_schemeIso_translate (D : CartierData X) :
    ∃ c : kˣ, ∃ v : Lattice n,
      let E := (torusNormalizedCartier k n X jX D).dominantPullback e.hom
      (torusCartierGenerator k n Y jY E : Y.functionField)=
          openTorusRationalAlgHom k n Y jY (AddMonoidAlgebra.single v (c:k)) ∧
      intrinsicSectionExponents k n X jX D=
        (fun m=>v+m) '' intrinsicSectionExponents k n Y jY E := by
  let E := (torusNormalizedCartier k n X jX D).dominantPullback e.hom
  obtain ⟨c,v,hv⟩ := torusCartierGenerator_scalar_character k n Y jY E
    (normalizedPullback_unitFrames k n X Y jX jY e he D)
  refine ⟨c,v,hv,?_⟩
  rw [intrinsicSectionExponents_eq,
    ← torusSectionExponents_schemeIso k n X Y jX jY e he,
    torusSectionExponents_eq_translate k n Y jY E c v hv]

/-- The intrinsic real section polytope, defined solely by actual global
sections and the original dense torus. -/
def intrinsicSectionPolytope (D : CartierData X) : Set (Ambient n) :=
  convexHull ℝ (embed n '' intrinsicSectionExponents k n X jX D)

theorem convexHull_embed_translate (v : Lattice n) (S : Set (Lattice n)) :
    convexHull ℝ (embed n '' ((fun m=>v+m) '' S))=
      (fun x : Ambient n=>embed n v+x) '' convexHull ℝ (embed n '' S) := by
  have h : embed n '' ((fun m=>v+m) '' S)=
      (fun x : Ambient n=>embed n v+x) '' (embed n '' S) := by
    rw [Set.image_image,Set.image_image]
    congr 1
    funext m
    exact map_add (embed n) v m
  rw [h]
  exact ((AffineEquiv.constVAdd ℝ (Ambient n) (embed n v)).toAffineMap.image_convexHull (embed n '' S)).symm

include he in
theorem intrinsicSectionPolytope_schemeIso_translate (D : CartierData X) :
    ∃ v : Lattice n,
      intrinsicSectionPolytope k n X jX D=
        (fun x : Ambient n=>embed n v+x) ''
          intrinsicSectionPolytope k n Y jY
            ((torusNormalizedCartier k n X jX D).dominantPullback e.hom) := by
  obtain ⟨c,v,hq,hv⟩ :=
    intrinsicSectionExponents_schemeIso_translate k n X Y jX jY e he D
  refine ⟨v,?_⟩
  unfold intrinsicSectionPolytope
  rw [hv,convexHull_embed_translate]

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance intrinsicSection_splitTorus_isOpenImmersion : IsOpenImmersion
    (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
      «Σ».splitTorusOpenMap k) :=
  «Σ».splitTorusOpenMap_isOpenImmersion k

local instance intrinsicSection_splitTorus_isOver :
    (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
      «Σ».splitTorusOpenMap k).IsOver (Spec (CommRingCat.of k)) :=
  «Σ».splitTorusOpenMap_isOver k

theorem openTorusRationalAlgHom_eq_torusRationalAlgHom :
    openTorusRationalAlgHom k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k)=
      «Σ».torusRationalAlgHom k := by
  let j : ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k :=
    «Σ».splitTorusOpenMap k
  letI : IsOpenImmersion j := «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : j.IsOver (Spec (CommRingCat.of k)) := «Σ».splitTorusOpenMap_isOver k
  apply AlgHom.ext
  intro f
  exact (openTorusRationalAlgHom_value k n («Σ».fanScheme k) j f).trans
    («Σ».torusRationalMap_eq_openImmersion k f).symm

/-- The intrinsic normalized section exponents on the fan scheme are
exactly the actual lattice points of its recovered support polytope. -/
theorem intrinsicSectionExponents_eq_fanIntegralExponents (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    intrinsicSectionExponents k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D=
      «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D) := by
  let j : ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k :=
    «Σ».splitTorusOpenMap k
  letI : IsOpenImmersion j := «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : j.IsOver (Spec (CommRingCat.of k)) := «Σ».splitTorusOpenMap_isOver k
  refine (intrinsicSectionExponents_eq k n («Σ».fanScheme k) j D).trans ?_
  ext m
  change openTorusRationalAlgHom k n («Σ».fanScheme k) j
      (AddMonoidAlgebra.single m (1:k))∈
      Set.range ((«Σ».normalizedCartier k D).sectionValue ⊤) ↔ _
  have hj : openTorusRationalAlgHom k n («Σ».fanScheme k) j =
      «Σ».torusRationalAlgHom k := «Σ».openTorusRationalAlgHom_eq_torusRationalAlgHom k
  rw [hj]
  change «Σ».torusRationalMap k (AddMonoidAlgebra.single m (1:k))∈
      Set.range ((«Σ».normalizedCartier k D).sectionValue ⊤) ↔ _
  rw [«Σ».normalizedCartier_globalRange k hpure D]
  constructor
  · rintro ⟨f,hf,he⟩
    have hf' := («Σ».torusRationalMap_injective k) he
    rw [hf'] at hf
    exact (single_mem_characterModule k _ m).mp hf
  · intro hm
    exact ⟨AddMonoidAlgebra.single m 1,
      (single_mem_characterModule k _ m).mpr hm,rfl⟩

/-- For an integral nef support, the actual halfspace polytope is the
convex hull of all of its actual lattice points. Both inclusions are
proved; the integral Cartier vertices supply the reverse inclusion. -/
theorem convexHull_fanIntegralExponents (hpure : «Σ».IsPure)
    (a : Lattice n→ℤ) (ha : «Σ».IsNef (fun u=>(a u:ℝ))) :
    convexHull ℝ (embed n '' «Σ».fanIntegralExponents a)=
      «Σ».fanPolytope (fun u=>(a u:ℝ)) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨m,hm,rfl⟩
      exact hm
    · exact «Σ».convex_fanPolytope _
  · rw [«Σ».fanPolytope_eq_convexHull_cartier hpure _ ha]
    apply convexHull_mono
    rintro _ ⟨s,rfl⟩
    refine ⟨«Σ».cartierLatticePoint a s,?_,«Σ».embed_cartierLatticePoint a s⟩
    change embed n («Σ».cartierLatticePoint a s)∈«Σ».fanPolytope _
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_mem_of_nef ha s

theorem intrinsicSectionPolytope_eq_fanPolytope (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k))
    (hD : «Σ».IsNef (fun u=>(«Σ».cartierCoefficients k hpure D u:ℝ))) :
    intrinsicSectionPolytope k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D=
      «Σ».fanPolytope (fun u=>(«Σ».cartierCoefficients k hpure D u:ℝ)) := by
  unfold intrinsicSectionPolytope
  rw [«Σ».intrinsicSectionExponents_eq_fanIntegralExponents k hpure D]
  exact «Σ».convexHull_fanIntegralExponents hpure _ hD

/-- The intrinsic polytope and the intrinsic character set of an
arbitrary Cartier divisor are both the same integral translate of their
recovered fan counterparts. This comparison does not define either
intrinsic object using the fan. -/
theorem intrinsic_sections_fan_translate (hpure : «Σ».IsPure)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : ToricSchemes.splitTorus k (Fin n→ℤ) ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]
    (e : «Σ».fanScheme k≅X) [e.hom.IsOver (Spec (CommRingCat.of k))]
    (he : «Σ».splitTorusOpenMap k≫e.hom=j) (D : CartierData X)
    (hD : «Σ».IsNef (fun u=>(«Σ».cartierCoefficients k hpure
      ((torusNormalizedCartier k n X j D).dominantPullback e.hom) u:ℝ))) :
    ∃ v : Lattice n,
      let E := (torusNormalizedCartier k n X j D).dominantPullback e.hom
      let a := «Σ».cartierCoefficients k hpure E
      intrinsicSectionExponents k n X j D=(fun m=>v+m) '' «Σ».fanIntegralExponents a ∧
      intrinsicSectionPolytope k n X j D=
        (fun x : Ambient n=>embed n v+x) '' «Σ».fanPolytope (fun u=>(a u:ℝ)) := by
  let E := (torusNormalizedCartier k n X j D).dominantPullback e.hom
  obtain ⟨c,v,hq,hv⟩ := intrinsicSectionExponents_schemeIso_translate
    k n X («Σ».fanScheme k) j («Σ».splitTorusOpenMap k) e he D
  rw [«Σ».intrinsicSectionExponents_eq_fanIntegralExponents k hpure E] at hv
  refine ⟨v,hv,?_⟩
  unfold intrinsicSectionPolytope
  rw [hv,convexHull_embed_translate,«Σ».convexHull_fanIntegralExponents hpure _ hD]

end PaperVerification.ToricGeometry.SmoothCompleteFan
