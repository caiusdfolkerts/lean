module

public import ToricQuadratic.InteriorUnitBoxes
public import ToricQuadratic.FaceUnitBoxes
public import paper_verification.toric021

@[expose] public section

/-!
# Full mixed multiplication from unit corner boxes

This proves Lemma 4.2 with its literal geometric hypotheses, including
boundary targets. The induction takes the two corresponding support faces
in the same saturated quotient lattice; unit boxes descend to these faces.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

/-- The exact induction predicate for the full unit-box multiplication lemma. -/
def UnitBoxDecompositionDimension (d : ℕ) : Prop :=
  ∀ P Q : LatticePolytope d, P.UnitCornerBoxes → Q.UnitCornerBoxes →
    P.SameNormalFan Q → ∀ m : Lattice d,
      embed d m ∈ P.minkowskiSum Q →
      ∃ x y : Lattice d,
        embed d x ∈ P.carrier ∧ embed d y ∈ Q.carrier ∧ x + y = m

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Minkowski addition for the actual integral support functions of the two
input polytopes. This bridge uses only nef support addition. -/
theorem unitBox_integralSupport_sum_eq (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan) :
    «Σ».fanPolytope (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      P.minkowskiSum Q := by
  have he : (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      (fun u => (P.integralSupport u : ℝ)) +
        (fun u => (Q.integralSupport u : ℝ)) := by
    funext u
    simp
  rw [he, «Σ».fanPolytope_add hpure _ _
    (IsStrictSupport.isNef «Σ» (P.integralSupport_isStrictSupport «Σ» hfanP))
    (IsStrictSupport.isNef «Σ» (Q.integralSupport_isStrictSupport «Σ» hfanQ)),
    P.fanPolytope_integralSupport_eq «Σ» hfanP,
    Q.fanPolytope_integralSupport_eq «Σ» hfanQ]
  rfl

/-- Points in the ambient polytope and in a saturated support-face chart
belong to the actual supporting face. -/
theorem mem_supportFace_of_mem_chart_range
    (a : Lattice n → ℤ) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient n)
    (hx : x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)))
    (hr : x ∈ Set.range (quotientFaceIntegralChart a b I).realMap) :
    x ∈ «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  refine ⟨hx, ?_⟩
  rw [quotientFaceIntegralChart_realMap] at hr
  have hactive := (mem_range_quotientFaceMap_iff
    (fun u => (a u : ℝ)) b I x).mp hr
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  exact hactive i hi

/-- The complete boundary branch, with no edge-length assumption. -/
theorem unit_box_decomposition_at_support_face
    (hpure : «Σ».IsPure) (P Q : LatticePolytope n)
    (hP : P.UnitCornerBoxes) (hQ : Q.UnitCornerBoxes)
    (hfanP : «Σ».realCones = P.normalFan)
    (hfanQ : «Σ».realCones = Q.normalFan)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) (hIpos : 0 < I.card)
    (m : Lattice n) (hm : embed n m ∈ P.minkowskiSum Q)
    (hactive : ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) (embed n m) =
        -((P.integralSupport + Q.integralSupport) (b i) : ℝ))
    (IH : ∀ d : ℕ, d < n → UnitBoxDecompositionDimension d) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧ x + y = m := by
  let a := P.integralSupport
  let c := Q.integralSupport
  have ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)) :=
    P.integralSupport_isStrictSupport «Σ» hfanP
  have hc : «Σ».IsStrictSupport (fun u => (c u : ℝ)) :=
    Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hcarP : P.carrier = «Σ».fanPolytope (fun u => (a u : ℝ)) :=
    (P.fanPolytope_integralSupport_eq «Σ» hfanP).symm
  have hcarQ : Q.carrier = «Σ».fanPolytope (fun u => (c u : ℝ)) :=
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ).symm
  have haN := IsStrictSupport.isNef «Σ» ha
  have hcN := IsStrictSupport.isNef «Σ» hc
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eA := quotientFaceIntegralChart a b I
  let eC := quotientFaceIntegralChart c b I
  let eSum := quotientFaceIntegralChart (a + c) b I
  have hqa : Ψ.IsStrictSupport
      (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) := by
    rw [«Σ».faceSupportLattice_cast]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  have hqc : Ψ.IsStrictSupport
      (fun u => («Σ».faceSupportLattice b I hF c u : ℝ)) := by
    rw [«Σ».faceSupportLattice_cast]
    exact «Σ».faceSupport_isStrictSupport b I hF _ hc
  obtain ⟨A, hApoly, hAsm, hAfan, hAimage⟩ :=
    «Σ».exists_face_supportPolytope_of_nefRestriction b I hF hpure a haN hqa
  obtain ⟨C, hCpoly, hCsm, hCfan, hCimage⟩ :=
    «Σ».exists_face_supportPolytope_of_nefRestriction b I hF hpure c hcN hqc
  have hfaceA : IsExtreme ℝ P.carrier
      («Σ».supportFace (fun u => (a u : ℝ)) (I.image b)) := by
    rw [hcarP]
    exact «Σ».supportFace_isExtreme _ _ (fun u hu => «Σ».ray_mem_of_mem_cone hF hu)
  have hfaceC : IsExtreme ℝ Q.carrier
      («Σ».supportFace (fun u => (c u : ℝ)) (I.image b)) := by
    rw [hcarQ]
    exact «Σ».supportFace_isExtreme _ _ (fun u hu => «Σ».ray_mem_of_mem_cone hF hu)
  have hAb : A.UnitCornerBoxes := hP.face_chart _ hfaceA A hAsm eA hAimage (by
    intro x hx hr
    exact «Σ».mem_supportFace_of_mem_chart_range a b I x
      (by simpa only [hcarP] using hx) hr)
  have hCb : C.UnitCornerBoxes := hQ.face_chart _ hfaceC C hCsm eC hCimage (by
    intro x hx hr
    exact «Σ».mem_supportFace_of_mem_chart_range c b I x
      (by simpa only [hcarQ] using hx) hr)
  obtain ⟨mQ, hmQmap⟩ := eSum.exists_latticeMap_of_mem_range m (by
    rw [quotientFaceIntegralChart_realMap]
    exact (mem_range_quotientFaceMap_iff _ b I _).mpr hactive)
  have hmQreal : eSum.realMap (embed (n - I.card) mQ) = embed n m := by
    rw [← IntegralAffineEmbedding.embed_latticeMap, hmQmap]
  have hsumcast : (fun u => ((a + c) u : ℝ)) =
      (fun u => (a u : ℝ)) + (fun u => (c u : ℝ)) := by
    funext u
    simp
  have hsumN : «Σ».IsNef (fun u => ((a + c) u : ℝ)) := by
    rw [hsumcast]
    exact IsNef.add «Σ» haN hcN
  have hmface : embed n m ∈
      «Σ».supportFace (fun u => ((a + c) u : ℝ)) (I.image b) := by
    refine ⟨?_, ?_⟩
    · rw [«Σ».unitBox_integralSupport_sum_eq hpure P Q hfanP hfanQ]
      exact hm
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact hactive i hi
  have hmQ : embed (n - I.card) mQ ∈ Ψ.fanPolytope
      (fun u => («Σ».faceSupportLattice b I hF (a + c) u : ℝ)) := by
    have himage := «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure
      (a + c) hsumN
    rw [← himage] at hmface
    obtain ⟨z, hz, he⟩ := hmface
    have he' : z = embed (n - I.card) mQ :=
      eSum.realMap_injective (he.trans hmQreal.symm)
    simpa only [he'] using hz
  have hqA := «Σ».faceSupport_isNef b I hF _ haN
  have hqC := «Σ».faceSupport_isNef b I hF _ hcN
  have hsumSupport : «Σ».faceSupport b I hF (fun u => ((a + c) u : ℝ)) =
      «Σ».faceSupport b I hF (fun u => (a u : ℝ)) +
        «Σ».faceSupport b I hF (fun u => (c u : ℝ)) := by
    rw [hsumcast, «Σ».faceSupport_add]
  have hsumPoly : Ψ.fanPolytope («Σ».faceSupport b I hF
      (fun u => ((a + c) u : ℝ))) = A.minkowskiSum C := by
    rw [hsumSupport, Ψ.fanPolytope_add
      («Σ».completeQuotientStarFan_isPure hpure b I hF) _ _ hqA hqC,
      ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast]
    change _ = A.carrier + C.carrier
    rw [← hApoly, ← hCpoly]
  rw [«Σ».faceSupportLattice_cast, hsumPoly] at hmQ
  have hIn : I.card ≤ n := by
    simpa only [Finset.card_fin] using Finset.card_le_card (Finset.subset_univ I)
  have hd : n - I.card < n := by omega
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ⟩ := IH (n - I.card) hd A C hAb hCb
    (hAfan.trans hCfan.symm) mQ hmQ
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    rw [hcarP, IntegralAffineEmbedding.embed_latticeMap]
    exact hx.1
  · have hy : eC.realMap (embed (n - I.card) yQ) ∈ eC.realMap '' C.carrier :=
      Set.mem_image_of_mem _ hyQ
    rw [hCimage] at hy
    rw [hcarQ, IntegralAffineEmbedding.embed_latticeMap]
    exact hy.1
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap

end SmoothCompleteFan

namespace LatticePolytope

/-- Lemma 4.2, including every boundary lattice point. The hypotheses are
literal common normal fan and containment of all primitive unit corner boxes. -/
theorem lattice_decomposition_of_unit_corner_boxes {n : ℕ}
    (P Q : LatticePolytope n) (hP : P.UnitCornerBoxes) (hQ : Q.UnitCornerBoxes)
    (hfan : P.SameNormalFan Q) (m : Lattice n)
    (hm : embed n m ∈ P.minkowskiSum Q) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧ x + y = m := by
  have hall : ∀ d : ℕ, UnitBoxDecompositionDimension d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d IH =>
      intro P Q hP hQ hfan m hm
      by_cases hint : embed d m ∈ interior (P.minkowskiSum Q)
      · exact P.interior_lattice_decomposition_of_unit_boxes Q hP.smooth hQ.smooth
          hfan hP hQ m hint
      · obtain ⟨«Σ», hfanP, hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP.smooth
        have hfanQ : «Σ».realCones = Q.normalFan := hfanP.trans hfan
        have he := «Σ».unitBox_integralSupport_sum_eq hpure P Q hfanP hfanQ
        have hmfan := hm
        rw [← he] at hmfan hint
        rw [«Σ».interior_fanPolytope_eq] at hint
        change ¬ ∀ u ∈ «Σ».rays,
          -((P.integralSupport + Q.integralSupport) u : ℝ) <
            (dotProductEquiv ℝ (Fin d) (embed d u)) (embed d m) at hint
        push_neg at hint
        obtain ⟨u, hu, hule⟩ := hint
        have hueq : (dotProductEquiv ℝ (Fin d) (embed d u)) (embed d m) =
            -((P.integralSupport + Q.integralSupport) u : ℝ) :=
          le_antisymm hule (hmfan u hu)
        have hsing := «Σ».singleton_mem_of_mem_rays hu
        obtain ⟨b, I, hI⟩ := «Σ».smooth {u} hsing
        have hF : I.image b ∈ «Σ».cones := hI ▸ hsing
        have hIcard : I.card = 1 := by
          rw [← Finset.card_image_of_injective I b.injective, ← hI, Finset.card_singleton]
        apply «Σ».unit_box_decomposition_at_support_face hpure P Q hP hQ
          hfanP hfanQ b I hF (by omega) m hm ?_ IH
        intro i hi
        have hbi : b i = u := Finset.mem_singleton.mp
          (hI.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        simpa only [hbi] using hueq
  exact hall n P Q hP hQ hfan m hm

/-- The set equality stated in Lemma 4.2. -/
theorem lemma4_2_unit_corner_boxes {n : ℕ}
    (P Q : LatticePolytope n) (hP : P.UnitCornerBoxes) (hQ : Q.UnitCornerBoxes)
    (hfan : P.SameNormalFan Q) :
    {x : Lattice n | embed n x ∈ P.carrier} +
      {y : Lattice n | embed n y ∈ Q.carrier} =
      {m : Lattice n | embed n m ∈ P.minkowskiSum Q} := by
  ext m
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨embed n x, hx, embed n y, hy, (map_add (embed n) x y).symm⟩
  · intro hm
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      P.lattice_decomposition_of_unit_corner_boxes Q hP hQ hfan m hm
    exact ⟨x, hx, y, hy, hxy⟩

end LatticePolytope

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.LatticePolytope.lemma4_2_unit_corner_boxes
