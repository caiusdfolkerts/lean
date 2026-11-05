module
public import PaperVerification.ToricFaceCoordinates
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
@[expose] public section
/-!
# Face coordinates for smooth lattice polytopes

The coordinate support of a face is determined by the incident edge rays that
remain in that face. This gives a coordinate sublattice of an actual integral
basis, hence a saturated lattice, without assuming a face-inheritance theorem.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical
open Set
open PaperVerification.ToricExchange

section AffineCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem affine_apply_add_smul (f : E →ᵃ[ℝ] ℝ) (v w : E) (a : ℝ) :
    f (v + a • w) = f v + a * f.linear w := by
  rw [add_comm]
  change f ((a • w) +ᵥ v) = _
  rw [AffineMap.map_vadd]
  simp [map_smul, vadd_eq_add, smul_eq_mul, add_comm]

theorem affine_apply_basis_coordinates (f : E →ᵃ[ℝ] ℝ)
    (b : Module.Basis ι ℝ E) (v x : E) :
    f x = f v + ∑ i, b.repr (x - v) i * f.linear (b i) := by
  have hx : x = (∑ i, b.repr (x - v) i • b i) +ᵥ v := by
    rw [b.sum_repr]
    simp
  calc
    f x = f ((∑ i, b.repr (x - v) i • b i) +ᵥ v) := congrArg f hx
    _ = _ := by
      rw [AffineMap.map_vadd]
      simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]

/-- A positive basis coordinate of a point on a face forces that edge ray
to remain in the same face. The proof uses actual affine slacks and their
nonnegative weighted sum, rather than a combinatorial face assumption. -/
theorem positive_coordinate_endpoint_mem_face {κ : Type*}
    (H : AffineInequalities κ E) (J : Set κ)
    (b : Module.Basis ι ℝ E) (v : E) (hv : v ∈ H.face J)
    (lengths : ι → ℝ) (hlength : ∀ i, 0 < lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ H.region)
    (hcone : ∀ x ∈ H.region, ∀ i, 0 ≤ b.repr (x - v) i)
    (x : E) (hx : x ∈ H.face J) (i : ι) (hi : 0 < b.repr (x - v) i) :
    v + lengths i • b i ∈ H.face J := by
  refine ⟨hedges i, ?_⟩
  intro k hk
  have hv0 : H.slack k v = 0 := hv.2 k hk
  have hx0 : H.slack k x = 0 := hx.2 k hk
  have hcoef (j : ι) : 0 ≤ (H.slack k).linear (b j) := by
    have hj := hedges j k
    rw [affine_apply_add_smul, hv0, zero_add] at hj
    exact nonneg_of_mul_nonneg_right hj (hlength j)
  have hterms (j : ι) :
      0 ≤ b.repr (x - v) j * (H.slack k).linear (b j) :=
    mul_nonneg (hcone x hx.1 j) (hcoef j)
  have hsum : (∑ j, b.repr (x - v) j * (H.slack k).linear (b j)) = 0 := by
    have h := affine_apply_basis_coordinates (H.slack k) b v x
    rw [hv0, hx0, zero_add] at h
    exact h.symm
  have hle : b.repr (x - v) i * (H.slack k).linear (b i) ≤ 0 := by
    have h := Finset.single_le_sum (f := fun j =>
      b.repr (x - v) j * (H.slack k).linear (b j)) (fun j _ => hterms j)
      (Finset.mem_univ i)
    rwa [hsum] at h
  have hzero := le_antisymm hle (hterms i)
  have hlin : (H.slack k).linear (b i) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hi.ne'
  rw [affine_apply_add_smul, hv0, hlin, mul_zero, add_zero]

end AffineCoordinates

/-- The origin together with one nonzero point on every coordinate axis
affinely spans the full coordinate space, including dimension zero. -/
theorem affineSpan_eq_top_of_scaled_axes {d : ℕ} (S : Set (Ambient d))
    (hzero : (0 : Ambient d) ∈ S) (lengths : Fin d → ℝ)
    (hlength : ∀ i, lengths i ≠ 0)
    (haxes : ∀ i, lengths i • Pi.basisFun ℝ (Fin d) i ∈ S) :
    affineSpan ℝ S = ⊤ := by
  have hspan : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℝ (Fin d)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi := (Submodule.span ℝ S).smul_mem (lengths i)⁻¹
      (Submodule.subset_span (haxes i))
    simpa [smul_smul, hlength i] using hi
  rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ S hzero)]
  rw [hspan] <;> rfl

/-- Indices of the incident basis directions whose endpoints lie on a specified face. -/
def faceEdgeIndices {n : ℕ} (F : Set (Ambient n)) (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (lengths : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => v + lengths i • b i ∈ F)

@[simp] theorem mem_faceEdgeIndices {n : ℕ} (F : Set (Ambient n)) (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (lengths : Fin n → ℝ) (i : Fin n) :
    i ∈ faceEdgeIndices F v b lengths ↔ v + lengths i • b i ∈ F := by
  classical
  simp [faceEdgeIndices]

/-- An actual nonempty face in a supporting basis orthant is exactly the
coordinate section obtained by setting its omitted edge coordinates to zero. -/
theorem face_eq_coordinate_section {n : ℕ} {κ : Type*} [Finite κ]
    (H : AffineInequalities κ (Ambient n)) (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ H.region F)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v : Ambient n) (hv : v ∈ F)
    (lengths : Fin n → ℝ) (hlength : ∀ i, 0 < lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ H.region)
    (hcone : ∀ x ∈ H.region, ∀ i, 0 ≤ b.repr (x - v) i) :
    F = {x ∈ H.region | ∀ i ∉ faceEdgeIndices F v b lengths,
      b.repr (x - v) i = 0} := by
  classical
  obtain ⟨z, hz, hFeq⟩ := H.exists_activeFace_eq hFconv hF ⟨v, hv⟩
  let J := H.jointZeros z z
  have hvJ : v ∈ H.face J := by simpa only [hFeq] using hv
  ext x
  constructor
  · intro hx
    refine ⟨hF.subset hx, ?_⟩
    intro i hi
    have hnonneg := hcone x (hF.subset hx) i
    by_contra hne
    have hpos : 0 < b.repr (x - v) i := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hxJ : x ∈ H.face J := by simpa only [hFeq] using hx
    have hiJ := positive_coordinate_endpoint_mem_face H J b v hvJ lengths hlength
      hedges hcone x hxJ i hpos
    apply hi
    apply (mem_faceEdgeIndices F v b lengths i).mpr
    simpa only [hFeq] using hiJ
  · rintro ⟨hxP, hxzero⟩
    rw [hFeq]
    refine ⟨hxP, ?_⟩
    intro k hk
    have hv0 : H.slack k v = 0 := hvJ.2 k hk
    have hterm (i : Fin n) :
        b.repr (x - v) i * (H.slack k).linear (b i) = 0 := by
      by_cases hi : i ∈ faceEdgeIndices F v b lengths
      · have hwi : v + lengths i • b i ∈ H.face J := by
          have hiF := (mem_faceEdgeIndices F v b lengths i).mp hi
          simpa only [hFeq] using hiF
        have hzero := hwi.2 k hk
        rw [affine_apply_add_smul, hv0, zero_add] at hzero
        have hlin := (mul_eq_zero.mp hzero).resolve_left (hlength i).ne'
        rw [hlin, mul_zero]
      · rw [hxzero i hi, zero_mul]
    rw [affine_apply_basis_coordinates (H.slack k) b v x, hv0]
    simp only [hterm, Finset.sum_const_zero, add_zero]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A convex face is generated by the original integral generators it contains. -/
theorem face_eq_hull_lattice_filter (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) :
    F = convexHull ℝ ((embed n) ''
      ((P.generators.filter fun z => embed n z ∈ F) : Set (Lattice n))) := by
  classical
  let s := P.generators.image (embed n)
  have hs : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have h := convex_face_eq_convexHull_filter s F hFconv (by simpa only [hs] using hF)
  calc
    F = convexHull ℝ (faceGenerators s F : Set (Ambient n)) := h
    _ = _ := by
      congr 1
      ext x
      simp only [faceGenerators, Finset.mem_coe, Finset.mem_filter, Finset.mem_image,
        Set.mem_image, s]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hx⟩
        exact ⟨z, ⟨hz, hx⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hx⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, hx⟩

/-- Every nonempty actual convex face has an actual vertex. -/
theorem face_vertices_nonempty (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) (hFne : F.Nonempty) :
    (F.extremePoints ℝ).Nonempty := by
  have hcompact : IsCompact F := by
    rw [P.face_eq_hull_lattice_filter F hFconv hF]
    exact ((P.generators.filter fun z => embed n z ∈ F).finite_toSet.image
      (embed n)).isCompact_convexHull ℝ
  exact hcompact.extremePoints_nonempty hFne

/-- Supporting basis coordinates follow from the complete list of actual
incident edges. This form retains a specified primitive basis. -/
theorem basis_cone_of_incident_edges (v : Ambient n)
    (hv : v ∈ P.carrier.extremePoints ℝ) (vZ : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hvZ : embed n vZ = v)
    (hall : ∀ w, P.IsEdge v w →
      ∃ i, w = embed n (vZ + (lengths i : ℤ) • b i)) :
    ∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i := by
  classical
  let s := P.generators.image (embed n)
  have hs : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hs] using hv
  have hedgeRay : ∀ w : Ambient n, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Ambient n))) (segment ℝ v w) →
      ∃ i : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • integralBasisReal b i := by
    intro w hvw hface
    obtain ⟨i, rfl⟩ := hall w ⟨hvw, by simpa only [hs] using hface⟩
    refine ⟨i, (lengths i : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [map_add, hvZ, integralBasisReal_apply, add_sub_cancel_left]
    ext j
    simp [embed, Int.cast_mul]
  have h := PaperVerification.ToricVertexCone.nonnegative_basis_coordinates_of_incident_edges
    s v hv' (integralBasisReal b) hedgeRay
  simpa only [hs] using h

/-- Every face, at every one of its vertices, has saturated integral coordinates
in which its complete incident edge family consists of the standard coordinate
axes. Its coordinate polytope is full dimensional; a proper face has strictly
smaller dimension. No face-smoothness theorem is assumed. -/
theorem exists_face_chart_at_vertex (hP : P.Smooth)
    (F : Set (Ambient n)) (hFconv : Convex ℝ F)
    (hF : IsExtreme ℝ P.carrier F) (v : Ambient n)
    (hv : v ∈ F.extremePoints ℝ) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
      (lengths : Fin d → ℕ),
      d ≤ n ∧ (F ≠ P.carrier → d < n) ∧
      e.realMap 0 = v ∧ e.realMap '' Q.carrier = F ∧
      (∀ i, 0 < lengths i ∧ Q.IsEdge 0
        (embed d ((lengths i : ℤ) • Pi.basisFun ℤ (Fin d) i))) ∧
      (∀ w, Q.IsEdge 0 w → ∃ i,
        w = embed d ((lengths i : ℤ) • Pi.basisFun ℤ (Fin d) i)) := by
  classical
  have hvP := hF.extremePoints_subset_extremePoints hv
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hvP
  let bR := integralBasisReal b
  let lR : Fin n → ℝ := fun i => lengths i
  have hlR (i : Fin n) : 0 < lR i := by
    change (0 : ℝ) < (lengths i : ℝ)
    exact_mod_cast (hedges i).1
  have hendpoint (i : Fin n) :
      embed n (vZ + (lengths i : ℤ) • b i) = v + lR i • bR i := by
    rw [map_add, hvZ]
    ext j
    simp [lR, bR, integralBasisReal_apply, embed, Int.cast_mul]
  have hcone := P.basis_cone_of_incident_edges v hvP vZ b lengths hvZ hall
  obtain ⟨κ, hκ, H, hHP⟩ := P.hasFiniteHalfspaces
  letI := hκ
  let I := faceEdgeIndices F v bR lR
  have hsection : F = {x ∈ P.carrier | ∀ i ∉ I, bR.repr (x - v) i = 0} := by
    have h := face_eq_coordinate_section H F hFconv
      (by simpa only [← hHP] using hF) bR v hv.1 lR hlR
      (fun i => by
        rw [← hHP, ← hendpoint]
        exact (P.edge_endpoints_extreme (hedges i).2).2.1)
      (by simpa only [← hHP] using hcone)
    simpa only [← hHP, I] using h
  let d := I.card
  let a : Fin d ↪ Fin n := (I.orderEmbOfFin rfl).toEmbedding
  have harange : Set.range a = (I : Set (Fin n)) := by
    exact Finset.range_orderEmbOfFin I rfl
  have haI (i : Fin d) : a i ∈ I := by
    change a i ∈ (I : Set (Fin n))
    rw [← harange]
    exact Set.mem_range_self i
  let e := selectedBasisChart vZ b a
  let proj : Lattice n → Lattice d := fun z i => b.repr (z - vZ) (a i)
  let S := P.generators.filter (fun z => embed n z ∈ F)
  let qgens := S.image proj
  let Qset := convexHull ℝ ((embed d) '' (qgens : Set (Lattice d)))
  have hcoord (x : Ambient n) (hx : x ∈ F) :
      ∀ j ∉ Set.range a, bR.repr (x - v) j = 0 := by
    have hx' : x ∈ {x ∈ P.carrier | ∀ i ∉ I, bR.repr (x - v) i = 0} := by
      rwa [← hsection]
    intro j hj
    exact hx'.2 j (by simpa only [harange, Finset.mem_coe] using hj)
  have hreconstruct (z : Lattice n) (hz : embed n z ∈ F) : e.latticeMap (proj z) = z := by
    have hz0 (j : Fin n) (hj : j ∉ Set.range a) : b.repr (z - vZ) j = 0 := by
      have h := hcoord (embed n z) hz j hj
      rw [← hvZ, ← map_sub, integralBasisReal_repr] at h
      exact Int.cast_eq_zero.mp h
    change vZ + selectedBasisMap b a (fun i => b.repr (z - vZ) (a i)) = z
    rw [selectedBasisMap_repr_restrict b a (z - vZ) hz0]
    abel
  have hgenimage : e.realMap '' ((embed d) '' (qgens : Set (Lattice d))) =
      (embed n) '' (S : Set (Lattice n)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
      rw [← e.embed_latticeMap, hreconstruct z (Finset.mem_filter.mp hz).2]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨embed d (proj z), ⟨proj z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [← e.embed_latticeMap, hreconstruct z (Finset.mem_filter.mp hz).2]
  have himage : e.realMap '' Qset = F := by
    rw [e.realMap.image_convexHull, hgenimage]
    exact (P.face_eq_hull_lattice_filter F hFconv hF).symm
  have hezero : e.realMap 0 = v := by
    simp only [e, selectedBasisChart_realMap, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, hvZ]
  have hmem (x : Ambient d) : x ∈ Qset ↔ e.realMap x ∈ F := by
    rw [← himage]
    exact e.realMap_injective.mem_set_image.symm
  have hzero : (0 : Ambient d) ∈ Qset := (hmem 0).mpr (hezero.symm ▸ hv.1)
  have heaxis (i : Fin d) : e.realMap
      ((lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i) =
        embed n (vZ + (lengths (a i) : ℤ) • b (a i)) := by
    change embed n vZ + selectedBasisMap bR a
      ((lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i) = _
    rw [map_smul]
    have hsingle : selectedBasisMap bR a (Pi.basisFun ℝ (Fin d) i) = bR (a i) := by
      simpa only [Pi.basisFun_apply, selectedBasisMap_single, one_smul]
        using selectedBasisMap_single bR a i (1 : ℝ)
    rw [hsingle, hvZ, hendpoint]
  have haxes (i : Fin d) :
      (lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i ∈ Qset := by
    apply (hmem _).mpr
    rw [heaxis, hendpoint]
    exact (mem_faceEdgeIndices F v bR lR (a i)).mp (haI i)
  have hfull : affineSpan ℝ Qset = ⊤ :=
    affineSpan_eq_top_of_scaled_axes Qset hzero (fun i => lengths (a i))
      (fun i => (hlR (a i)).ne') haxes
  have hqne : qgens.Nonempty := by
    obtain ⟨x, hx⟩ := convexHull_nonempty_iff.mp ⟨0, hzero⟩
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq⟩
  let Q : LatticePolytope d := ⟨qgens, hqne, hfull⟩
  have hQset : Q.carrier = Qset := rfl
  have hd : d ≤ n := by
    calc
      d = I.card := rfl
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ I)
      _ = n := Finset.card_fin n
  have hdstrict (hproper : F ≠ P.carrier) : d < n := by
    apply lt_of_le_of_ne hd
    intro hdn
    have hI : I = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ I)
      (by simpa only [Finset.card_fin, ← hdn] using (le_rfl : I.card ≤ I.card))
    apply hproper
    rw [hsection, hI]
    simp
  have heembedaxis (i : Fin d) :
      e.realMap (embed d ((lengths (a i) : ℤ) • Pi.basisFun ℤ (Fin d) i)) =
      embed n (vZ + (lengths (a i) : ℤ) • b (a i)) := by
    rw [← e.embed_latticeMap]
    congr 1
    change vZ + selectedBasisMap b a
      ((lengths (a i) : ℤ) • Pi.basisFun ℤ (Fin d) i) = _
    rw [map_smul]
    have hs : selectedBasisMap b a (Pi.basisFun ℤ (Fin d) i) = b (a i) := by
      simpa only [Pi.basisFun_apply, selectedBasisMap_single, one_smul]
        using selectedBasisMap_single b a i (1 : ℤ)
    rw [hs]
  refine ⟨d, Q, e, fun i => lengths (a i), hd, hdstrict, hezero, himage, ?_, ?_⟩
  · intro i
    refine ⟨(hedges (a i)).1, ?_, ?_⟩
    · intro heq
      have h := congrArg e.realMap heq
      rw [hezero, heembedaxis] at h
      exact (hedges (a i)).2.1 h
    · apply (affine_isExtreme_image_iff e.realMap e.realMap_injective _ _).mp
      rw [hQset, himage, image_segment, hezero, heembedaxis]
      apply (hedges (a i)).2.2.mono hF.subset
      apply hFconv.segment_subset hv.1
      rw [hendpoint]
      exact (mem_faceEdgeIndices F v bR lR (a i)).mp (haI i)
  · intro w hw
    have hwF : e.realMap w ∈ F := by
      rw [← himage]
      exact ⟨w, (Q.edge_endpoints_extreme hw).2.1, rfl⟩
    have hedgeP : P.IsEdge v (e.realMap w) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw.1
        apply e.realMap_injective
        simpa only [hezero] using h
      · have h := affine_isExtreme_image e.realMap e.realMap_injective hw.2
        rw [hQset, himage, image_segment, hezero] at h
        exact hF.trans h
    obtain ⟨j, hj⟩ := hall (e.realMap w) hedgeP
    have hjI : j ∈ I := by
      apply (mem_faceEdgeIndices F v bR lR j).mpr
      rw [← hendpoint, ← hj]
      exact hwF
    have hjrange : j ∈ Set.range a := by rwa [harange]
    obtain ⟨i, rfl⟩ := hjrange
    refine ⟨i, e.realMap_injective ?_⟩
    rw [heembedaxis]
    exact hj

end LatticePolytope

end PaperVerification.ToricGeometry
