module

public import paper_verification.toric019

@[expose] public section

/-!
# The full numerical corner-box criterion

The forward implication needs inequalities only on extremal primitive
relations. The converse evaluates an actual missing-ray facet inequality
at an actual corner of a contained box and applies to every combinatorially
contractible primitive relation. Supports and box coordinates are real.

The explicit purity and integral strict-support hypotheses in the forward
direction are the fan data already constructed for the paper's projective
polytopes. The converse does not need a projectivity witness or nefness.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Literal containment of every point of every real corner box in the
actual primitive-ray halfspace polytope. No degree condition is part of
this definition. -/
def ContainsCornerBoxes (a : Lattice n → ℝ) (side : ℝ) : Prop :=
  ∀ (s : «Σ».fullCones) (t : Fin n → ℝ),
    (∀ i, 0 ≤ t i ∧ t i ≤ side) →
      «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a

/-- The forward direction of Lemma 3.1 uses only the manuscript's
extremal-relation inequalities. It also allows nef degenerate endpoints. -/
theorem containsCornerBoxes_of_extremal_degrees
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal →
      side * R.fiberDimension ≤ R.degree a) :
    «Σ».ContainsCornerBoxes a side := by
  intro s t ht
  apply «Σ».corner_box_mem_fanPolytope_of_vertices a _ _ side ?_ t ht
  intro I
  apply «Σ».corner_vertex_mem_fanPolytope s I side hside
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
  intro R hR
  apply R.degree_sub_corner_selection_nonneg («Σ».fullCones_mem s) ?_
    a side hside (hdegree R hR)
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.subset_univ I)

/-- The converse direction of Lemma 3.1. At a full cone over the negative
focus, select the `r` positive directions of the relation. The omitted
positive ray has coefficient `−1` on each selected direction, so its facet
slack at this actual box corner is `R.degree a − side * r`. -/
theorem contractible_degree_lower_of_cornerBoxes
    (hpure : «Σ».IsPure) (a : Lattice n → ℝ)
    (side : ℝ) (hside : 0 ≤ side) (hboxes : «Σ».ContainsCornerBoxes a side)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible) :
    side * R.fiberDimension ≤ R.degree a := by
  obtain ⟨U, hUcone, hNU, hUcard⟩ := hpure R.negative R.negative_cone
  let s : «Σ».fullCones := ⟨U, Finset.mem_filter.mpr ⟨hUcone, hUcard⟩⟩
  let b := «Σ».fullConeBasis s
  have hU : U = Finset.univ.image b := «Σ».fullConeBasis_ray_set s
  obtain ⟨w, hw, hPdiff⟩ :=
    R.exists_unique_omitted_positive hR hUcone hUcard hNU
  have hwU : w ∉ U := by
    have hh := hPdiff.symm ▸ Finset.mem_singleton_self w
    exact (Finset.mem_sdiff.mp hh).2
  let I : Finset (Fin n) := Finset.univ.filter (fun i => b i ∈ R.positive)
  have himage : I.image b = R.positive ∩ U := by
    ext u
    constructor
    · intro hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2,
        hU.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    · intro hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hU ▸ (Finset.mem_inter.mp hu).2)
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_inter.mp hu).1⟩, rfl⟩
  have hcardI : I.card = R.fiberDimension := by
    calc
      I.card = (I.image b).card := (Finset.card_image_of_injective _ b.injective).symm
      _ = (R.positive ∩ U).card := congrArg Finset.card himage
      _ = R.fiberDimension := R.positive_count_in_full_cone hR hUcone hUcard hNU
  let v := «Σ».cartierPoint a s
  let ℓ : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) v)
  have hpair (u : Lattice n) :
      ℓ (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) v := by
    change -(v ⬝ᵥ embed n u) = -(embed n u ⬝ᵥ v)
    rw [dotProduct_comm]
  have hsupport (u : Lattice n) (hu : u ∈ U) : ℓ (embed n u) = a u := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hU ▸ hu)
    rw [hpair]
    have hh := «Σ».cartierPoint_active a s i
    change (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -a (b i) at hh
    rw [hh, neg_neg]
  have hdegree : R.degree a = a w - ℓ (embed n w) := by
    rw [R.degree_eq_sum_slack a ℓ (fun u hu => hsupport u (hNU hu))]
    refine Finset.sum_eq_single w ?_ ?_
    · intro u hu huw
      have huU : u ∈ U := by
        by_contra hnot
        have hh : u ∈ R.positive \ U := Finset.mem_sdiff.mpr ⟨hu, hnot⟩
        rw [hPdiff] at hh
        exact huw (Finset.mem_singleton.mp hh)
      exact sub_eq_zero.mpr (hsupport u huU).symm
    · intro hnot
      exact False.elim (hnot hw)
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n w)
  have hf (i : Fin n) (hi : i ∈ I) : f («Σ».cartierBasis s i) = -1 := by
    have hc : b.repr w i = -1 :=
      (R.positive_iff_omitted_coordinate_neg_one b U hU hNU w hw hwU hPdiff i).mp
        (Finset.mem_filter.mp hi).2
    change (dotProductEquiv ℝ (Fin n) (embed n w))
      (integralBasisReal (integralDualBasis b) i) = -1
    rw [pairing_integral_dual_basis, hc]
    norm_num
  let t : Fin n → ℝ := fun i => if i ∈ I then side else 0
  have ht (i : Fin n) : 0 ≤ t i ∧ t i ≤ side := by
    by_cases hi : i ∈ I <;> simp [t, hi, hside]
  have hsum : f (∑ i, t i • «Σ».cartierBasis s i) =
      -side * R.fiberDimension := by
    simp only [map_sum, map_smul, smul_eq_mul]
    have hreduce : (∑ i, t i * f («Σ».cartierBasis s i)) =
        ∑ i ∈ I, side * f («Σ».cartierBasis s i) := by
      simp only [t, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hreduce]
    calc
      (∑ i ∈ I, side * f («Σ».cartierBasis s i)) = ∑ i ∈ I, side * (-1) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun z : ℝ => side * z) (hf i hi))
      _ = -side * R.fiberDimension := by simp [hcardI, mul_comm]
  have hmem := hboxes s t ht
  have hfacet : -a w ≤ f (v + ∑ i, t i • «Σ».cartierBasis s i) :=
    hmem w (R.primitive.1 hw)
  have hdegree' : R.degree a = a w + f v := by
    rw [hdegree, hpair, sub_neg_eq_add]
  rw [map_add, hsum] at hfacet
  linarith

/-- Equivalence with all contractible numerical inequalities. The two
directions refer to the same actual real support and its actual boxes. -/
theorem containsCornerBoxes_iff_contractible_degrees
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side) :
    «Σ».ContainsCornerBoxes a side ↔
      ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
        side * R.fiberDimension ≤ R.degree a := by
  constructor
  · intro h R hR
    exact «Σ».contractible_degree_lower_of_cornerBoxes hpure a side hside h R hR
  · intro h s t ht
    exact «Σ».corner_box_mem_fanPolytope hpure H hH a side hside h s t ht

/-- The extremal inequalities suffice and are also necessary, since
extremal primitive relations are proved combinatorially contractible. -/
theorem containsCornerBoxes_iff_extremal_degrees
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side) :
    «Σ».ContainsCornerBoxes a side ↔
      ∀ R : «Σ».PrimitiveRelation, R.IsExtremal →
        side * R.fiberDimension ≤ R.degree a := by
  constructor
  · intro h R hR
    exact «Σ».contractible_degree_lower_of_cornerBoxes hpure a side hside h R
      (R.combinatoriallyContractible_of_extremal hR)
  · exact «Σ».containsCornerBoxes_of_extremal_degrees hpure H hH a side hside

end PaperVerification.ToricGeometry.SmoothCompleteFan
