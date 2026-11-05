module

public import PaperVerification.ToricQuotientFaceSupport
public import PaperVerification.ToricDisplacedSupport
public import PaperVerification.ToricStarBoxCoordinates
public import PaperVerification.ToricNefBoxGeometry

@[expose] public section

/-!
# Exact box coordinates in the saturated quotient slice

In a full old normal basis the complementary projected rays are the
standard integral basis.  The quotient tangent coordinates of a sheared
box are its unchanged tangent box coordinates.  These are identities of
actual vectors and affine maps, for arbitrary real normal heights.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

theorem integralDualBasis_standard :
    integralDualBasis (Pi.basisFun ℤ (Fin n)) = Pi.basisFun ℤ (Fin n) := by
  apply DFunLike.ext
  intro i
  funext k
  have hh := integralDualBasis_pairing (Pi.basisFun ℤ (Fin n)) i (Pi.basisFun ℤ (Fin n) k)
  simpa [Pi.basisFun_apply, Pi.single_apply, Module.Basis.repr_self_apply, eq_comm] using hh

theorem integralBasisReal_standard_apply (i : Fin n) :
    integralBasisReal (Pi.basisFun ℤ (Fin n)) i = Pi.basisFun ℝ (Fin n) i := by
  rw [integralBasisReal_apply]
  funext k
  simp [Pi.basisFun_apply, Pi.single_apply, embed]

theorem standard_normal_pairing (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (Pi.basisFun ℤ (Fin n) i))) x = x i := by
  simp [dotProductEquiv, dotProduct, Pi.basisFun_apply, Pi.single_apply, embed]

theorem coneQuotientLattice_complementary_basis
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (j : Fin (n - I.card)) :
    coneQuotientLattice b I (b (complementaryEmbedding I j)) =
      Pi.basisFun ℤ (Fin (n - I.card)) j := by
  funext k
  change b.repr (b (complementaryEmbedding I j)) (complementaryEmbedding I k) = _
  simp only [Module.Basis.repr_self_apply, (complementaryEmbedding I).injective.eq_iff,
    Pi.basisFun_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem quotientFaceMap_complementary_coordinate (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) (j : Fin (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) (embed n (b (complementaryEmbedding I j))))
      (quotientFaceMap a b I x) = x j := by
  rw [normal_pairing_eq_dual_coordinate, quotientFaceMap_apply,
    map_add, Finsupp.add_apply, quotientFaceOrigin_coordinate]
  have hj : complementaryEmbedding I j ∉ I :=
    (mem_range_complementaryEmbedding_iff I _).mp ⟨j, rfl⟩
  rw [if_neg hj, zero_add]
  exact selectedBasisMap_coordinate (integralBasisReal (integralDualBasis b))
    (complementaryEmbedding I) x j

def normalHeight (δ : Ambient n) : Lattice n → ℝ :=
  fun u => (dotProductEquiv ℝ (Fin n) (embed n u)) δ

theorem normalHeight_basis (δ : Ambient n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    normalHeight δ (b i) = (integralBasisReal (integralDualBasis b)).coord i δ :=
  normal_pairing_eq_dual_coordinate b i δ

theorem normalHeight_sum_image (δ : Ambient n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    (∑ u ∈ I.image b, normalHeight δ u) =
      ∑ i ∈ I, (integralBasisReal (integralDualBasis b)).coord i δ := by
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun i hi => normalHeight_basis δ b i)
  · exact fun i _ j _ hij => b.injective hij

def tangentSliceCoordinates (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (δ : Ambient n) : Ambient (n - I.card) :=
  fun j => -a (b (complementaryEmbedding I j)) + normalHeight δ (b (complementaryEmbedding I j))

/-- A displacement with its actual old normal heights has exactly these
affine tangent coordinates in the saturated face chart. -/
theorem quotientFaceMap_tangentSliceCoordinates
    (a : Lattice n → ℝ) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (v δ : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -a (b i)) :
    quotientFaceMap (displacedSupport a (I.image b) (normalHeight δ)) b I
      (tangentSliceCoordinates a b I δ) = v + δ := by
  apply (integralBasisReal (integralDualBasis b)).ext_elem
  intro i
  rw [← normal_pairing_eq_dual_coordinate, ← normal_pairing_eq_dual_coordinate]
  by_cases hi : i ∈ I
  · rw [quotientFaceMap_active _ b I _ i hi, map_add, hv i]
    have hbi : b i ∈ I.image b := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos hbi, normalHeight]
    ring
  · obtain ⟨j, hj⟩ := (mem_range_complementaryEmbedding_iff I i).mpr hi
    rw [← hj, quotientFaceMap_complementary_coordinate, map_add, hv]
    rfl

/-- The shear changes no tangent coordinate, including its base shift. -/
theorem tangentSliceCoordinates_shifted_star_box
    (a : Lattice n → ℝ) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I)
    (t : ℝ) («λ» : Fin n → ℝ) :
    tangentSliceCoordinates a b I
      (t • integralBasisReal (integralDualBasis b) j +
        ∑ k, «λ» k • starShearBasis (integralBasisReal (integralDualBasis b)) I j k) =
      fun k => -a (b (complementaryEmbedding I k)) + «λ» (complementaryEmbedding I k) := by
  funext k
  have hk : complementaryEmbedding I k ∉ I :=
    (mem_range_complementaryEmbedding_iff I _).mp ⟨k, rfl⟩
  have hkj : complementaryEmbedding I k ≠ j := fun hh => hk (hh.symm ▸ hj)
  simp only [tangentSliceCoordinates, normalHeight, normal_pairing_eq_dual_coordinate]
  rw [show (integralBasisReal (integralDualBasis b)).repr _ (complementaryEmbedding I k) =
      (integralBasisReal (integralDualBasis b)).coord (complementaryEmbedding I k) _ from rfl,
    coord_shifted_star_box, if_neg hkj, add_zero]

/-- Inner unit boxes start at old normal height at least one. The upper
normal budget is exactly `t+2`, with no rounding of real coordinates. -/
theorem shifted_inner_star_box_normal_heights
    (B : Module.Basis (Fin n) ℝ (Ambient n)) (I : Finset (Fin n))
    (j : Fin n) (hj : j ∈ I) (t : ℝ)
    (ht : 2 * (I.card - 1 : ℕ) ≤ t)
    («λ» : Fin n → ℝ) («hλ» : ∀ i, 0 ≤ «λ» i ∧ «λ» i ≤ 1) :
    let δ := t • B j + ∑ k, (1 + «λ» k) • starShearBasis B I j k
    (∀ i ∈ I, 1 ≤ B.coord i δ) ∧
      t + 1 ≤ ∑ i ∈ I, B.coord i δ ∧
      (∑ i ∈ I, B.coord i δ) ≤ t + 2 := by
  dsimp only
  have hsum : (∑ k ∈ I.erase j, (1 + «λ» k)) ≤ 2 * (I.card - 1 : ℕ) := by
    calc
      (∑ k ∈ I.erase j, (1 + «λ» k)) ≤ ∑ _k ∈ I.erase j, (2 : ℝ) :=
        Finset.sum_le_sum (fun k hk => by have hh := («hλ» k).2; linarith)
      _ = 2 * (I.card - 1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj]
        ring
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [coord_shifted_star_box]
    by_cases hij : i = j
    · rw [if_pos hij]
      have hh := («hλ» i).1
      linarith
    · rw [if_neg hij, add_zero]
      exact le_add_of_nonneg_right («hλ» i).1
  · rw [sum_normal_coords_shifted_star_box B I j hj]
    have hh := («hλ» j).1
    linarith
  · rw [sum_normal_coords_shifted_star_box B I j hj]
    have hh := («hλ» j).2
    linarith

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem quotient_of_full_basis_standard_cone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) :
    let hF := «Σ».downward _ hfull (I.image b) (Finset.image_subset_image (Finset.subset_univ I))
    Finset.univ.image (Pi.basisFun ℤ (Fin (n - I.card))) ∈
      («Σ».completeQuotientStarFan b I hF).cones := by
  dsimp only
  apply («Σ».mem_quotientStarCones b I _).mpr
  refine ⟨Finset.univ.image b, hfull,
    Finset.image_subset_image (Finset.subset_univ I), ?_⟩
  ext u
  constructor
  · intro hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨b (complementaryEmbedding I j), ?_,
      coneQuotientLattice_complementary_basis b I j⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    intro hh
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hh
    have hkj := b.injective he
    exact ((mem_range_complementaryEmbedding_iff I _).mp ⟨j, rfl⟩) (hkj ▸ hk)
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hv).1
    have hiI : i ∉ I := fun hh => (Finset.mem_sdiff.mp hv).2
      (Finset.mem_image.mpr ⟨i, hh, rfl⟩)
    obtain ⟨j, hj⟩ := (mem_range_complementaryEmbedding_iff I i).mpr hiI
    rw [← hj, coneQuotientLattice_complementary_basis]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

theorem faceSupport_displaced_standard_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hfull : Finset.univ.image b ∈ «Σ».cones) (hF : I.image b ∈ «Σ».cones)
    (a : Lattice n → ℝ) (h : Lattice n → ℝ) (j : Fin (n - I.card)) :
    «Σ».faceSupport b I hF (displacedSupport a (I.image b) h)
      (Pi.basisFun ℤ (Fin (n - I.card)) j) = a (b (complementaryEmbedding I j)) := by
  have hj : complementaryEmbedding I j ∉ I :=
    (mem_range_complementaryEmbedding_iff I _).mp ⟨j, rfl⟩
  have hvN : b (complementaryEmbedding I j) ∉ I.image b := by
    intro hh
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hh
    exact hj (b.injective he ▸ hk)
  have hv : b (complementaryEmbedding I j) ∈ (Finset.univ.image b) \ I.image b :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, hvN⟩
  rw [← coneQuotientLattice_complementary_basis b I j,
    «Σ».faceSupport_projected b I hF _ hfull
      (Finset.image_subset_image (Finset.subset_univ I)) hv,
    normal_pairing_eq_dual_coordinate, quotientFaceOrigin_coordinate, if_neg hj, add_zero]
  simp only [displacedSupport, Pi.sub_apply, facetWeight, if_neg hvN, sub_zero]

/-- A corner-box criterion in explicitly chosen primitive normal
coordinates, without any dependence on a chosen enumeration of the full
cone by `fullConeBasis`. -/
theorem corner_box_at_normal_basis
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      side * Q.fiberDimension ≤ Q.degree a)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : Finset.univ.image b ∈ «Σ».cones)
    (v : Ambient n) (hv : ∀ i,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -a (b i))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis b) i ∈ «Σ».fanPolytope a := by
  apply «Σ».box_mem_fanPolytope_of_vertices a v _ side hside ?_ t ht
  intro I
  let F := a - side • (fun u => if u ∈ I.image b then 1 else 0)
  have hF : «Σ».IsNef F := «Σ».nef_sub_cone_selection_of_contractible_degrees hpure H hH
    a side hside hdegree hb (Finset.image_subset_image (Finset.subset_univ I))
  apply «Σ».box_corner_mem_of_refinement_nef «Σ» (Finset.Subset.refl _) a F hF b hb v hv I side
  · intro i
    simp only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mem_image, b.injective.eq_iff]
    simp
  · intro u hu
    change a u - side * (if u ∈ I.image b then 1 else 0) ≤ a u
    split_ifs <;> nlinarith

theorem coordinate_box_mem_fanPolytope
    (hpure : «Σ».IsPure) (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      side * Q.fiberDimension ≤ Q.degree a)
    (hstandard : Finset.univ.image (Pi.basisFun ℤ (Fin n)) ∈ «Σ».cones)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    (fun i => -a (Pi.basisFun ℤ (Fin n) i) + t i) ∈ «Σ».fanPolytope a := by
  have hh := «Σ».corner_box_at_normal_basis hpure H hH a side hside hdegree
    (Pi.basisFun ℤ (Fin n)) hstandard
    (fun i => -a (Pi.basisFun ℤ (Fin n) i)) (by intro i; rw [standard_normal_pairing]) t ht
  rw [integralDualBasis_standard] at hh
  simp only [integralBasisReal_standard_apply] at hh
  have he : (∑ i, t i • Pi.basisFun ℝ (Fin n) i) = t := by
    funext k
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [he] at hh
  exact hh

end SmoothCompleteFan

end PaperVerification.ToricGeometry
