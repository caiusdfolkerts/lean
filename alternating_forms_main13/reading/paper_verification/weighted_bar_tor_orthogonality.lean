module

public import PaperVerification.WeightedBarTor

/-!
# Orthogonal original-degree summands in ordinary augmentation Tor

The actual chain-level degree projections split the inclusions and kill
all other internal degrees. Their transported maps on ordinary Tor prove
disjointness of distinct degree summands. Together with the already proved
exhaustion, diagonal concentration is equivalent to the diagonal summand
being the whole Tor module. The zeroth off-diagonal summands vanish directly
because the unique length-zero word has original degree zero.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.WeightedBar

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PaperVerification.NoncommutativeBar PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "internal" => internalComplex ε B hunit hε δ hδ

theorem internalProjection_inclusion_of_ne (r N M : ℕ) (hMN : M≠N)
    (z : piece (K := K) δ r M) :
    internalProjection δ r N (internalInclusion δ r M z)=0 := by
  apply Subtype.ext
  change degreeProjection δ N z.val=0
  have hz : z.val∈lengthPiece I K r ⊓ degreePiece δ M := by
    rw [←piece_eq_inf]
    exact z.property
  exact (degreeProjection_homogeneous δ N M z.val hz.2).trans (if_neg hMN)

theorem inclusion_projection_eq_zero (N M : ℕ) (hMN : M≠N) :
    inclusionChain ε B hunit hε δ hδ M ≫
      projectionChain ε B hunit hε δ hδ N=0 := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact internalProjection_inclusion_of_ne δ r N M hMN z

/-- Projection from actual ordinary Tor to its original internal degree. -/
def torProjection (r N : ℕ) :
    AugmentationCoinvariants.augmentationTor ε r ⟶ (internal N).homology r :=
  (ordinaryTorReducedBarIso ε B hunit hε r).hom ≫
    homologyMap (projectionChain ε B hunit hε δ hδ N) r

theorem internalTorMap_projection (r N : ℕ) :
    internalTorMap ε B hunit hε δ hδ r N ≫
      torProjection ε B hunit hε δ hδ r N=𝟙 _ := by
  simp only [internalTorMap,torProjection,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←homologyMap_comp,chain_retraction,homologyMap_id]

theorem internalTorMap_projection_of_ne (r N M : ℕ) (hMN : M≠N) :
    internalTorMap ε B hunit hε δ hδ r M ≫
      torProjection ε B hunit hε δ hδ r N=0 := by
  simp only [internalTorMap,torProjection,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←homologyMap_comp,inclusion_projection_eq_zero ε B hunit hε δ hδ N M hMN,
    homologyMap_zero]

theorem torProjection_internalTorMap_self (r N : ℕ) (z : (internal N).homology r) :
    torProjection ε B hunit hε δ hδ r N
      (internalTorMap ε B hunit hε δ hδ r N z)=z :=
  congrArg (fun f => f z) (internalTorMap_projection ε B hunit hε δ hδ r N)

theorem torProjection_internalTorMap_of_ne (r N M : ℕ) (hMN : M≠N)
    (z : (internal M).homology r) :
    torProjection ε B hunit hε δ hδ r N
      (internalTorMap ε B hunit hε δ hδ r M z)=0 :=
  congrArg (fun f => f z) (internalTorMap_projection_of_ne ε B hunit hε δ hδ r N M hMN)

/-- Distinct original internal degrees have zero intersection in actual Tor. -/
theorem torPiece_disjoint (r N M : ℕ) (hNM : N≠M) :
    Disjoint (torPiece ε B hunit hε δ hδ r N) (torPiece ε B hunit hε δ hδ r M) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨z,hz⟩ := hy
  have hy0 : y=0 := by
    calc
      y=torProjection ε B hunit hε δ hδ r N
          (internalTorMap ε B hunit hε δ hδ r N y) :=
        (torProjection_internalTorMap_self ε B hunit hε δ hδ r N y).symm
      _ = torProjection ε B hunit hε δ hδ r N
          (internalTorMap ε B hunit hε δ hδ r M z) :=
        congrArg (fun t => torProjection ε B hunit hε δ hδ r N t) hz.symm
      _ = 0 := torProjection_internalTorMap_of_ne ε B hunit hε δ hδ r N M
        (Ne.symm hNM) z
  change internalTorMap ε B hunit hε δ hδ r N y=0
  rw [hy0,map_zero]

/-- Under actual diagonal concentration, its diagonal summand is all of Tor. -/
theorem diagonal_top_of_hasDiagonalTor (h : HasDiagonalTor ε B hunit hε δ hδ)
    (r : ℕ) : torPiece ε B hunit hε δ hδ r r=⊤ := by
  apply top_unique
  rw [←torPieces_iSup ε B hunit hε δ hδ r]
  apply iSup_le
  intro N
  by_cases hN : r=N
  · subst N
    exact le_rfl
  · rw [h r N hN]
    exact bot_le

theorem hasDiagonalTor_iff_diagonal_top : HasDiagonalTor ε B hunit hε δ hδ ↔
    ∀ r,torPiece ε B hunit hε δ hδ r r=⊤ := by
  constructor
  · exact diagonal_top_of_hasDiagonalTor ε B hunit hε δ hδ
  · intro h r N hN
    have hd := torPiece_disjoint ε B hunit hε δ hδ r r N hN
    simpa only [h r,top_disjoint] using hd

/-- Degree zero of the bar complex has only the empty word. No Koszul
assumption, finite basis, or positivity premise is needed here. -/
theorem torPiece_zero_off_diagonal (N : ℕ) (hN : 0≠N) :
    torPiece ε B hunit hε δ hδ 0 N=⊥ := by
  apply (torPiece_eq_bot_iff ε B hunit hε δ hδ 0 N).mpr
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero (ModuleCat.of K (piece (K := K) δ 0 N))
  have hzero (z : piece (K := K) δ 0 N) : z=0 := by
    apply Subtype.ext
    apply Finsupp.ext
    intro L
    change z.val L=0
    apply (Finsupp.mem_supported' K z.val).mp z.property
    rintro ⟨hL,hW⟩
    have hn : L=[] := List.length_eq_zero_iff.mp hL
    subst L
    exact hN hW
  letI : Subsingleton (piece (K := K) δ 0 N) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end PaperVerification.WeightedBar
