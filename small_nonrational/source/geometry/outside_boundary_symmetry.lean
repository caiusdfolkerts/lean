module

public import BoundaryGeneratorFrames
public import FacePlacementCodes
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.ViaEmbedding

@[expose] public section

/-!
# Permuting all labels outside a fixed root

Checked adjacent-swap frames generate every permutation of the outside
labels. This uses Mathlib's theorem for the complete symmetric group; no
producer enumeration of permutations is treated as a completeness proof.
The frames are ordinary boundary frames, with no fixed graph premise.
-/

noncomputable section
namespace Papers.RationalityTen.OutsideBoundarySymmetry

open Finset
open BoundaryGeneratorFrames FacePlacementCodes
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LiteralMaskGeometry

def adjacentSwap : (n : Nat) → Fin (n - 1) → Equiv.Perm (Fin n)
  | 0, i => i.elim0
  | n + 1, i => Equiv.swap i.castSucc i.succ

def adjacentFirst (n : Nat) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by have := i.isLt; omega⟩

def adjacentSecond (n : Nat) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

theorem adjacentSwap_eq (n : Nat) (i : Fin (n - 1)) :
    adjacentSwap n i = Equiv.swap (adjacentFirst n i) (adjacentSecond n i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => rfl

theorem viaEmbedding_swap {n : Nat} (outside : Fin n ↪ Fin 10) (a b : Fin n) :
    (Equiv.swap a b).viaEmbedding outside = Equiv.swap (outside a) (outside b) := by
  apply Equiv.ext
  intro v
  by_cases hv : v ∈ Set.range outside
  · obtain ⟨j, rfl⟩ := hv
    rw [Equiv.Perm.viaEmbedding_apply, outside.injective.map_swap]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hv]
    apply (Equiv.swap_apply_of_ne_of_ne _ _).symm
    · intro h
      exact hv ⟨a, h.symm⟩
    · intro h
      exact hv ⟨b, h.symm⟩

theorem frames_of_adjacent {c n : Nat} (cells : Fin c → ConcreteGrowth.Cell)
    (outside : Fin n ↪ Fin 10)
    (hgenerators : ∀ i : Fin (n - 1), ∃ F : BoundaryFrame cells,
      F.vertices = (adjacentSwap n i).viaEmbedding outside) :
    ∀ σ : Equiv.Perm (Fin n), ∃ F : BoundaryFrame cells,
      F.vertices = σ.viaEmbedding outside := by
  let H : Submonoid (Equiv.Perm (Fin n)) :=
    { carrier := {σ | ∃ F : BoundaryFrame cells,
        F.vertices = Equiv.Perm.viaEmbeddingHom outside σ}
      one_mem' := by
        refine ⟨identityFrame cells, ?_⟩
        change (1 : Equiv.Perm (Fin 10)) = Equiv.Perm.viaEmbeddingHom outside 1
        rw [map_one]
      mul_mem' := by
        rintro σ τ ⟨F, hF⟩ ⟨G, hG⟩
        refine ⟨composeFrame G F, ?_⟩
        change F.vertices * G.vertices = Equiv.Perm.viaEmbeddingHom outside (σ * τ)
        rw [hF, hG, map_mul] }
  intro σ
  have hσ : σ ∈ H := by
    cases n with
    | zero =>
      have hσ : σ = 1 := Subsingleton.elim _ _
      rw [hσ]
      exact H.one_mem
    | succ n =>
      have hle : Submonoid.closure
          (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ H := by
        apply Submonoid.closure_le.mpr
        rintro _ ⟨i, rfl⟩
        exact hgenerators i
      apply hle
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
  exact hσ

def outsideEmbedding {m : Nat} (B : Block m) : Fin B.outside ↪ Fin 10 where
  toFun j := B.target ⟨B.shared + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt B.shared) B.target_le⟩
  inj' := by
    intro i j hij
    have h := congrArg Fin.val (B.target.injective hij)
    apply Fin.ext
    change B.shared + i.val = B.shared + j.val at h
    omega

theorem inside_not_outside {m : Nat} (B : Block m) (i : Fin B.shared) :
    B.target ⟨i.val, lt_of_lt_of_le i.isLt
      ((Nat.le_add_right _ _).trans B.target_le)⟩ ∉ Set.range (outsideEmbedding B) := by
  rintro ⟨j, hj⟩
  have heq := congrArg Fin.val (B.target.injective hj)
  change B.shared + j.val = i.val at heq
  omega

/-- A permutation of outside coordinates takes the canonical outer code
to any outer injection, while preserving every possible inner code. -/
theorem decoded_factor {m : Nat} (B : Block m) (inner outer : Nat) :
    ∃ σ : Equiv.Perm (Fin B.outside),
      ∀ i : Fin m,
        σ.viaEmbedding (outsideEmbedding B) (B.decoded inner 0 i) =
          B.decoded inner outer i := by
  let first := FiniteCycleCandidates.decodeEmbedding B.remaining_le 0
  let second := FiniteCycleCandidates.decodeEmbedding B.remaining_le outer
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair first second
    first.injective second.injective
  refine ⟨σ, ?_⟩
  intro i
  unfold Block.decoded
  by_cases hi : (B.source.symm i).val < B.shared
  · rw [dif_pos hi, dif_pos hi]
    exact Equiv.Perm.viaEmbedding_apply_of_notMem σ (outsideEmbedding B) _
      (inside_not_outside B _)
  · rw [dif_neg hi, dif_neg hi]
    have hindex : (B.source.symm i).val - B.shared < m - B.shared := by
      have := (B.source.symm i).isLt
      omega
    let j : Fin (m - B.shared) := ⟨(B.source.symm i).val - B.shared, hindex⟩
    change σ.viaEmbedding (outsideEmbedding B) ((outsideEmbedding B) (first j)) =
      (outsideEmbedding B) (second j)
    rw [Equiv.Perm.viaEmbedding_apply, hσ]

/-- A complete cell is fixed when all its vertices are outside the support
of the extended permutation and all its faces use those vertices. -/
theorem mapCell_fixed {n : Nat} (root : Cell 10) (outside : Fin n ↪ Fin 10)
    (hvertices : ∀ v ∈ root.vertices, v ∉ Set.range outside)
    (hedges : ∀ e ∈ root.edges, e ⊆ root.vertices)
    (hridges : ∀ q ∈ root.ridges, q ⊆ root.vertices)
    (σ : Equiv.Perm (Fin n)) : mapCell (σ.viaEmbedding outside).toEmbedding root = root := by
  have himage (S : Finset (Fin 10)) (hS : S ⊆ root.vertices) :
      S.image (σ.viaEmbedding outside) = S := by
    calc
      _ = S.image id := Finset.image_congr (fun v hv =>
        Equiv.Perm.viaEmbedding_apply_of_notMem σ outside v (hvertices v (hS hv)))
      _ = S := Finset.image_id
  apply cell_ext
  · exact himage root.vertices (fun _ hv => hv)
  · change root.edges.image (fun S => S.image (σ.viaEmbedding outside)) = root.edges
    calc
      _ = root.edges.image id := Finset.image_congr (fun S hS => himage S (hedges S hS))
      _ = root.edges := Finset.image_id
  · change root.ridges.image (fun S => S.image (σ.viaEmbedding outside)) = root.ridges
    calc
      _ = root.ridges.image id := Finset.image_congr (fun S hS => himage S (hridges S hS))
      _ = root.ridges := Finset.image_id

end Papers.RationalityTen.OutsideBoundarySymmetry
