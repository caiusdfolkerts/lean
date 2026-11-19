module
public import RawBoundaryMatch
public import TerminalGeometry

@[expose] public section

/-!
# Semantic transport of a literal boundary match

The finite checker compares complete mask families.  This module proves that
its checked vertex permutation gives equality of the corresponding geometric
`Boundary` records, simultaneously for facets and polygons.
-/

noncomputable section

namespace Nonrational.TerminalVerification

open Nonrational.TerminalData
open Papers.RationalityTen
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open GrowthRenaming RawBoundaryMatch

def vertexEquiv (p : Bijection (Fin 10)) : Equiv.Perm (Fin 10) where
  toFun := p.forward
  invFun := p.inverse
  left_inv := p.left_inverse
  right_inv := p.right_inverse

theorem decodeMask_rename (p : Bijection (Fin 10)) (mask : Nat) :
    decodeMask (renameMask p.forward mask) = (decodeMask mask).image (vertexEquiv p) := by
  ext a
  constructor
  · intro ha
    have hbit : (renameMask p.forward mask).testBit a.val = true :=
      (Finset.mem_filter.mp ha).2
    refine Finset.mem_image.mpr ⟨p.inverse a, ?_, p.right_inverse a⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := renameMask_bit p mask (p.inverse a)
    rw [p.right_inverse] at h
    exact h.symm.trans hbit
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (renameMask_bit p mask b).trans (Finset.mem_filter.mp hb).2

theorem decode_family_relabel (p : Bijection (Fin 10)) (A : List Nat) :
    (A.toFinset.image decodeMask).image (fun S => S.image (vertexEquiv p)) =
      (A.map (renameMask p.forward)).toFinset.image decodeMask := by
  ext S
  constructor
  · intro hS
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨mask, hm, rfl⟩ := Finset.mem_image.mp hF
    refine Finset.mem_image.mpr ⟨renameMask p.forward mask, ?_, decodeMask_rename p mask⟩
    exact List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨mask, List.mem_toFinset.mp hm, rfl⟩)
  · intro hS
    obtain ⟨mask, hm, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    refine Finset.mem_image.mpr ⟨decodeMask source, ?_, (decodeMask_rename p source).symm⟩
    exact Finset.mem_image.mpr ⟨source, List.mem_toFinset.mpr hsource, rfl⟩

theorem decode_relabel_of_matching_sets (B T : RawBoundary)
    (p : Bijection (Fin 10))
    (hfacets : ∀ x, x ∈ B.facets.map (renameMask p.forward) ↔ x ∈ T.facets)
    (hpolygons : ∀ x, x ∈ B.polygons.map (renameMask p.forward) ↔ x ∈ T.polygons) :
    (decode B).relabel (vertexEquiv p) = decode T := by
  have hf : (B.facets.map (renameMask p.forward)).toFinset = T.facets.toFinset := by
    ext x
    simpa only [List.mem_toFinset] using hfacets x
  have hp : (B.polygons.map (renameMask p.forward)).toFinset = T.polygons.toFinset := by
    ext x
    simpa only [List.mem_toFinset] using hpolygons x
  have hff := decode_family_relabel p B.facets
  have hpp := decode_family_relabel p B.polygons
  rw [hf] at hff
  rw [hp] at hpp
  exact Boundary.ext_faces _ _ hff hpp

theorem witnessCheck_decode (B : RawBoundary) (w : RawBoundaryMatch.Witness)
    (h : witnessCheck targetCount (fun j => (targets j).facets)
      (fun j => (targets j).polygons) B.facets B.polygons w = true) :
    w.target < targetCount ∧ ∃ σ : Equiv.Perm (Fin 10),
      (decode B).relabel σ = decode (targets w.target) := by
  obtain ⟨hbound, p, hf, hp⟩ := witnessCheck_sound targetCount
    (fun j => (targets j).facets) (fun j => (targets j).polygons)
    B.facets B.polygons w h
  exact ⟨hbound, vertexEquiv p, decode_relabel_of_matching_sets B (targets w.target) p hf hp⟩

#print axioms witnessCheck_decode

end Nonrational.TerminalVerification
