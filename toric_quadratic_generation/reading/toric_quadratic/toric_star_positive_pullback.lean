module

public import PaperVerification.ToricContractibleEdgeDegrees
public import Mathlib.Tactic.Abel

@[expose] public section

/-! # Pullback degrees at positive exceptional endpoints

The supporting slack across an actual old wall is proved to be the length
of a genuine edge of the original polytope.  Replacing either endpoint
ray by its sum with wall rays does not change that slack when coefficients
are pulled back by the corresponding sum.  Thus the degree estimate uses
the literal old edge bound, without an assumed curve-pushforward theorem.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The normalized old wall slack is exactly a genuine primitive edge length. -/
theorem wall_support_slack_eq_edge_length
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones=P.normalFan)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hU : Finset.univ.image d ∈ «Σ».cones) (j : Fin n) (q : Lattice n)
    (hqcone : insert q ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (hqcoord : d.repr q j = -1)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ i, ℓ (embed n (d i))=(P.integralSupport (d i):ℝ)) :
    ∃ v w : Lattice n, P.IsEdge (embed n v) (embed n w) ∧
      (P.integralSupport q:ℝ)-ℓ (embed n q)=(latticeLength v w:ℝ) := by
  have hnormal : (latticeRayCone (Finset.univ.image d):Set (Ambient n)) ∈ P.normalFan := by
    rw [← hfan]
    exact ⟨Finset.univ.image d,hU,rfl⟩
  obtain ⟨x,hx,hxcone⟩ := hnormal
  obtain ⟨v,lengths,hv,hedges⟩ := P.full_normal_basis_edges hP x hx d hxcone.symm
  have hcone : P.normalCone (embed n v)=
      (latticeRayCone (Finset.univ.image d):Set (Ambient n)) := by
    rw [hv]
    exact hxcone.symm
  have hvP : embed n v ∈ P.carrier := hv.symm ▸ hx
  have hform : ℓ=-(dotProductEquiv ℝ (Fin n) (embed n v)) := by
    apply (integralBasisReal d).ext
    intro i
    rw [integralBasisReal_apply,hℓ i]
    have hactive : embed n (d i) ∈ P.normalCone (embed n v) := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    have hs := (P.integralSupport_spec (d i) (embed n v) hvP).2.mpr hactive
    change (P.integralSupport (d i) : ℝ) =
      -dotProduct (embed n v) (embed n (d i))
    calc
      _ = -dotProduct (embed n (d i)) (embed n v) := hs.symm
      _ = _ := congrArg Neg.neg (dotProduct_comm _ _)
  let w := v+(lengths j:ℤ)•integralDualBasis d j
  have hedge : P.IsEdge (embed n v) (embed n w) := (hedges j).2
  have hactive := P.opposite_wall_normal_at_edge_endpoint hP «Σ» hfan v d hU
    hcone j (lengths j) (hedges j).1 hedge q hqcone (by omega)
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n q)
  have hqvalue : (P.integralSupport q:ℝ)=-f (embed n w) :=
    ((P.integralSupport_spec q (embed n w) (P.edge_endpoints_extreme hedge).2.1).2.mpr
      hactive).symm
  have hℓq : ℓ (embed n q)=-f (embed n v) := by
    rw [hform]
    change -dotProduct (embed n v) (embed n q) =
      -dotProduct (embed n q) (embed n v)
    exact congrArg Neg.neg (dotProduct_comm _ _)
  refine ⟨v,w,hedge,?_⟩
  rw [hqvalue,hℓq]
  have hdisp : embed n w-embed n v=(lengths j:ℝ)•integralBasisReal (integralDualBasis d) j := by
    simp only [w,map_add,embed_int_smul,Int.cast_natCast,
      integralBasisReal_apply,add_sub_cancel_left]
  calc
    -f (embed n w)- -f (embed n v) = -f (embed n w-embed n v) := by
      rw [map_sub]
      ring
    _ = (lengths j:ℝ) := by
      rw [hdisp,map_smul,smul_eq_mul,pairing_integral_dual_basis,hqcoord]
      simp
    _ = (latticeLength v w:ℝ) := by
      change (lengths j : ℝ) =
        (latticeLength v (v + (lengths j : ℤ) • integralDualBasis d j) : ℝ)
      rw [latticeLength_basis_direction]

end LatticePolytope

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {Γ : SmoothCompleteFan n} (R : Γ.PrimitiveRelation)

/-- Replacing both endpoint rays by sums with common wall rays leaves the
primitive degree equal to the original supporting slack. -/
theorem degree_pullback_two_sum_rays
    (a b : Lattice n → ℝ) (W C D : Finset (Lattice n))
    (p q e x : Lattice n) (hC : C⊆W) (hD : D⊆W)
    (he : e=p+∑ u ∈ C,u) (hx : x=q+∑ u ∈ D,u)
    (hN : R.negative⊆W) (hP : R.positive \ insert e W={x})
    (hbW : ∀ u ∈ W,b u=a u)
    (hbe : b e=a p+∑ u ∈ C,a u) (hbx : b x=a q+∑ u ∈ D,a u)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓW : ∀ u ∈ W,ℓ (embed n u)=a u) (hℓp : ℓ (embed n p)=a p) :
    R.degree b=a q-ℓ (embed n q) := by
  have hsum (T : Finset (Lattice n)) (hT : T⊆W) :
      ℓ (embed n (∑ u ∈ T,u))=∑ u ∈ T,a u := by
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun u hu ↦ hℓW u (hT hu))
  have hℓe : ℓ (embed n e)=b e := by
    calc
      ℓ (embed n e)=ℓ (embed n p)+ℓ (embed n (∑ u ∈ C,u)) := by
        rw [he,map_add,map_add]
      _ = a p+∑ u ∈ C,a u := by rw [hℓp,hsum C hC]
      _ = b e := hbe.symm
  have hactive (u : Lattice n) (hu : u ∈ insert e W) : ℓ (embed n u)=b u := by
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hℓe
    · exact (hℓW u hu).trans (hbW u hu).symm
  have hxP : x ∈ R.positive := by
    have hm : x ∈ R.positive \ insert e W := hP.symm ▸ Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp hm).1
  have hrest (u : Lattice n) (hu : u ∈ R.positive) (hux : u≠x) :
      b u-ℓ (embed n u)=0 := by
    apply sub_eq_zero.mpr
    symm
    apply hactive
    by_contra hn
    have hm : u ∈ R.positive \ insert e W := Finset.mem_sdiff.mpr ⟨hu,hn⟩
    rw [hP] at hm
    exact hux (Finset.mem_singleton.mp hm)
  rw [R.degree_eq_sum_slack b ℓ (fun u hu ↦
    (hℓW u (hN hu)).trans (hbW u (hN hu)).symm)]
  rw [Finset.sum_eq_single x (fun u hu hux ↦ hrest u hu hux)
    (fun h ↦ False.elim (h hxP))]
  rw [hbx,hx,map_add,map_add,hsum D hD]
  ring

/-- The opposite old ray has primitive coefficient -1. This follows from
the actual relation equation; no normalization or pushforward is assumed. -/
theorem opposite_old_coordinate_of_two_sum_rays
    (d : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (C D : Finset (Lattice n)) (q e x : Lattice n)
    (hC : C⊆(Finset.univ.erase j).image d)
    (hD : D⊆(Finset.univ.erase j).image d)
    (he : e=d j+∑ u ∈ C,u) (hx : x=q+∑ u ∈ D,u)
    (heP : e ∈ R.positive)
    (hN : R.negative⊆(Finset.univ.erase j).image d)
    (hP : R.positive \ insert e ((Finset.univ.erase j).image d)={x}) :
    d.repr q j = -1 := by
  let W := (Finset.univ.erase j).image d
  have hwall (u : Lattice n) (hu : u ∈ W) : d.coord j u=0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    simp only [Module.Basis.coord_apply,Module.Basis.repr_self_apply,
      if_neg (Finset.mem_erase.mp hi).1]
  have hsum (T : Finset (Lattice n)) (hT : T⊆W) : d.coord j (∑ u ∈ T,u)=0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun u hu ↦ hwall u (hT hu))
  have hecoord : d.coord j e=1 := by
    rw [he,map_add,hsum C hC]
    simp [Module.Basis.coord_apply]
  have hxcoord : d.coord j x=d.coord j q := by rw [hx,map_add,hsum D hD,add_zero]
  have hxdata : x ∈ R.positive ∧ x ∉ insert e W :=
    Finset.mem_sdiff.mp (hP.symm ▸ Finset.mem_singleton_self x)
  have hex : e≠x := by
    intro h
    exact hxdata.2 (Finset.mem_insert.mpr (Or.inl h.symm))
  have heRest : e ∈ R.positive.erase x := Finset.mem_erase.mpr ⟨hex,heP⟩
  have hrest : (∑ u ∈ R.positive.erase x,d.coord j u)=1 := by
    rw [Finset.sum_eq_single e]
    · exact hecoord
    · intro u hu hue
      apply hwall
      have huU : u ∈ insert e W := by
        by_contra hn
        have hm : u ∈ R.positive \ insert e W :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hu,hn⟩
        rw [hP] at hm
        exact (Finset.mem_erase.mp hu).1 (Finset.mem_singleton.mp hm)
      exact (Finset.mem_insert.mp huU).resolve_left hue
    · intro hn
      exact (hn heRest).elim
  have hnegative : (∑ u ∈ R.negative,(R.coefficient u:ℤ)*d.coord j u)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [hwall u (hN hu),mul_zero]
  have h := congrArg (d.coord j) R.equation
  simp only [map_sum,map_smul,smul_eq_mul] at h
  rw [← Finset.add_sum_erase R.positive (fun u ↦ d.coord j u) hxdata.1,
    hrest,hxcoord,hnegative] at h
  change d.coord j q = -1
  omega

end SmoothCompleteFan.PrimitiveRelation

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The positive-exceptional pullback degree is an actual old edge length.
The two sum-ray descriptions allow either or both endpoints to be exceptional. -/
theorem positive_sum_pullback_degree_eq_edge_length
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n) (hfan : «Σ».realCones=P.normalFan)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hU : Finset.univ.image d ∈ «Σ».cones) (j : Fin n)
    (C D : Finset (Lattice n)) (q e x : Lattice n)
    (hC : C⊆(Finset.univ.erase j).image d)
    (hD : D⊆(Finset.univ.erase j).image d)
    (he : e=d j+∑ u ∈ C,u) (hx : x=q+∑ u ∈ D,u)
    (hqcone : insert q ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (Γ : SmoothCompleteFan n) (R : Γ.PrimitiveRelation)
    (heP : e ∈ R.positive)
    (hN : R.negative⊆(Finset.univ.erase j).image d)
    (hPdiff : R.positive \ insert e ((Finset.univ.erase j).image d)={x})
    (b : Lattice n → ℝ)
    (hbW : ∀ u ∈ (Finset.univ.erase j).image d,b u=(P.integralSupport u:ℝ))
    (hbe : b e=(P.integralSupport (d j):ℝ)+∑ u ∈ C,(P.integralSupport u:ℝ))
    (hbx : b x=(P.integralSupport q:ℝ)+∑ u ∈ D,(P.integralSupport u:ℝ)) :
    ∃ v w : Lattice n, P.IsEdge (embed n v) (embed n w) ∧
      R.degree b=(latticeLength v w:ℝ) := by
  obtain ⟨ℓ,hℓ,hstrict⟩ := P.integralSupport_isStrictSupport «Σ» hfan _ hU
  have hℓi (i : Fin n) : ℓ (embed n (d i))=(P.integralSupport (d i):ℝ) :=
    hℓ (d i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hℓW (u : Lattice n) (hu : u ∈ (Finset.univ.erase j).image d) :
      ℓ (embed n u)=(P.integralSupport u:ℝ) :=
    hℓ u (Finset.image_subset_image (Finset.erase_subset j Finset.univ) hu)
  have hcoord := R.opposite_old_coordinate_of_two_sum_rays d j C D q e x
    hC hD he hx heP hN hPdiff
  have hdegree := R.degree_pullback_two_sum_rays (fun u ↦ (P.integralSupport u:ℝ)) b
    ((Finset.univ.erase j).image d) C D (d j) q e x hC hD he hx hN hPdiff
    hbW hbe hbx ℓ hℓW (hℓi j)
  obtain ⟨v,w,hedge,hslack⟩ := P.wall_support_slack_eq_edge_length hP «Σ» hfan d hU
    j q hqcone hcoord ℓ hℓi
  exact ⟨v,w,hedge,hdegree.trans hslack⟩

/-- A literal edge bound applies to a degree once the preceding theorem
identifies its genuine old edge. -/
theorem degree_lower_bound_of_edge_length {Γ : SmoothCompleteFan n}
    (R : Γ.PrimitiveRelation) (b : Lattice n → ℝ) {bound : ℕ}
    (hbound : P.EdgesAtLeast bound)
    (hdegree : ∃ v w : Lattice n,P.IsEdge (embed n v) (embed n w) ∧
      R.degree b=(latticeLength v w:ℝ)) : (bound:ℝ) ≤ R.degree b := by
  obtain ⟨v,w,hedge,hdegree⟩ := hdegree
  rw [hdegree]
  exact_mod_cast (P.edgesAtLeast_iff bound).mp hbound v w hedge

end LatticePolytope

end PaperVerification.ToricGeometry
