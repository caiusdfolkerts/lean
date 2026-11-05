module

public import PaperVerification.ToricQuotientStarCovering
public import PaperVerification.ToricFanPolytopeConstruction
public import PaperVerification.ToricWallUniqueness
public import Mathlib.Algebra.Group.Int.Units

@[expose] public section

/-!
# Genuine opposite full cones in a complete smooth fan

Completeness is used through a small negative transverse perturbation of
the sum of the wall rays. Purity extends the resulting cone. The integral
basis condition then forces the opposite ray's transverse coordinate to
be exactly minus one.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem basis_wall_card (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) :
    ((Finset.univ.erase j).image b).card=n-1 := by
  rw [Finset.card_image_of_injective _ b.injective,Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp

theorem basis_wall_coord_zero (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (v : Lattice n) (hv : v∈(Finset.univ.erase j).image b) : b.repr v j=0 := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  simp only [Module.Basis.repr_self_apply,if_neg (Finset.mem_erase.mp hi).1]

/-- Smoothness makes the opposite transverse coefficient a unit in Z;
its sign therefore determines it exactly. -/
theorem opposite_wall_coord_eq_neg_one
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) (w : Lattice n)
    (hwcone : insert w ((Finset.univ.erase j).image b)∈«Σ».cones)
    (hwneg : b.repr w j<0) : b.repr w j = -1 := by
  let F := (Finset.univ.erase j).image b
  have hwF : w∉F := by
    intro hw
    rw [basis_wall_coord_zero b j w hw] at hwneg
    exact (lt_irrefl 0 hwneg)
  have hn : 0<n := by have h := j.isLt; omega
  have hcard : (insert w F).card=n := by
    rw [Finset.card_insert_of_notMem hwF,basis_wall_card b j]
    omega
  obtain ⟨c,hc⟩ := «Σ».full_cone_basis hwcone hcard
  obtain ⟨l,hl,hcl⟩ := Finset.mem_image.mp (hc ▸ Finset.mem_insert_self w F)
  have hzero (i : Fin n) (hil : i≠l) : b.repr (c i) j=0 := by
    have hci : c i∈insert w F := hc.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    rcases Finset.mem_insert.mp hci with hiw | hiF
    · exact (hil (c.injective (hiw.trans hcl.symm))).elim
    · exact basis_wall_coord_zero b j (c i) hiF
  have hprod : b.repr w j * c.repr (b j) l = 1 := by
    calc
      b.repr w j * c.repr (b j) l = ∑ i, c.repr (b j) i * b.repr (c i) j := by
        rw [Finset.sum_eq_single l]
        · rw [hcl,mul_comm]
        · intro i hi hil
          rw [hzero i hil,mul_zero]
        · intro hl
          exact (hl (Finset.mem_univ l)).elim
      _ = b.repr (∑ i,c.repr (b j) i • c i) j := by
        simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
      _ = 1 := by rw [c.sum_repr]; simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h | h
  · omega
  · exact h

/-- A negative coordinate of a cone vector must occur in one of the
actual generating rays. -/
theorem exists_ray_negative_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (s : Finset (Lattice n)) (x : Ambient n) (hx : x∈latticeRayCone s)
    (hxneg : (integralBasisReal b).repr x j<0) :
    ∃ w∈s,b.repr w j<0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨c,hc,hcx⟩ := hx
  have hsum : 0≤∑ v∈s.image (embed n),c v * (integralBasisReal b).repr v j := by
    apply Finset.sum_nonneg
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact mul_nonneg (hc _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
      (by rw [integralBasisReal_repr]; exact_mod_cast hn w hw)
  have he := congrArg (fun y=>(integralBasisReal b).repr y j) hcx
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul] at he
  rw [he] at hsum
  exact (not_lt_of_ge hsum) hxneg

/-- An actual opposite full cone exists across every facet of every full
cone; all ray sets and the transverse integral coordinate are explicit. -/
theorem exists_full_opposite_wall (hpure : «Σ».IsPure) (s : «Σ».fullCones) (j : Fin n) :
    ∃ t : «Σ».fullCones, ∃ w : Lattice n,
      t.val=insert w ((Finset.univ.erase j).image («Σ».fullConeBasis s)) ∧
      («Σ».fullConeBasis s).repr w j = -1 ∧
      s.val∩t.val=(Finset.univ.erase j).image («Σ».fullConeBasis s) ∧
      w∈t.val ∧ w∉s.val := by
  let b := «Σ».fullConeBasis s
  let F := (Finset.univ.erase j).image b
  have hFs : F⊆s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.image_subset_image (Finset.erase_subset j _)
  have hF : F∈«Σ».cones := «Σ».downward s.val («Σ».fullCones_mem s) F hFs
  obtain ⟨ε,hε,q,hq,hFq,hx⟩ := «Σ».exists_small_perturbation_in_containing_cone hF
    (-embed n (b j))
  obtain ⟨t,ht,hqt,htcard⟩ := hpure q hq
  let t' : «Σ».fullCones := ⟨t,Finset.mem_filter.mpr ⟨ht,htcard⟩⟩
  have hFt : F⊆t := hFq.trans hqt
  have hx' : (∑ u∈F,embed n u)+ε • (-embed n (b j))∈latticeRayCone t :=
    latticeRayCone_mono hqt hx
  have hneg : (integralBasisReal b).repr
      ((∑ u∈F,embed n u)+ε • (-embed n (b j))) j<0 := by
    have hz : (integralBasisReal b).repr (∑ u∈F,embed n u) j=0 := by
      rw [map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro u hu
      rw [integralBasisReal_repr,basis_wall_coord_zero b j u hu,Int.cast_zero]
    simp only [map_add,map_smul,map_neg,Finsupp.add_apply,Finsupp.smul_apply,
      Finsupp.neg_apply,integralBasisReal_repr,Module.Basis.repr_self_apply,
      if_true,Int.cast_one,smul_eq_mul,hz,zero_add,mul_neg,mul_one]
    exact neg_neg_of_pos hε
  obtain ⟨w,hwt,hwneg⟩ := exists_ray_negative_coordinate b j t _ hx' hneg
  have hwF : w∉F := by
    intro hw
    rw [basis_wall_coord_zero b j w hw] at hwneg
    exact (lt_irrefl 0 hwneg)
  have hins : insert w F⊆t := Finset.insert_subset hwt hFt
  have hcard : (insert w F).card=n := by
    rw [Finset.card_insert_of_notMem hwF,basis_wall_card b j]
    have hn := j.isLt
    omega
  have htF : t=insert w F :=
    (Finset.eq_of_subset_of_card_le hins (by rw [hcard,htcard])).symm
  have hwcone : insert w F∈«Σ».cones := htF ▸ ht
  have hwj : b.repr w j = -1 := «Σ».opposite_wall_coord_eq_neg_one b j w hwcone hwneg
  have hws : w∉s.val := by
    intro hws
    obtain ⟨i,hi,hwi⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hws)
    rw [← hwi,Module.Basis.repr_self_apply] at hwneg
    split_ifs at hwneg <;> omega
  have hmeet : s.val∩t=F := by
    rw [htF]
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hvs,rfl|hvF⟩
      · exact (hws hvs).elim
      · exact hvF
    · intro hvF
      exact ⟨hFs hvF,Or.inr hvF⟩
  exact ⟨t',w,htF,hwj,hmeet,hwt,hws⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.opposite_wall_coord_eq_neg_one
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_full_opposite_wall
