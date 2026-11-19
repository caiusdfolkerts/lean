module
public import graph_foundation.part009
public import Mathlib.Algebra.MvPolynomial.Division

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Universal.BasisFilteredHomology -/
section

section
set_option maxRecDepth 4000
set_option maxHeartbeats 300000
set_option Elab.async false
/-! # Actual cycle lifts for a basis-graded differential

The filtration is the span of basis vectors of weight below its index.  Its
top projections are the actual basis coefficient projections.  A differential
homogeneous in these weights has all required cycle lifts over any ring.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical CommAlg FourPapers.FilteredHomology
variable {K I J X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

def basisFiltration (b : Module.Basis I K X) (w : I → ℕ) : Filtration (K := K) X where
  level n := Submodule.span K (b '' {i | w i < n})
  zero := by simp
  mono := by
    intro m n hmn
    apply Submodule.span_mono
    exact Set.image_mono (fun i hi => hi.trans_le hmn)
  exhaustive x := by
    refine ⟨(b.repr x).support.sup w + 1, ?_⟩
    rw [b.mem_span_image]
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup (f := w) hi)

theorem basisFiltration_mem (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ) (x : X) :
    x ∈ (basisFiltration b w).level n ↔ ∀ i, n ≤ w i → b.repr x i = 0 := by
  rw [basisFiltration, b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hn
    exact (not_lt_of_ge hi) (h (Finsupp.mem_support_iff.mpr hn))
  · intro h i hi
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (h i (Nat.le_of_not_gt hn))

@[simp] theorem basisProjection_coefficient (b : Module.Basis I K X) (w : I → ℕ)
    (n : ℕ) (x : X) (i : I) :
    b.repr (Grading.projection b w n x) i = if w i = n then b.repr x i else 0 := by
  simp only [Grading.projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Grading.filterMap_apply, Finsupp.filter_apply]
  split_ifs <;> rfl

theorem basisProjection_level (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ) (x : X) :
    Grading.projection b w n x ∈ (basisFiltration b w).level (n + 1) := by
  rw [basisFiltration_mem]
  intro i hi
  rw [basisProjection_coefficient, if_neg (by omega)]

theorem basisProjection_error_lower (b : Module.Basis I K X) (w : I → ℕ)
    (n : ℕ) (x : X) (hx : x ∈ (basisFiltration b w).level (n + 1)) :
    x - Grading.projection b w n x ∈ (basisFiltration b w).level n := by
  rw [basisFiltration_mem] at hx ⊢
  intro i hi
  rw [map_sub, Finsupp.sub_apply, basisProjection_coefficient]
  by_cases hn : w i = n
  · rw [if_pos hn, sub_self]
  · rw [if_neg hn, sub_zero]
    exact hx i (by omega)

theorem basisProjection_lower_zero (b : Module.Basis I K X) (w : I → ℕ)
    (n : ℕ) (x : X) (hx : x ∈ (basisFiltration b w).level n) :
    Grading.projection b w n x = 0 := by
  apply b.repr.injective
  ext i
  rw [basisProjection_coefficient, map_zero, Finsupp.zero_apply]
  split_ifs with hi
  · exact (basisFiltration_mem b w n x).mp hx i (by omega)
  · rfl

theorem basisProjection_commutes (b : Module.Basis I K X) (c : Module.Basis J K Y)
    (w : I → ℕ) (v : J → ℕ) (f : X →ₗ[K] Y)
    (h : ∀ i, f (b i) ∈ Grading.Piece c v (w i)) (n : ℕ) :
    f.comp (Grading.projection b w n) = (Grading.projection c v n).comp f := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, Grading.projection_basis]
  by_cases hi : w i = n
  · rw [if_pos hi]
    exact (Grading.projection_eq_self (hi ▸ h i)).symm
  · rw [if_neg hi, map_zero]
    exact (Grading.projection_eq_zero (Ne.symm hi) (h i)).symm

/-- Concrete homogeneous basis data imply cycle lifting in the literal
weight filtration.  No exactness or splitting assumption is retained. -/
theorem basisHomogeneous_liftsCycles (b : Module.Basis I K X) (c : Module.Basis J K Y)
    (w : I → ℕ) (v : J → ℕ) (f : X →ₗ[K] Y)
    (h : ∀ i, f (b i) ∈ Grading.Piece c v (w i)) :
    LiftsCycles (basisFiltration b w) (basisFiltration c v) f :=
  liftsCycles_of_projections (basisFiltration b w) (basisFiltration c v) f
    (Grading.projection b w) (Grading.projection c v)
    (fun n x _ => basisProjection_level b w n x)
    (basisProjection_error_lower b w) (basisProjection_lower_zero c v)
    (basisProjection_commutes b c w v f h)


/-- Top coefficient projection to the genuine homogeneous submodule. -/
def basisTopProjection (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ) :
    (basisFiltration b w).level (n + 1) →ₗ[K] Grading.Piece b w n :=
  ((Grading.projection b w n).domRestrict _).codRestrict _
    (fun x => Grading.projection_mem b w n x.val)

theorem basisTopProjection_ker (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ) :
    LinearMap.ker (basisTopProjection b w n) = lowerInLevel (basisFiltration b w) n := by
  ext x
  constructor
  · intro h
    have hz : Grading.projection b w n x.val = 0 := congrArg Subtype.val h
    change x.val ∈ (basisFiltration b w).level n
    simpa only [hz, sub_zero] using basisProjection_error_lower b w n x.val x.property
  · intro h
    exact Subtype.ext (basisProjection_lower_zero b w n x.val h)

theorem basisTopProjection_surjective (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ) :
    Function.Surjective (basisTopProjection b w n) := by
  intro y
  have hy : y.val ∈ (basisFiltration b w).level (n + 1) := by
    have hp := basisProjection_level b w n y.val
    rwa [Grading.projection_eq_self y.property] at hp
  exact ⟨⟨y.val, hy⟩, Subtype.ext (Grading.projection_eq_self y.property)⟩

/-- The canonical identification of the literal successive quotient with the
actual homogeneous submodule is induced by the top coefficient projection. -/
def basisGradeEquiv (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ) :
    Grade (basisFiltration b w) n ≃ₗ[K] Grading.Piece b w n :=
  (Submodule.quotEquivOfEq _ _ (basisTopProjection_ker b w n).symm).trans
    ((basisTopProjection b w n).quotKerEquivOfSurjective (basisTopProjection_surjective b w n))

@[simp] theorem basisGradeEquiv_mk (b : Module.Basis I K X) (w : I → ℕ) (n : ℕ)
    (x : (basisFiltration b w).level (n + 1)) :
    basisGradeEquiv b w n (Submodule.Quotient.mk x) = basisTopProjection b w n x := rfl

/-- Compatibility with the actual associated graded differential is the
coefficient-projection identity, stated on representatives. -/
theorem basisGradeEquiv_differential (b : Module.Basis I K X) (c : Module.Basis J K Y)
    (w : I → ℕ) (v : J → ℕ) (f : X →ₗ[K] Y)
    (hf : Preserves (basisFiltration b w) (basisFiltration c v) f)
    (h : ∀ i, f (b i) ∈ Grading.Piece c v (w i)) (n : ℕ)
    (x : Grade (basisFiltration b w) n) :
    (basisGradeEquiv c v n
      (gradeMap (basisFiltration b w) (basisFiltration c v) f hf n x)).val =
      f (basisGradeEquiv b w n x).val := by
  obtain ⟨y, rfl⟩ := (lowerInLevel (basisFiltration b w) n).mkQ_surjective x
  change Grading.projection c v n (f y.val) = f (Grading.projection b w n y.val)
  exact (LinearMap.congr_fun (basisProjection_commutes b c w v f h n) y.val).symm

end FourPapers.Universal

#print axioms FourPapers.Universal.basisHomogeneous_liftsCycles


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FilteredPerturbationLifting -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg FourPapers.FilteredHomology FourPapers.Universal
variable {R X Y Z I J L : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]

lemma basisMap_preserves_of_coefficients
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (w : I → ℕ) (v : J → ℕ) (f : X →ₗ[R] Y)
    (hf : ∀i j,w i<v j→ c.repr (f (b i)) j=0) :
    Preserves (basisFiltration b w) (basisFiltration c v) f := by
  intro n x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change w i<n at hi
    rw [basisFiltration_mem]
    intro j hj
    exact hf i j (hi.trans_le hj)
  | zero => simpa only [map_zero] using (Submodule.zero_mem ((basisFiltration c v).level n))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

lemma basisStrictLower_level
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (w : I → ℕ) (v : J → ℕ) (f : X →ₗ[R] Y)
    (hf : ∀i j,w i≤v j→ c.repr (f (b i)) j=0)
    (n : ℕ) (x : X) (hx : x∈(basisFiltration b w).level (n+1)) :
    f x∈(basisFiltration c v).level n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change w i<n+1 at hi
    rw [basisFiltration_mem]
    intro j hj
    exact hf i j (by omega)
  | zero => simpa only [map_zero] using (Submodule.zero_mem ((basisFiltration c v).level n))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

lemma basisPerturbation_preserves
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (w : I → ℕ) (v : J → ℕ) (f f₀ : X →ₗ[R] Y)
    (h₀ : ∀i,f₀ (b i)∈Grading.Piece c v (w i))
    (hlower : ∀i j,w i≤v j→ c.repr ((f-f₀) (b i)) j=0) :
    Preserves (basisFiltration b w) (basisFiltration c v) f := by
  apply basisMap_preserves_of_coefficients b c w v f
  intro i j hij
  have hzero : c.repr (f₀ (b i)) j=0 := by
    by_contra hn
    have he := (Grading.mem_piece c v (w i) (f₀ (b i))).mp (h₀ i) j hn
    omega
  have hh := hlower i j hij.le
  simpa only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply,hzero,sub_zero] using hh

/-- The actual associated graded map is the homogeneous leading map, proved
from the strict matrix inequality on the difference. -/
lemma basisGradeEquiv_differential_of_lower
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (w : I → ℕ) (v : J → ℕ) (f f₀ : X →ₗ[R] Y)
    (h₀ : ∀i,f₀ (b i)∈Grading.Piece c v (w i))
    (hlower : ∀i j,w i≤v j→ c.repr ((f-f₀) (b i)) j=0)
    (hf : Preserves (basisFiltration b w) (basisFiltration c v) f)
    (n : ℕ) (x : Grade (basisFiltration b w) n) :
    (basisGradeEquiv c v n
      (gradeMap (basisFiltration b w) (basisFiltration c v) f hf n x)).val=
        f₀ (basisGradeEquiv b w n x).val := by
  obtain ⟨y,rfl⟩ := (lowerInLevel (basisFiltration b w) n).mkQ_surjective x
  change Grading.projection c v n (f y.val)=f₀ (Grading.projection b w n y.val)
  have hzero := basisProjection_lower_zero c v n ((f-f₀) y.val)
    (basisStrictLower_level b c w v (f-f₀) hlower n y.val y.property)
  rw [LinearMap.sub_apply,map_sub] at hzero
  rw [sub_eq_zero.mp hzero]
  exact (LinearMap.congr_fun (basisProjection_commutes b c w v f₀ h₀ n) y.val).symm

lemma homology_subsingleton_of_cycle_filling
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hfg : g.comp f=0)
    (hfill : ∀y,g y=0→∃x,f x=y) : Subsingleton (Homology f g hfg) := by
  constructor
  intro z t
  obtain ⟨z,rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective z
  obtain ⟨t,rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective t
  apply (homologyClass_eq_iff f g hfg z t).mpr
  apply hfill
  rw [map_sub,z.property,t.property,sub_self]

/-- Exactness of the literal homogeneous leading complex implies exactness
of the associated graded complex of the actual differential. -/
theorem basisGradedHomology_subsingleton
    (b : Module.Basis I R X) (c : Module.Basis J R Y) (e : Module.Basis L R Z)
    (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f f₀ : X →ₗ[R] Y) (g g₀ : Y →ₗ[R] Z)
    (hf₀ : ∀i,f₀ (b i)∈Grading.Piece c v (w i))
    (hg₀ : ∀j,g₀ (c j)∈Grading.Piece e u (v j))
    (hlowerf : ∀i j,w i≤v j→ c.repr ((f-f₀) (b i)) j=0)
    (hlowerg : ∀j l,v j≤u l→ e.repr ((g-g₀) (c j)) l=0)
    (hf : Preserves (basisFiltration b w) (basisFiltration c v) f)
    (hg : Preserves (basisFiltration c v) (basisFiltration e u) g)
    (hfg : g.comp f=0)
    (hfill : ∀n,∀y : Y,y∈Grading.Piece c v n→ g₀ y=0→
      ∃x : X,x∈Grading.Piece b w n ∧ f₀ x=y) (n : ℕ) :
    Subsingleton (GradedHomology (basisFiltration b w) (basisFiltration c v)
      (basisFiltration e u) f g hf hg hfg n) := by
  apply homology_subsingleton_of_cycle_filling
  intro y hy
  have hgy : g₀ (basisGradeEquiv c v n y).val=0 := by
    rw [←basisGradeEquiv_differential_of_lower c e v u g g₀ hg₀ hlowerg hg n y,hy,map_zero]
    rfl
  obtain ⟨x,hx,hfx⟩ := hfill n _ (basisGradeEquiv c v n y).property hgy
  refine ⟨(basisGradeEquiv b w n).symm ⟨x,hx⟩,?_⟩
  apply (basisGradeEquiv c v n).injective
  apply Subtype.ext
  rw [basisGradeEquiv_differential_of_lower b c w v f f₀ hf₀ hlowerf hf n,
    LinearEquiv.apply_symm_apply]
  exact hfx

/-- A faithful finite lifting theorem for an actual differential with a
strictly lower triangular perturbation. There is no field hypothesis. -/
theorem basisPerturbation_liftsCycles
    (b : Module.Basis I R X) (c : Module.Basis J R Y) (e : Module.Basis L R Z)
    (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f f₀ : X →ₗ[R] Y) (g g₀ : Y →ₗ[R] Z)
    (hf₀ : ∀i,f₀ (b i)∈Grading.Piece c v (w i))
    (hg₀ : ∀j,g₀ (c j)∈Grading.Piece e u (v j))
    (hlowerf : ∀i j,w i≤v j→ c.repr ((f-f₀) (b i)) j=0)
    (hlowerg : ∀j l,v j≤u l→ e.repr ((g-g₀) (c j)) l=0)
    (hfg : g.comp f=0)
    (hfill : ∀n,∀y : Y,y∈Grading.Piece c v n→ g₀ y=0→
      ∃x : X,x∈Grading.Piece b w n ∧ f₀ x=y) :
    LiftsCycles (basisFiltration b w) (basisFiltration c v) f := by
  let hf := basisPerturbation_preserves b c w v f f₀ hf₀ hlowerf
  let hg := basisPerturbation_preserves c e v u g g₀ hg₀ hlowerg
  apply liftsCycles_of_gradedHomology_subsingleton _ _ _ f g hf hg hfg
  exact basisGradedHomology_subsingleton b c e w v u f f₀ g g₀
    hf₀ hg₀ hlowerf hlowerg hf hg hfg hfill

end FourPapers.Sublattice
end


end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RestrictedBasisLifting -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg FourPapers.FilteredHomology FourPapers.Universal
variable {R X Y Z I J L : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]

lemma restrictedBasis_repr (b : Module.Basis I R X) (P : I → Prop)
    (x : Submodule.span R (b '' {i | P i})) (i : {i // P i}) :
    (Grading.restrictedBasis b P).repr x i=b.repr x.val i.val := by
  let rb := Grading.restrictedBasis b P
  have hh : rb.coord i=(b.coord i.val).comp
      (Submodule.span R (b '' {i | P i})).subtype := by
    apply rb.ext
    intro j
    simp only [rb, Module.Basis.coord_apply,LinearMap.comp_apply,
      Grading.restrictedBasis_val,Module.Basis.repr_self,Finsupp.single_apply]
    by_cases h : j=i
    · subst j
      simp
    · have hv : j.val≠i.val := fun he => h (Subtype.ext he)
      simp [h,hv]
  exact LinearMap.congr_fun hh x

lemma restrictedBasis_piece_iff (b : Module.Basis I R X) (P : I → Prop)
    (w : I → ℕ) (n : ℕ) (x : Submodule.span R (b '' {i | P i})) :
    x∈Grading.Piece (Grading.restrictedBasis b P) (fun i => w i.val) n ↔
      x.val∈Grading.Piece b w n := by
  rw [Grading.mem_piece,Grading.mem_piece]
  constructor
  · intro hx i hi
    have hPi : P i := (b.mem_span_image.mp x.property) (Finsupp.mem_support_iff.mpr hi)
    exact hx ⟨i,hPi⟩ (by simpa only [restrictedBasis_repr] using hi)
  · intro hx i hi
    exact hx i.val (by simpa only [restrictedBasis_repr] using hi)

lemma restrictedBasis_filtration_iff (b : Module.Basis I R X) (P : I → Prop)
    (w : I → ℕ) (n : ℕ) (x : Submodule.span R (b '' {i | P i})) :
    x∈(basisFiltration (Grading.restrictedBasis b P) (fun i => w i.val)).level n ↔
      x.val∈(basisFiltration b w).level n := by
  rw [basisFiltration_mem,basisFiltration_mem]
  constructor
  · intro hx i hi
    by_cases hPi : P i
    · exact (restrictedBasis_repr b P x ⟨i,hPi⟩).symm.trans (hx ⟨i,hPi⟩ hi)
    · by_contra hn
      exact hPi ((b.mem_span_image.mp x.property) (Finsupp.mem_support_iff.mpr hn))
  · intro hx i hi
    rw [restrictedBasis_repr]
    exact hx i.val hi

def basisSpanMap (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (P : I → Prop) (Q : J → Prop) (f : X →ₗ[R]Y)
    (hf : ∀x,x∈Submodule.span R (b '' {i | P i}) →
      f x∈Submodule.span R (c '' {j | Q j})) :
    Submodule.span R (b '' {i | P i}) →ₗ[R] Submodule.span R (c '' {j | Q j}) :=
  (f.domRestrict _).codRestrict _ (fun x => hf x.val x.property)

@[simp] lemma basisSpanMap_val (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (P : I → Prop) (Q : J → Prop) (f : X →ₗ[R]Y)
    (hf : ∀x,x∈Submodule.span R (b '' {i | P i}) →
      f x∈Submodule.span R (c '' {j | Q j}))
    (x : Submodule.span R (b '' {i | P i})) : (basisSpanMap b c P Q f hf x).val=f x.val := rfl

/-- Finite lifting confined to an actual basis-defined auxiliary component. -/
theorem basisPerturbation_liftsCycles_on_span
    (b : Module.Basis I R X) (c : Module.Basis J R Y) (e : Module.Basis L R Z)
    (P : I → Prop) (Q : J → Prop) (T : L → Prop)
    (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f f₀ : X →ₗ[R]Y) (g g₀ : Y →ₗ[R]Z)
    (hfP : ∀x,x∈Submodule.span R (b '' {i | P i}) → f x∈Submodule.span R (c '' {j | Q j}))
    (hf₀P : ∀x,x∈Submodule.span R (b '' {i | P i}) → f₀ x∈Submodule.span R (c '' {j | Q j}))
    (hgQ : ∀y,y∈Submodule.span R (c '' {j | Q j}) → g y∈Submodule.span R (e '' {l | T l}))
    (hg₀Q : ∀y,y∈Submodule.span R (c '' {j | Q j}) → g₀ y∈Submodule.span R (e '' {l | T l}))
    (hf₀ : ∀i,f₀ (b i)∈Grading.Piece c v (w i))
    (hg₀ : ∀j,g₀ (c j)∈Grading.Piece e u (v j))
    (hlowerf : ∀i j,w i≤v j→ c.repr ((f-f₀) (b i)) j=0)
    (hlowerg : ∀j l,v j≤u l→ e.repr ((g-g₀) (c j)) l=0)
    (hfg : g.comp f=0)
    (hfill : ∀n,∀y : Y,y∈Submodule.span R (c '' {j | Q j}) →
      y∈Grading.Piece c v n→ g₀ y=0→
      ∃x : X,x∈Submodule.span R (b '' {i | P i}) ∧ x∈Grading.Piece b w n ∧ f₀ x=y) :
    LiftsCycles (basisFiltration (Grading.restrictedBasis b P) (fun i => w i.val))
      (basisFiltration (Grading.restrictedBasis c Q) (fun j => v j.val))
      (basisSpanMap b c P Q f hfP) := by
  let fr := basisSpanMap b c P Q f hfP
  let f₀r := basisSpanMap b c P Q f₀ hf₀P
  let gr := basisSpanMap c e Q T g hgQ
  let g₀r := basisSpanMap c e Q T g₀ hg₀Q
  apply basisPerturbation_liftsCycles (Grading.restrictedBasis b P)
    (Grading.restrictedBasis c Q) (Grading.restrictedBasis e T)
    (fun i => w i.val) (fun j => v j.val) (fun l => u l.val) fr f₀r gr g₀r
  · intro i
    apply (restrictedBasis_piece_iff c Q v (w i.val) _).mpr
    simpa only [f₀r,basisSpanMap_val,Grading.restrictedBasis_val] using hf₀ i.val
  · intro j
    apply (restrictedBasis_piece_iff e T u (v j.val) _).mpr
    simpa only [g₀r,basisSpanMap_val,Grading.restrictedBasis_val] using hg₀ j.val
  · intro i j hij
    rw [restrictedBasis_repr]
    change c.repr ((f-f₀) ((Grading.restrictedBasis b P i).val)) j.val=0
    rw [Grading.restrictedBasis_val]
    exact hlowerf i.val j.val hij
  · intro j l hjl
    rw [restrictedBasis_repr]
    change e.repr ((g-g₀) ((Grading.restrictedBasis c Q j).val)) l.val=0
    rw [Grading.restrictedBasis_val]
    exact hlowerg j.val l.val hjl
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hfg x.val
  · intro n y hy hgy
    have hgy' : g₀ y.val=0 := congrArg Subtype.val hgy
    obtain ⟨x,hx,hxn,hfx⟩ := hfill n y.val y.property
      ((restrictedBasis_piece_iff c Q v n y).mp hy) hgy'
    refine ⟨⟨x,hx⟩,(restrictedBasis_piece_iff b P w n _).mpr hxn,?_⟩
    exact Subtype.ext hfx

theorem lift_cycle_from_span_filtration
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (P : I → Prop) (Q : J → Prop) (w : I → ℕ) (v : J → ℕ)
    (f f₀ : X →ₗ[R]Y)
    (hfP : ∀x,x∈Submodule.span R (b '' {i | P i}) → f x∈Submodule.span R (c '' {j | Q j}))
    (hlower : ∀i j,w i≤v j→ c.repr ((f-f₀) (b i)) j=0)
    (hlift : LiftsCycles
      (basisFiltration (Grading.restrictedBasis b P) (fun i => w i.val))
      (basisFiltration (Grading.restrictedBasis c Q) (fun j => v j.val))
      (basisSpanMap b c P Q f hfP))
    (n : ℕ) (x : X) (hxP : x∈Submodule.span R (b '' {i | P i}))
    (hxw : x∈Grading.Piece b w n) (hfx : f₀ x=0) :
    ∃y : X,y∈Submodule.span R (b '' {i | P i}) ∧ f y=0 ∧
      x-y∈(basisFiltration b w).level n := by
  have hxlevel : x∈(basisFiltration b w).level (n+1) := by
    rw [basisFiltration_mem]
    intro i hi
    by_contra hn
    have he := (Grading.mem_piece _ _ _ _).mp hxw i hn
    omega
  have hflevel : f x∈(basisFiltration c v).level n := by
    have hh := basisStrictLower_level b c w v (f-f₀) hlower n x hxlevel
    simpa only [LinearMap.sub_apply,hfx,sub_zero] using hh
  obtain ⟨y,hy,hfy,hxy⟩ := hlift n ⟨x,hxP⟩
    ((restrictedBasis_filtration_iff b P w (n+1) _).mpr hxlevel)
    ((restrictedBasis_filtration_iff c Q v n _).mpr hflevel)
  refine ⟨y.val,y.property,congrArg Subtype.val hfy,?_⟩
  exact (restrictedBasis_filtration_iff b P w n _).mp hxy

end FourPapers.Sublattice
end


end
end

/- BEGIN EXACT BODY: FourPapers.Common.BasisPieceMaps -/
section

section
set_option autoImplicit false
noncomputable section

namespace FourPapers
open Classical CommAlg

variable {R X Y I J Γ A : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- A fine homogeneous vector has its corresponding coarse degree. -/
lemma piece_regrade (b : Module.Basis I R X) (deg : I → Γ) (a : Γ)
    (coarse : Γ → A) {x : X} (hx : x ∈ Grading.Piece b deg a) :
    x ∈ Grading.Piece b (fun i => coarse (deg i)) (coarse a) := by
  apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) hx
  exact congrArg coarse hi

/-- A map that has the required degree on actual basis vectors preserves
every homogeneous span. -/
lemma map_mem_piece_of_basis (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (deg : I → Γ) (degree : J → Γ) (f : X →ₗ[R] Y)
    (hf : ∀ i, f (b i) ∈ Grading.Piece c degree (deg i))
    (a : Γ) {x : X} (hx : x ∈ Grading.Piece b deg a) :
    f x ∈ Grading.Piece c degree a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      change deg i = a at hi
      rw [← hi]
      exact hf i
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Grading.Piece c degree a))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FineCycleAssembly -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
variable {R X Y Z I J L Γ : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]

lemma fineProjection_commutes (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (deg : I → Γ) (deg' : J → Γ) (f : X →ₗ[R] Y)
    (hf : ∀i,f (b i)∈Grading.Piece c deg' (deg i)) (γ : Γ) :
    f.comp (Grading.projection b deg γ)=(Grading.projection c deg' γ).comp f := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply,Grading.projection_basis]
  by_cases hi : deg i=γ
  · rw [if_pos hi]
    exact (Grading.projection_eq_self (hi ▸ hf i)).symm
  · rw [if_neg hi,map_zero]
    exact (Grading.projection_eq_zero (Ne.symm hi) (hf i)).symm

/-- A collection of actual fine-strand fillings assembles to a filling in any
specified union of fine degrees. The sum is the finite support decomposition
of the given cycle; no product/direct-sum surjectivity is assumed. -/
theorem fineCycleFilling_assemble
    (b : Module.Basis I R X) (c : Module.Basis J R Y) (e : Module.Basis L R Z)
    (degX : I → Γ) (degY : J → Γ) (degZ : L → Γ)
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (hg : ∀j,g (c j)∈Grading.Piece e degZ (degY j)) (P : Γ → Prop)
    (hfill : ∀γ,P γ→∀y : Y,y∈Grading.Piece c degY γ→ g y=0→
      ∃x : X,x∈Grading.Piece b degX γ ∧ f x=y)
    (y : Y) (hy : y∈Submodule.span R (c '' {j | P (degY j)})) (hgy : g y=0) :
    ∃x : X,x∈Submodule.span R (b '' {i | P (degX i)}) ∧ f x=y := by
  let S := (c.repr y).support.image degY
  have hP : ∀γ∈S,P γ := by
    intro γ hγ
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hγ
    exact (c.mem_span_image.mp hy) hj
  have hf : ∀γ∈S,∃x : X,x∈Grading.Piece b degX γ ∧
      f x=Grading.projection c degY γ y := by
    intro γ hγ
    apply hfill γ (hP γ hγ) _ (Grading.projection_mem c degY γ y)
    have hh := LinearMap.congr_fun (fineProjection_commutes c e degY degZ g hg γ) y
    change g (Grading.projection c degY γ y)=Grading.projection e degZ γ (g y) at hh
    rw [hh,hgy,map_zero]
  let x : Γ → X := fun γ => if hγ : γ∈S then (hf γ hγ).choose else 0
  have hxmem : ∀γ∈S,x γ∈Submodule.span R (b '' {i | P (degX i)}) := by
    intro γ hγ
    have hx := (hf γ hγ).choose_spec.1
    change x γ∈_
    dsimp only [x]
    rw [dif_pos hγ]
    apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) hx
    change degX i=γ at hi
    change P (degX i)
    rw [hi]
    exact hP γ hγ
  have hxmap : ∀γ∈S,f (x γ)=Grading.projection c degY γ y := by
    intro γ hγ
    simpa only [x,dif_pos hγ] using (hf γ hγ).choose_spec.2
  refine ⟨∑γ∈S,x γ,Submodule.sum_mem _ (fun γ hγ => hxmem γ hγ),?_⟩
  rw [map_sum]
  rw [Finset.sum_congr rfl hxmap]
  exact Grading.sum_projections c degY y

/-- Fine fillings can simultaneously retain a coarse homogeneous degree
and a second weight. The finite support of the input determines the sum;
there is no assumption that an infinite product equals a direct sum. -/
theorem fineCycleFilling_assemble_two_gradings {A : Type*}
    (b : Module.Basis I R X) (c : Module.Basis J R Y) (e : Module.Basis L R Z)
    (degX : I → Γ) (degY : J → Γ) (degZ : L → Γ)
    (coarse : Γ → A) (weight : Γ → ℕ) (a : A) (n : ℕ)
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (hg : ∀j,g (c j)∈Grading.Piece e degZ (degY j))
    (hfill : ∀γ,coarse γ=a→ weight γ=n→∀y : Y,
      y∈Grading.Piece c degY γ→ g y=0→
      ∃x : X,x∈Grading.Piece b degX γ ∧ f x=y)
    (y : Y) (hya : y∈Grading.Piece c (fun j => coarse (degY j)) a)
    (hyn : y∈Grading.Piece c (fun j => weight (degY j)) n) (hgy : g y=0) :
    ∃x : X,x∈Grading.Piece b (fun i => coarse (degX i)) a ∧
      x∈Grading.Piece b (fun i => weight (degX i)) n ∧ f x=y := by
  have hy : y∈Submodule.span R
      (c '' {j | coarse (degY j)=a ∧ weight (degY j)=n}) := by
    apply c.mem_span_image.mpr
    intro j hj
    have hj' := Finsupp.mem_support_iff.mp hj
    exact ⟨(Grading.mem_piece _ _ _ _).mp hya j hj',
      (Grading.mem_piece _ _ _ _).mp hyn j hj'⟩
  obtain ⟨x, hx, hfx⟩ := fineCycleFilling_assemble b c e degX degY degZ f g hg
    (fun γ => coarse γ=a ∧ weight γ=n)
    (fun γ hγ => hfill γ hγ.1 hγ.2) y hy hgy
  refine ⟨x, ?_, ?_, hfx⟩
  · exact Submodule.span_mono (Set.image_mono (fun _ h => h.1)) hx
  · exact Submodule.span_mono (Set.image_mono (fun _ h => h.2)) hx

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerCycleLifting -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.FilteredHomology FourPapers.Universal
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma quotientDifferential_regraded_basis {A : Type*} (B : Family V)
    (deg : Exponent V → A) (p : ℕ) (t : QuotientIndex B (p+1)) :
    quotientDifferential (k := k) B p (quotientCoefficientBasis (k := k) B (p+1) t)∈
      Grading.Piece (quotientCoefficientBasis (k := k) B p) (fun s => deg (quotientDegree s))
        (deg (quotientDegree t)) :=
  piece_regrade _ quotientDegree (quotientDegree t) deg
    (quotientDifferential_homogeneous B _ p (Grading.basis_mem_piece _ _ t))

lemma quotientPreviousDifferential_regraded_basis {A : Type*} (B : Family V)
    (deg : Exponent V → A) (p : ℕ) (t : QuotientIndex B p) :
    quotientPreviousDifferential (k := k) B p (quotientCoefficientBasis (k := k) B p t)∈
      Grading.Piece (quotientCoefficientBasis (k := k) B p.pred) (fun s => deg (quotientDegree s))
        (deg (quotientDegree t)) :=
  piece_regrade _ quotientDegree (quotientDegree t) deg
    (quotientPreviousDifferential_homogeneous (k := k) B p t)

/-- Basis form of homogeneous regrading, used by the actual ideal-coordinate
filtration and independent of any graph cycle-lifting hypothesis. -/
lemma quotientDifferential_basis_regraded {A : Type*} (B : Family V)
    (deg : Exponent V → A) (p : ℕ) (t : QuotientIndex B (p+1)) :
    quotientDifferential (k := k) B p (quotientCoefficientBasis (k := k) B (p+1) t) ∈
      Grading.Piece (quotientCoefficientBasis (k := k) B p)
        (fun s => deg (quotientDegree s)) (deg (quotientDegree t)) :=
  quotientDifferential_regraded_basis (k := k) B deg p t

variable (m : MonomialOrder V) (J : Ideal (MvPolynomial V k))
  (G : Set (MvPolynomial V k)) (hG : m.IsGroebnerBasis G J)
  (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g)) (B : Family V)
  (hstd : ∀a,a∈m.standardMonomials J ↔ QuotientAllowed B a)

def groebnerPreviousDifferential : ∀p : ℕ,
    (Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) →ₗ[k]
      (Set.powersetCard V p.pred →₀ CoefficientQuotient (k := k) B)
  | 0 => 0
  | p+1 => groebnerQuotientDifferential m J G hG hu B hstd p

lemma groebnerPreviousDifferential_comp (p : ℕ) :
    (groebnerPreviousDifferential m J G hG hu B hstd p).comp
      (groebnerQuotientDifferential m J G hG hu B hstd p)=0 := by
  cases p with
  | zero => simp [groebnerPreviousDifferential]
  | succ p => exact groebnerQuotientDifferential_comp m J G hG hu B hstd p

lemma groebnerPreviousDifferential_homogeneous
    {A : Type*} [AddCommMonoid A] (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (a : A) (p : ℕ)
    (x : Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
    (hx : x∈Grading.Piece (quotientCoefficientBasis (k := k) B p)
      (fun s => Finsupp.weight deg (quotientDegree s)) a) :
    groebnerPreviousDifferential m J G hG hu B hstd p x∈
      Grading.Piece (quotientCoefficientBasis (k := k) B p.pred)
        (fun s => Finsupp.weight deg (quotientDegree s)) a := by
  cases p with
  | zero => exact Submodule.zero_mem _
  | succ p => exact groebnerQuotientDifferential_homogeneous m J G hG hu B hstd deg hJ a p x hx

lemma groebnerPreviousDifferential_strictly_lowers (w : V → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    (p : ℕ) (t : QuotientIndex B p) (s : QuotientIndex B p.pred)
    (hw : Finsupp.weight w (quotientDegree t)≤Finsupp.weight w (quotientDegree s)) :
    (quotientCoefficientBasis (k := k) B p.pred).repr
      ((groebnerPreviousDifferential m J G hG hu B hstd p-
        quotientPreviousDifferential (k := k) B p) (quotientCoefficientBasis (k := k) B p t)) s=0 := by
  cases p with
  | zero =>
      simp only [groebnerPreviousDifferential, quotientPreviousDifferential,
        LinearMap.sub_apply, LinearMap.zero_apply, sub_self,
        map_zero, Finsupp.zero_apply]
  | succ p => exact groebnerQuotientDifferential_strictly_lowers m J G hG hu B hstd w htail p t s hw

/-- Vanishing of the necessary monomial quotient homology gives actual cycle
lifts in the corresponding auxiliary component of the genuine `S/J` Koszul
complex. The normal-form matrix, not a postulated degeneration, supplies the
strictly lower weight perturbation. -/
theorem groebnerQuotient_liftsCycles_of_fine_fillings
    (w : V → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    {A : Type*} [AddCommMonoid A] (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg)) (a : A) (p : ℕ)
    (hfill : ∀α : Exponent V,Finsupp.weight deg α=a→
      ∀y : Set.powersetCard V p →₀ CoefficientQuotient (k := k) B,
      y∈quotientPiece (k := k) B α p→quotientPreviousDifferential (k := k) B p y=0→
      ∃x,x∈quotientPiece (k := k) B α (p+1) ∧ quotientDifferential (k := k) B p x=y) :
    LiftsCycles (K := k)
      (X := Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
        (fun t => Finsupp.weight deg (quotientDegree t)) a)
      (Y := Grading.Piece (quotientCoefficientBasis (k := k) B p)
        (fun t => Finsupp.weight deg (quotientDegree t)) a)
      (basisFiltration (K := k) (Grading.restrictedBasis (quotientCoefficientBasis (k := k) B (p+1))
        (fun t => Finsupp.weight deg (quotientDegree t)=a))
        (fun t : {t : QuotientIndex B (p+1) // Finsupp.weight deg (quotientDegree t)=a} =>
          Finsupp.weight w (quotientDegree t.val)))
      (basisFiltration (K := k) (Grading.restrictedBasis (quotientCoefficientBasis (k := k) B p)
        (fun t => Finsupp.weight deg (quotientDegree t)=a))
        (fun t : {t : QuotientIndex B p // Finsupp.weight deg (quotientDegree t)=a} =>
          Finsupp.weight w (quotientDegree t.val)))
      (basisSpanMap (quotientCoefficientBasis (k := k) B (p+1)) (quotientCoefficientBasis (k := k) B p)
        (fun t => Finsupp.weight deg (quotientDegree t)=a)
        (fun t => Finsupp.weight deg (quotientDegree t)=a)
        (groebnerQuotientDifferential m J G hG hu B hstd p)
        (groebnerQuotientDifferential_homogeneous m J G hG hu B hstd deg hJ a p)) := by
  have hf₀P : ∀ x, x ∈ Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a →
      quotientDifferential (k := k) B p x ∈
        Grading.Piece (quotientCoefficientBasis (k := k) B p)
          (fun t => Finsupp.weight deg (quotientDegree t)) a := by
    intro x hx
    exact map_mem_piece_of_basis _ _ _ _ _
      (quotientDifferential_regraded_basis (k := k) B (Finsupp.weight deg) p) a hx
  have hg₀Q : ∀ y, y ∈ Grading.Piece (quotientCoefficientBasis (k := k) B p)
      (fun t => Finsupp.weight deg (quotientDegree t)) a →
      quotientPreviousDifferential (k := k) B p y ∈
        Grading.Piece (quotientCoefficientBasis (k := k) B p.pred)
          (fun t => Finsupp.weight deg (quotientDegree t)) a := by
    intro y hy
    exact map_mem_piece_of_basis _ _ _ _ _
      (quotientPreviousDifferential_regraded_basis (k := k) B (Finsupp.weight deg) p) a hy
  apply basisPerturbation_liftsCycles_on_span (R := k)
    (X := Set.powersetCard V (p+1) →₀ CoefficientQuotient (k := k) B)
    (Y := Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
    (Z := Set.powersetCard V p.pred →₀ CoefficientQuotient (k := k) B)
    (quotientCoefficientBasis (k := k) B (p+1)) (quotientCoefficientBasis (k := k) B p)
    (quotientCoefficientBasis (k := k) B p.pred)
    (fun t => Finsupp.weight deg (quotientDegree t)=a)
    (fun t => Finsupp.weight deg (quotientDegree t)=a)
    (fun t => Finsupp.weight deg (quotientDegree t)=a)
    (fun t => Finsupp.weight w (quotientDegree t))
    (fun t => Finsupp.weight w (quotientDegree t))
    (fun t => Finsupp.weight w (quotientDegree t))
    (groebnerQuotientDifferential m J G hG hu B hstd p) (quotientDifferential (k := k) B p)
    (groebnerPreviousDifferential m J G hG hu B hstd p) (quotientPreviousDifferential (k := k) B p)
    (groebnerQuotientDifferential_homogeneous m J G hG hu B hstd deg hJ a p)
    hf₀P (groebnerPreviousDifferential_homogeneous m J G hG hu B hstd deg hJ a p) hg₀Q
    (quotientDifferential_regraded_basis (k := k) B (Finsupp.weight w) p)
    (quotientPreviousDifferential_regraded_basis (k := k) B (Finsupp.weight w) p)
    (groebnerQuotientDifferential_strictly_lowers m J G hG hu B hstd w htail p)
    (groebnerPreviousDifferential_strictly_lowers m J G hG hu B hstd w htail p)
    (groebnerPreviousDifferential_comp m J G hG hu B hstd p)
  intro n y hya hyn hgy
  exact fineCycleFilling_assemble_two_gradings
      (quotientCoefficientBasis (k := k) B (p+1)) (quotientCoefficientBasis (k := k) B p)
      (quotientCoefficientBasis (k := k) B p.pred) quotientDegree quotientDegree quotientDegree
      (Finsupp.weight deg) (Finsupp.weight w) a n (quotientDifferential (k := k) B p)
      (quotientPreviousDifferential (k := k) B p) (quotientPreviousDifferential_homogeneous (k := k) B p)
      (fun α ha _ => hfill α ha) y hya hyn hgy

theorem groebnerQuotient_lift_cycle_of_fine_fillings
    (w : V → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    {A : Type*} [AddCommMonoid A] (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg)) (a : A) (p : ℕ)
    (hfill : ∀α : Exponent V,Finsupp.weight deg α=a→
      ∀y : Set.powersetCard V p →₀ CoefficientQuotient (k := k) B,
      y∈quotientPiece (k := k) B α p→quotientPreviousDifferential (k := k) B p y=0→
      ∃x,x∈quotientPiece (k := k) B α (p+1) ∧ quotientDifferential (k := k) B p x=y)
    (n : ℕ) (z : Set.powersetCard V (p+1) →₀ CoefficientQuotient (k := k) B)
    (hza : z∈Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a)
    (hzw : z∈Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
      (fun t => Finsupp.weight w (quotientDegree t)) n)
    (hdz : quotientDifferential (k := k) B p z=0) :
    ∃y,y∈Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a ∧
      groebnerQuotientDifferential m J G hG hu B hstd p y=0 ∧
      z-y∈(basisFiltration (K := k) (quotientCoefficientBasis (k := k) B (p+1))
        (fun t => Finsupp.weight w (quotientDegree t))).level n := by
  exact lift_cycle_from_span_filtration
    (quotientCoefficientBasis (k := k) B (p+1)) (quotientCoefficientBasis (k := k) B p)
    (fun t => Finsupp.weight deg (quotientDegree t)=a)
    (fun t => Finsupp.weight deg (quotientDegree t)=a)
    (fun t => Finsupp.weight w (quotientDegree t))
    (fun t => Finsupp.weight w (quotientDegree t))
    (groebnerQuotientDifferential m J G hG hu B hstd p) (quotientDifferential (k := k) B p)
    (groebnerQuotientDifferential_homogeneous m J G hG hu B hstd deg hJ a p)
    (groebnerQuotientDifferential_strictly_lowers m J G hG hu B hstd w htail p)
    (groebnerQuotient_liftsCycles_of_fine_fillings m J G hG hu B hstd w htail deg hJ a p hfill)
    n z hza hzw hdz

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerQuotientMaps -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u v

lemma coordinateDifferential_mapRange {R V : Type u} [CommRing R]
    [Fintype V] [LinearOrder V] (x : V → R) (M N : ModuleCat.{u} R)
    (f : M →ₗ[R] N) (i : ℕ) (z : Set.powersetCard V (i+1) →₀ M) :
    coordinateDifferential x N i (Finsupp.mapRange.linearMap f z)=
      Finsupp.mapRange.linearMap f (coordinateDifferential x M i z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w ihz ihw => simp only [map_add,ihz,ihw]
  | single s c =>
    simp only [Finsupp.mapRange.linearMap_apply,Finsupp.mapRange_single,
      coordinateDifferential_single,map_sum,map_smul,map_zsmul_unit]

variable (V k : Type u) [Fintype V] [LinearOrder V] [CommRing k]

/-- Actual Gröbner data, including the identification with a specified
monomial ideal. The structure stores proofs, never additional axioms. -/
structure QuotientGroebnerData where
  order : MonomialOrder.{u,v} V
  ideal : Ideal (MvPolynomial V k)
  generators : Set (MvPolynomial V k)
  groebner : order.IsGroebnerBasis generators ideal
  unitLeading : ∀g∈generators,g≠0→IsUnit (order.leadingCoeff g)
  family : Family V
  standard : ∀a,a∈order.standardMonomials ideal ↔ QuotientAllowed family a

variable {V k}
namespace QuotientGroebnerData

def coefficientEquiv (P : QuotientGroebnerData V k) :
    CoefficientQuotient (k := k) P.family ≃ₗ[k] MvPolynomial V k ⧸ P.ideal :=
  groebnerCoefficientEquiv P.order P.ideal P.generators P.groebner P.unitLeading P.family P.standard

def coordinates (P : QuotientGroebnerData V k) (i : ℕ) :
    (Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) ≃ₗ[k]
      (Set.powersetCard V i →₀ MvPolynomial V k ⧸ P.ideal) :=
  groebnerKoszulCoordinates P.order P.ideal P.generators P.groebner P.unitLeading P.family P.standard i

def differential (P : QuotientGroebnerData V k) (i : ℕ) :=
  groebnerQuotientDifferential P.order P.ideal P.generators P.groebner
    P.unitLeading P.family P.standard i

def coefficientFactor (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal) :
    CoefficientQuotient (k := k) P.family →ₗ[k] CoefficientQuotient (k := k) Q.family :=
  Q.coefficientEquiv.symm.toLinearMap.comp
    ((Ideal.Quotient.factorₐ k hPQ).toLinearMap.comp P.coefficientEquiv.toLinearMap)

def koszulFactor (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal) (i : ℕ) :
    (Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) →ₗ[k]
      (Set.powersetCard V i →₀ CoefficientQuotient (k := k) Q.family) :=
  (Q.coordinates i).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Ideal.Quotient.factorₐ k hPQ).toLinearMap).comp
      (P.coordinates i).toLinearMap)

lemma koszulFactor_eq_mapRange (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal)
    (i : ℕ) : P.koszulFactor Q hPQ i=Finsupp.mapRange.linearMap (P.coefficientFactor Q hPQ) := by
  apply LinearMap.ext
  intro z
  ext s
  rfl

lemma koszulFactor_chain (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal)
    (i : ℕ) (z : Set.powersetCard V (i+1) →₀ CoefficientQuotient (k := k) P.family) :
    Q.differential i (P.koszulFactor Q hPQ (i+1) z)=
      P.koszulFactor Q hPQ i (P.differential i z) := by
  have hfactor (j : ℕ) (x : Set.powersetCard V j →₀ MvPolynomial V k ⧸ P.ideal) :
      Finsupp.mapRange.linearMap
          (Ideal.Quotient.factorₐ (MvPolynomial V k) hPQ).toLinearMap x =
        Finsupp.mapRange.linearMap (Ideal.Quotient.factorₐ k hPQ).toLinearMap x := by
    ext s
    rfl
  have hh := coordinateDifferential_mapRange
    (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ P.ideal))
    (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ Q.ideal))
    (Ideal.Quotient.factorₐ (MvPolynomial V k) hPQ).toLinearMap i (P.coordinates (i+1) z)
  rw [hfactor,hfactor] at hh
  simpa only [differential,groebnerQuotientDifferential,koszulFactor,
    LinearMap.comp_apply,LinearEquiv.coe_coe,LinearMap.restrictScalars_apply,
    LinearEquiv.apply_symm_apply,coordinates] using
      congrArg (Q.coordinates i).symm hh

lemma coefficientFactor_basis (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal)
    (a : {a // QuotientAllowed P.family a}) :
    P.coefficientFactor Q hPQ (quotientMonomialBasis P.family a)=
      Q.coefficientEquiv.symm (Ideal.Quotient.mk Q.ideal (monomial a.val 1)) := by
  simp only [coefficientFactor,LinearMap.comp_apply,LinearEquiv.coe_coe,coefficientEquiv,
    groebnerCoefficientEquiv_basis,AlgHom.toLinearMap_apply,Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_mk]

def initialCoefficientFactor (P Q : QuotientGroebnerData V k) :
    CoefficientQuotient (k := k) P.family →ₗ[k] CoefficientQuotient (k := k) Q.family :=
  (quotientMonomialBasis P.family).constr k (fun a => quotientMonomial Q.family a.val)

def initialKoszulFactor (P Q : QuotientGroebnerData V k) (i : ℕ) :
    (Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) →ₗ[k]
      (Set.powersetCard V i →₀ CoefficientQuotient (k := k) Q.family) :=
  Finsupp.mapRange.linearMap (P.initialCoefficientFactor Q)

lemma initialCoefficientFactor_basis (P Q : QuotientGroebnerData V k)
    (a : {a // QuotientAllowed P.family a}) :
    P.initialCoefficientFactor Q (quotientMonomialBasis P.family a)=quotientMonomial Q.family a.val := by
  simp only [initialCoefficientFactor,Module.Basis.constr_basis]

lemma koszulFactor_basis (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal)
    (i : ℕ) (t : QuotientIndex P.family i) :
    P.koszulFactor Q hPQ i (quotientCoefficientBasis P.family i t)=
      Finsupp.single t.1 (Q.coefficientEquiv.symm
        (Ideal.Quotient.mk Q.ideal (monomial t.2.val 1))) := by
  rw [koszulFactor_eq_mapRange,quotientCoefficientBasis_apply]
  simp only [Finsupp.mapRange.linearMap_apply,Finsupp.mapRange_single]
  simpa only [quotientMonomialBasis_apply] using
    congrArg (Finsupp.single t.1) (P.coefficientFactor_basis Q hPQ t.2)

lemma initialKoszulFactor_basis (P Q : QuotientGroebnerData V k)
    (i : ℕ) (t : QuotientIndex P.family i) :
    P.initialKoszulFactor Q i (quotientCoefficientBasis P.family i t)=
      Finsupp.single t.1 (quotientMonomial Q.family t.2.val) := by
  rw [quotientCoefficientBasis_apply]
  simp only [initialKoszulFactor,Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single]
  simpa only [quotientMonomialBasis_apply] using
    congrArg (Finsupp.single t.1) (P.initialCoefficientFactor_basis Q t.2)

/-- The actual quotient map has the natural monomial quotient map as its
leading part. Its strict correction bound is proved from normal forms. -/
theorem koszulFactor_strict_correction (P Q : QuotientGroebnerData V k)
    (hPQ : P.ideal≤Q.ideal) (w : V → ℕ)
    (htail : ∀g∈Q.generators,g≠0→∀b∈(monomial (Q.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (Q.order.degree g))
    (i : ℕ) (t : QuotientIndex P.family i) (s : QuotientIndex Q.family i)
    (hw : Finsupp.weight w (quotientDegree t)≤Finsupp.weight w (quotientDegree s)) :
    (quotientCoefficientBasis (k := k) Q.family i).repr
      ((P.koszulFactor Q hPQ i-P.initialKoszulFactor Q i)
        (quotientCoefficientBasis P.family i t)) s=0 := by
  rw [LinearMap.sub_apply,koszulFactor_basis,initialKoszulFactor_basis]
  by_cases ha : QuotientAllowed Q.family t.2.val
  · have hh := groebnerCoefficientEquiv_symm_monomial Q.order Q.ideal Q.generators
      Q.groebner Q.unitLeading Q.family Q.standard ha
    rw [show Q.coefficientEquiv.symm (Ideal.Quotient.mk Q.ideal (monomial t.2.val 1))=
      quotientMonomial Q.family t.2.val from hh,sub_self]
    exact congrArg (fun x : QuotientIndex Q.family i →₀ k => x s)
      (quotientCoefficientBasis (k := k) Q.family i).repr.map_zero
  · rw [quotientMonomial_zero Q.family t.2.val ha,Finsupp.single_zero,sub_zero,
      quotientCoefficientBasis_repr_single]
    by_cases hs : t.1=s.1
    · rw [if_pos hs]
      change (quotientMonomialBasis Q.family).repr
        ((groebnerCoefficientEquiv Q.order Q.ideal Q.generators Q.groebner Q.unitLeading
          Q.family Q.standard).symm (Ideal.Quotient.mk Q.ideal (monomial t.2.val 1))) s.2=0
      rw [groebnerCoefficientEquiv_symm_repr]
      by_contra hc
      have hnf := groebner_normalForm_strictly_lowers_of_tails Q.order Q.ideal Q.generators
        Q.groebner Q.unitLeading w htail t.2.val (fun h => ha ((Q.standard _).mp h))
      have hlt := (mem_restrictSupport_iff k).mp hnf (mem_support_iff.mpr hc)
      change Finsupp.weight w s.2.val < Finsupp.weight w t.2.val at hlt
      simp only [quotientDegree,map_add,hs] at hw
      omega
    · rw [if_neg hs]

lemma initialKoszulFactor_basis_homogeneous {A : Type*}
    (P Q : QuotientGroebnerData V k) (deg : Exponent V → A)
    (i : ℕ) (t : QuotientIndex P.family i) :
    P.initialKoszulFactor Q i (quotientCoefficientBasis P.family i t)∈
      Grading.Piece (quotientCoefficientBasis Q.family i)
        (fun s => deg (quotientDegree s)) (deg (quotientDegree t)) := by
  rw [initialKoszulFactor_basis]
  by_cases ha : QuotientAllowed Q.family t.2.val
  · have hh := Grading.basis_mem_piece (quotientCoefficientBasis (k := k) Q.family i)
      (fun s => deg (quotientDegree s)) (⟨t.1,⟨t.2.val,ha⟩⟩ : QuotientIndex Q.family i)
    simpa only [quotientCoefficientBasis_apply,quotientDegree] using hh
  · rw [quotientMonomial_zero Q.family t.2.val ha,Finsupp.single_zero]
    exact Submodule.zero_mem _

theorem koszulFactor_preserves_weight (P Q : QuotientGroebnerData V k)
    (hPQ : P.ideal≤Q.ideal) (w : V → ℕ)
    (htail : ∀g∈Q.generators,g≠0→∀b∈(monomial (Q.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (Q.order.degree g)) (i : ℕ) :
    FourPapers.FilteredHomology.Preserves
      (basisFiltration (quotientCoefficientBasis (k := k) P.family i)
        (fun t => Finsupp.weight w (quotientDegree t)))
      (basisFiltration (quotientCoefficientBasis (k := k) Q.family i)
        (fun t => Finsupp.weight w (quotientDegree t))) (P.koszulFactor Q hPQ i) :=
  basisPerturbation_preserves _ _ _ _ _ _
    (P.initialKoszulFactor_basis_homogeneous Q (Finsupp.weight w) i)
    (P.koszulFactor_strict_correction Q hPQ w htail i)

theorem koszulFactor_basis_homogeneous {A : Type*} [AddCommMonoid A]
    (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal) (deg : V → A)
    (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (i : ℕ) (t : QuotientIndex P.family i) :
    P.koszulFactor Q hPQ i (quotientCoefficientBasis P.family i t)∈
      Grading.Piece (quotientCoefficientBasis Q.family i)
        (fun s => Finsupp.weight deg (quotientDegree s))
        (Finsupp.weight deg (quotientDegree t)) := by
  rw [koszulFactor_basis,Grading.mem_piece]
  intro s hs
  rw [quotientCoefficientBasis_repr_single] at hs
  split_ifs at hs with hface
  · change (quotientMonomialBasis Q.family).repr
      ((groebnerCoefficientEquiv Q.order Q.ideal Q.generators Q.groebner Q.unitLeading
        Q.family Q.standard).symm (Ideal.Quotient.mk Q.ideal (monomial t.2.val 1))) s.2≠0 at hs
    rw [groebnerCoefficientEquiv_symm_repr] at hs
    have hnf := groebner_normalForm_homogeneous Q.order Q.ideal Q.generators Q.groebner
      Q.unitLeading deg hQ (Finsupp.weight deg t.2.val) (monomial t.2.val 1)
      (isWeightedHomogeneous_monomial deg _ _ rfl)
    have hh := hnf hs
    simp only [quotientDegree,map_add,hface,hh]
  · exact (hs rfl).elim

theorem koszulFactor_homogeneous {A : Type*} [AddCommMonoid A]
    (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal) (deg : V → A)
    (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg)) (i : ℕ)
    (a : A) (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family)
    (hz : z∈Grading.Piece (quotientCoefficientBasis P.family i)
      (fun t => Finsupp.weight deg (quotientDegree t)) a) :
    P.koszulFactor Q hPQ i z∈Grading.Piece (quotientCoefficientBasis Q.family i)
      (fun t => Finsupp.weight deg (quotientDegree t)) a :=
  map_mem_piece_of_basis _ _ _ _ _ (P.koszulFactor_basis_homogeneous Q hPQ deg hQ i) a hz

/-- An actual lifted cycle remains a lift after passing from a clique ideal
to a larger graph ideal. The leading map is the literal monomial quotient
map, and its correction is controlled in the same filtration. -/
theorem koszulFactor_transfers_lift {A : Type*} [AddCommMonoid A]
    (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal) (deg : V → A)
    (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (w : V → ℕ)
    (htail : ∀g∈Q.generators,g≠0→∀b∈(monomial (Q.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (Q.order.degree g))
    (p n : ℕ) (a : A)
    (z y : Set.powersetCard V (p+1) →₀ CoefficientQuotient (k := k) P.family)
    (hzw : z∈Grading.Piece (quotientCoefficientBasis P.family (p+1))
      (fun t => Finsupp.weight w (quotientDegree t)) n)
    (hya : y∈Grading.Piece (quotientCoefficientBasis P.family (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a)
    (hdy : P.differential p y=0)
    (herr : z-y∈(basisFiltration (quotientCoefficientBasis P.family (p+1))
      (fun t => Finsupp.weight w (quotientDegree t))).level n) :
    P.koszulFactor Q hPQ (p+1) y∈Grading.Piece (quotientCoefficientBasis Q.family (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a ∧
    Q.differential p (P.koszulFactor Q hPQ (p+1) y)=0 ∧
    P.initialKoszulFactor Q (p+1) z-P.koszulFactor Q hPQ (p+1) y∈
      (basisFiltration (quotientCoefficientBasis Q.family (p+1))
        (fun t => Finsupp.weight w (quotientDegree t))).level n := by
  refine ⟨P.koszulFactor_homogeneous Q hPQ deg hQ (p+1) a y hya,?_,?_⟩
  · rw [P.koszulFactor_chain Q hPQ p y,hdy,map_zero]
  · have hzlevel : z∈(basisFiltration (quotientCoefficientBasis P.family (p+1))
        (fun t => Finsupp.weight w (quotientDegree t))).level (n+1) := by
      rw [←Grading.projection_eq_self hzw]
      exact basisProjection_level _ _ n z
    have hlower := basisStrictLower_level _ _ _ _
      (P.koszulFactor Q hPQ (p+1)-P.initialKoszulFactor Q (p+1))
      (P.koszulFactor_strict_correction Q hPQ w htail (p+1)) n z hzlevel
    have hmap := P.koszulFactor_preserves_weight Q hPQ w htail (p+1) n (z-y) herr
    have he : P.initialKoszulFactor Q (p+1) z-P.koszulFactor Q hPQ (p+1) y=
        P.koszulFactor Q hPQ (p+1) (z-y)-
          (P.koszulFactor Q hPQ (p+1)-P.initialKoszulFactor Q (p+1)) z := by
      simp only [map_sub,LinearMap.sub_apply]
      abel
    rw [he]
    exact Submodule.sub_mem _ hmap hlower

/-- Transport the unique natural-number action explicitly when auxiliary
degrees are represented by products or finitely supported functions. -/
theorem koszulFactor_transfers_lift_withNatModule {A : Type*} [AddCommMonoid A] [hNat : Module ℕ A] [hDec : DecidableEq A]
    (P Q : QuotientGroebnerData V k) (hPQ : P.ideal≤Q.ideal) (deg : V → A)
    (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (w : V → ℕ)
    (htail : ∀g∈Q.generators,g≠0→∀b∈(monomial (Q.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (Q.order.degree g))
    (p n : ℕ) (a : A)
    (z y : Set.powersetCard V (p+1) →₀ CoefficientQuotient (k := k) P.family)
    (hzw : z∈Grading.Piece (quotientCoefficientBasis P.family (p+1))
      (fun t => Finsupp.weight w (quotientDegree t)) n)
    (hya : y∈Grading.Piece (quotientCoefficientBasis P.family (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a)
    (hdy : P.differential p y=0)
    (herr : z-y∈(basisFiltration (quotientCoefficientBasis P.family (p+1))
      (fun t => Finsupp.weight w (quotientDegree t))).level n) :
    P.koszulFactor Q hPQ (p+1) y∈Grading.Piece (quotientCoefficientBasis Q.family (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a ∧
    Q.differential p (P.koszulFactor Q hPQ (p+1) y)=0 ∧
    P.initialKoszulFactor Q (p+1) z-P.koszulFactor Q hPQ (p+1) y∈
      (basisFiltration (quotientCoefficientBasis Q.family (p+1))
        (fun t => Finsupp.weight w (quotientDegree t))).level n := by
  have hd : hDec = Classical.decEq A := Subsingleton.elim _ _
  subst hDec
  have he : hNat = (AddCommMonoid.toNatModule : Module ℕ A) := Subsingleton.elim _ _
  subst hNat
  exact P.koszulFactor_transfers_lift Q hPQ deg hQ w htail p n a z y hzw hya hdy herr

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FineCycleLiftingAssembly -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg FourPapers.Universal FourPapers.FilteredHomology
variable {R X Y I J Γ A : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- Fine cycle lifts assemble by the actual finite support decomposition.
The error lies in one common lower submodule, and every summand of the lift
retains the prescribed coarse degree. -/
theorem fineCycleLifting_assemble_two_gradings
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (deg : I → Γ) (degree : J → Γ) (coarse : Γ → A) (weight : Γ → ℕ)
    (a : A) (n : ℕ) (D d : X →ₗ[R]Y)
    (hd : ∀i,d (b i)∈Grading.Piece c degree (deg i)) (L : Submodule R X)
    (hlift : ∀γ,coarse γ=a→weight γ=n→∀x : X,
      x∈Grading.Piece b deg γ→d x=0→
      ∃y : X,y∈Grading.Piece b (fun i => coarse (deg i)) a ∧ D y=0 ∧ x-y∈L)
    (x : X) (hxa : x∈Grading.Piece b (fun i => coarse (deg i)) a)
    (hxn : x∈Grading.Piece b (fun i => weight (deg i)) n) (hdx : d x=0) :
    ∃y : X,y∈Grading.Piece b (fun i => coarse (deg i)) a ∧ D y=0 ∧ x-y∈L := by
  let S := (b.repr x).support.image deg
  have hcoarse : ∀γ∈S,coarse γ=a ∧ weight γ=n := by
    intro γ hγ
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hγ
    have hne := Finsupp.mem_support_iff.mp hi
    exact ⟨(Grading.mem_piece _ _ _ _).mp hxa i hne,
      (Grading.mem_piece _ _ _ _).mp hxn i hne⟩
  have hpieces : ∀γ∈S,∃y : X,
      y∈Grading.Piece b (fun i => coarse (deg i)) a ∧ D y=0 ∧
        Grading.projection b deg γ x-y∈L := by
    intro γ hγ
    apply hlift γ (hcoarse γ hγ).1 (hcoarse γ hγ).2 _ (Grading.projection_mem _ _ _ _)
    have hh := LinearMap.congr_fun (fineProjection_commutes b c deg degree d hd γ) x
    simpa only [LinearMap.comp_apply,hdx,map_zero] using hh
  let y : Γ → X := fun γ => if hγ : γ∈S then (hpieces γ hγ).choose else 0
  have hy : ∀γ∈S,y γ∈Grading.Piece b (fun i => coarse (deg i)) a ∧ D (y γ)=0 ∧
      Grading.projection b deg γ x-y γ∈L := by
    intro γ hγ
    simpa only [y,dif_pos hγ] using (hpieces γ hγ).choose_spec
  refine ⟨∑γ∈S,y γ,Submodule.sum_mem _ (fun γ hγ => (hy γ hγ).1),?_,?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero (fun γ hγ => (hy γ hγ).2.1)
  · have hh := Submodule.sum_mem L (fun γ hγ => (hy γ hγ).2.2)
    simpa only [Finset.sum_sub_distrib,S,Grading.sum_projections] using hh

/-- Actual lifts of all leading homogeneous cycles imply the literal
filtered lifting property. The proof removes the lower part of the input,
uses its genuine leading cycle, then restores the lower part of the error. -/
theorem basisLeadingCycles_liftsCycles
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (w : I → ℕ) (v : J → ℕ) (D d : X →ₗ[R]Y)
    (hd : ∀i,d (b i)∈Grading.Piece c v (w i))
    (hδ : ∀i j,w i≤v j→c.repr ((D-d) (b i)) j=0)
    (hlift : ∀n,∀x : X,x∈Grading.Piece b w n→d x=0→
      ∃y : X,D y=0 ∧ x-y∈(basisFiltration b w).level n) :
    LiftsCycles (basisFiltration b w) (basisFiltration c v) D := by
  intro n x hx hDx
  let z := Grading.projection b w n x
  have hz : z∈Grading.Piece b w n := Grading.projection_mem _ _ _ _
  have hδx : (D-d) x∈(basisFiltration c v).level n :=
    basisStrictLower_level b c w v (D-d) hδ n x hx
  have hdx : d x∈(basisFiltration c v).level n := by
    have hh := Submodule.sub_mem _ hDx hδx
    simpa only [LinearMap.sub_apply,sub_sub_cancel] using hh
  have hdz : d z=0 := by
    have hh := LinearMap.congr_fun (basisProjection_commutes b c w v d hd n) x
    change d z=Grading.projection c v n (d x) at hh
    rw [hh,basisProjection_lower_zero c v n (d x) hdx]
  obtain ⟨y,hDy,hzy⟩ := hlift n z hz hdz
  have hxy : x-y∈(basisFiltration b w).level n := by
    have hh := Submodule.add_mem _ (basisProjection_error_lower b w n x hx) hzy
    simpa only [z,sub_add_sub_cancel] using hh
  have hy : y∈(basisFiltration b w).level (n+1) := by
    have hh := Submodule.sub_mem _ hx
      ((basisFiltration b w).mono (Nat.le_succ n) hxy)
    simpa only [sub_sub_cancel] using hh
  exact ⟨y,hy,hDy,hxy⟩

/-- The same implication confined to actual source and target homogeneous
submodules. Every preservation and lower-weight condition is inherited from
the given literal maps, and the resulting lift remains in the source piece. -/
theorem basisLeadingCycles_liftsCycles_on_span
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (P : I → Prop) (Q : J → Prop) (w : I → ℕ) (v : J → ℕ)
    (D d : X →ₗ[R]Y)
    (hDP : ∀x,x∈Submodule.span R (b '' {i | P i})→
      D x∈Submodule.span R (c '' {j | Q j}))
    (hdP : ∀x,x∈Submodule.span R (b '' {i | P i})→
      d x∈Submodule.span R (c '' {j | Q j}))
    (hd : ∀i,d (b i)∈Grading.Piece c v (w i))
    (hδ : ∀i j,w i≤v j→c.repr ((D-d) (b i)) j=0)
    (hlift : ∀n,∀x : X,x∈Submodule.span R (b '' {i | P i})→
      x∈Grading.Piece b w n→d x=0→∃y : X,
      y∈Submodule.span R (b '' {i | P i}) ∧ D y=0 ∧ x-y∈(basisFiltration b w).level n) :
    LiftsCycles
      (basisFiltration (Grading.restrictedBasis b P) (fun i => w i.val))
      (basisFiltration (Grading.restrictedBasis c Q) (fun j => v j.val))
      (basisSpanMap b c P Q D hDP) := by
  let Dr := basisSpanMap b c P Q D hDP
  let dr := basisSpanMap b c P Q d hdP
  apply basisLeadingCycles_liftsCycles (Grading.restrictedBasis b P)
    (Grading.restrictedBasis c Q) (fun i => w i.val) (fun j => v j.val) Dr dr
  · intro i
    apply (restrictedBasis_piece_iff c Q v (w i.val) _).mpr
    simpa only [dr,basisSpanMap_val,Grading.restrictedBasis_val] using hd i.val
  · intro i j hij
    rw [restrictedBasis_repr]
    change c.repr ((D-d) ((Grading.restrictedBasis b P i).val)) j.val=0
    rw [Grading.restrictedBasis_val]
    exact hδ i.val j.val hij
  · intro n x hx hdx
    have hdx' : d x.val=0 := congrArg Subtype.val hdx
    obtain ⟨y,hy,hDy,hxy⟩ := hlift n x.val x.property
      ((restrictedBasis_piece_iff b P w n x).mp hx) hdx'
    refine ⟨⟨y,hy⟩,Subtype.ext hDy,?_⟩
    exact (restrictedBasis_filtration_iff b P w n (x-⟨y,hy⟩)).mpr hxy

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphBasisDecomposition -/
section

/-! # Finite coarsening of an actual basis grading

The equivalence is the literal family of homogeneous coefficient
projections; its inverse adds the finitely many fine components. A second
equivalence flattens the nested ordinary-degree/weight submodule. These
identifications do not change the underlying chain vectors.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg

variable {R X I Γ A : Type*} [CommRing R] [AddCommGroup X] [Module R X]

lemma fineProjection_coefficient (b : Module.Basis I R X) (deg : I → Γ)
    (γ : Γ) (x : X) (i : I) :
    b.repr (Grading.projection b deg γ x) i = if deg i = γ then b.repr x i else 0 := by
  simp only [Grading.projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Grading.filterMap_apply, Finsupp.filter_apply]

def basisCoarseningEquivPi (b : Module.Basis I R X) (deg : I → Γ)
    (coarse : Γ → A) (a : A) [Finite {γ : Γ // coarse γ = a}] :
    Grading.Piece b (fun i => coarse (deg i)) a ≃ₗ[R]
      ∀ γ : {γ : Γ // coarse γ = a}, Grading.Piece b deg γ.val := by
  letI : Fintype {γ : Γ // coarse γ = a} := Fintype.ofFinite _
  exact
    { toFun := fun x γ => ⟨Grading.projection b deg γ.val x.val,
        Grading.projection_mem b deg γ.val x.val⟩
      invFun := fun y => ⟨∑ γ, (y γ).val, Submodule.sum_mem _ (fun γ _ => by
        simpa only [γ.property] using piece_regrade b deg γ.val coarse (y γ).property)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply b.repr.injective
        ext i
        simp only [map_sum, Finsupp.finset_sum_apply, fineProjection_coefficient]
        by_cases hz : b.repr x.val i = 0
        · simp only [hz, ite_self, Finset.sum_const_zero]
        · have hi := (Grading.mem_piece b (fun i => coarse (deg i)) a x.val).mp
            x.property i hz
          let γ : {γ : Γ // coarse γ = a} := ⟨deg i, hi⟩
          rw [Finset.sum_eq_single γ]
          · simp only [γ, ite_true]
          · intro η _ hηγ
            apply if_neg
            intro he
            exact hηγ (Subtype.ext he.symm)
          · simp
      right_inv := by
        intro y
        funext γ
        apply Subtype.ext
        change Grading.projection b deg γ.val (∑ η, (y η).val) = (y γ).val
        rw [map_sum, Finset.sum_eq_single γ]
        · exact Grading.projection_eq_self (y γ).property
        · intro η _ hηγ
          apply Grading.projection_eq_zero _ (y η).property
          intro he
          exact hηγ (Subtype.ext he.symm)
        · simp
      map_add' := by
        intro x y
        funext γ
        apply Subtype.ext
        exact map_add (Grading.projection b deg γ.val) x.val y.val
      map_smul' := by
        intro r x
        funext γ
        apply Subtype.ext
        exact map_smul (Grading.projection b deg γ.val) r x.val }

@[simp] lemma basisCoarseningEquivPi_apply (b : Module.Basis I R X) (deg : I → Γ)
    (coarse : Γ → A) (a : A) [Finite {γ : Γ // coarse γ = a}]
    (x : Grading.Piece b (fun i => coarse (deg i)) a)
    (γ : {γ : Γ // coarse γ = a}) :
    (basisCoarseningEquivPi b deg coarse a x γ).val =
      Grading.projection b deg γ.val x.val := rfl

lemma basis_pair_piece_iff (b : Module.Basis I R X) (v w : I → ℕ)
    (q n : ℕ) (x : X) :
    x ∈ Grading.Piece b (fun i => (v i, w i)) (q,n) ↔
      x ∈ Grading.Piece b v q ∧ x ∈ Grading.Piece b w n := by
  rw [Grading.mem_piece, Grading.mem_piece, Grading.mem_piece]
  constructor
  · intro h
    exact ⟨fun i hi => congrArg Prod.fst (h i hi),
      fun i hi => congrArg Prod.snd (h i hi)⟩
  · rintro ⟨hv, hw⟩ i hi
    exact Prod.ext (hv i hi) (hw i hi)

/-- Flattening two successive basis restrictions retains the actual vector
and imposes the pair of degree conditions. -/
def basisIteratedPieceEquiv (b : Module.Basis I R X) (v w : I → ℕ) (q n : ℕ) :
    Grading.Piece (Grading.restrictedBasis b (fun i => v i = q))
        (fun i => w i.val) n ≃ₗ[R]
      Grading.Piece b (fun i => (v i, w i)) (q,n) where
  toFun x := ⟨x.val.val, (basis_pair_piece_iff b v w q n x.val.val).mpr
    ⟨x.val.property, (restrictedBasis_piece_iff b (fun i => v i = q) w n x.val).mp x.property⟩⟩
  invFun y :=
    ⟨⟨y.val, ((basis_pair_piece_iff b v w q n y.val).mp y.property).1⟩,
      (restrictedBasis_piece_iff b (fun i => v i = q) w n _).mpr
        ((basis_pair_piece_iff b v w q n y.val).mp y.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma basisIteratedPieceEquiv_val (b : Module.Basis I R X) (v w : I → ℕ)
    (q n : ℕ)
    (x : Grading.Piece (Grading.restrictedBasis b (fun i => v i = q))
      (fun i => w i.val) n) :
    (basisIteratedPieceEquiv b v w q n x).val = x.val.val := rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphAmbientKoszul -/
section

/-! # The ambient polynomial Koszul complex and its filtered quotient map

The empty monomial family gives the literal polynomial quotient by the zero
ideal. Its standard monomial coordinates are used only as coordinates: all
maps below are the actual quotient map, its standard-monomial section, and
the usual Koszul differential. Positive fine strands contract by exterior
creation in a variable with positive exponent.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma emptyFamily_allowed (a : Exponent V) : QuotientAllowed (∅ : Family V) a := by
  simp [QuotientAllowed, Contains]

abbrev polynomialQuotientData (m : MonomialOrder V) : QuotientGroebnerData V k where
  order := m
  ideal := ⊥
  generators := ∅
  groebner := MonomialOrder.IsGroebnerBasis.mk (Set.empty_subset _) (by simp)
  unitLeading := by simp
  family := ∅
  standard := by
    intro a
    simp [MonomialOrder.mem_standardMonomials_iff, QuotientAllowed, Contains]

abbrev AmbientKoszulCoordinates (p : ℕ) :=
  Set.powersetCard V p →₀ CoefficientQuotient (k := k) (∅ : Family V)

lemma polynomialQuotientData_differential (m : MonomialOrder V) (p : ℕ) :
    (polynomialQuotientData (k := k) m).differential p =
      quotientDifferential (k := k) (∅ : Family V) p := by
  apply (quotientCoefficientBasis (k := k) (∅ : Family V) (p+1)).ext
  intro t
  rw [QuotientGroebnerData.differential, groebnerQuotientDifferential_basis,
    quotientDifferential_basis]
  apply Finset.sum_congr rfl
  intro j _
  rw [dif_pos (emptyFamily_allowed _),
    groebnerCoefficientEquiv_symm_monomial _ _ _ _ _ _ _ (emptyFamily_allowed _),
    quotientCoefficientBasis_apply]
  rfl

def ambientKoszulProjection (P : QuotientGroebnerData V k) (p : ℕ) :
    AmbientKoszulCoordinates (k := k) (V := V) p →ₗ[k]
      (Set.powersetCard V p →₀ CoefficientQuotient (k := k) P.family) :=
  (polynomialQuotientData P.order).koszulFactor P bot_le p

def ambientInitialProjection (P : QuotientGroebnerData V k) (p : ℕ) :
    AmbientKoszulCoordinates (k := k) (V := V) p →ₗ[k]
      (Set.powersetCard V p →₀ CoefficientQuotient (k := k) P.family) :=
  (polynomialQuotientData P.order).initialKoszulFactor P p

def ambientCoefficientSection (P : QuotientGroebnerData V k) :
    CoefficientQuotient (k := k) P.family →ₗ[k]
      CoefficientQuotient (k := k) (∅ : Family V) :=
  (quotientMonomialBasis (k := k) P.family).constr k (fun a => quotientMonomial (k := k) ∅ a.val)

def ambientKoszulSection (P : QuotientGroebnerData V k) (p : ℕ) :
    (Set.powersetCard V p →₀ CoefficientQuotient (k := k) P.family) →ₗ[k]
      AmbientKoszulCoordinates (k := k) (V := V) p :=
  Finsupp.mapRange.linearMap (ambientCoefficientSection P)

@[simp] lemma ambientKoszulSection_basis (P : QuotientGroebnerData V k) (p : ℕ)
    (t : QuotientIndex P.family p) :
    ambientKoszulSection P p (quotientCoefficientBasis (k := k) P.family p t) =
      quotientCoefficientBasis (k := k) (∅ : Family V) p
        ⟨t.1, ⟨t.2.val, emptyFamily_allowed _⟩⟩ := by
  rw [quotientCoefficientBasis_apply, quotientCoefficientBasis_apply]
  change Finsupp.mapRange (ambientCoefficientSection P)
      (ambientCoefficientSection P).map_zero
      (Finsupp.single t.1 (quotientMonomial (k := k) P.family t.2.val)) = _
  rw [Finsupp.mapRange_single]
  rw [← quotientMonomialBasis_apply P.family t.2,
    ambientCoefficientSection, Module.Basis.constr_basis]

theorem ambientKoszulProjection_section (P : QuotientGroebnerData V k) (p : ℕ) :
    (ambientKoszulProjection P p).comp (ambientKoszulSection P p) = LinearMap.id := by
  apply (quotientCoefficientBasis (k := k) P.family p).ext
  intro t
  rw [LinearMap.comp_apply, ambientKoszulSection_basis]
  change (polynomialQuotientData P.order).koszulFactor P bot_le p _ = _
  rw [QuotientGroebnerData.koszulFactor_basis]
  rw [show P.coefficientEquiv.symm (Ideal.Quotient.mk P.ideal (monomial t.2.val 1)) =
      quotientMonomial (k := k) P.family t.2.val from
    groebnerCoefficientEquiv_symm_monomial P.order P.ideal P.generators
      P.groebner P.unitLeading P.family P.standard t.2.property]
  exact (quotientCoefficientBasis_apply P.family p t.1 t.2).symm

lemma ambientKoszulSection_initialProjection_standard (P : QuotientGroebnerData V k)
    (p : ℕ) (t : QuotientIndex (∅ : Family V) p) (ht : QuotientAllowed P.family t.2.val) :
    ambientKoszulSection P p
      (ambientInitialProjection P p (quotientCoefficientBasis (k := k) ∅ p t)) =
        quotientCoefficientBasis (k := k) ∅ p t := by
  rw [ambientInitialProjection, QuotientGroebnerData.initialKoszulFactor_basis]
  have he : Finsupp.single t.1 (quotientMonomial (k := k) P.family t.2.val) =
      quotientCoefficientBasis (k := k) P.family p ⟨t.1, ⟨t.2.val, ht⟩⟩ :=
    (quotientCoefficientBasis_apply P.family p t.1 ⟨t.2.val, ht⟩).symm
  rw [he, ambientKoszulSection_basis]

theorem ambientKoszulProjection_chain (P : QuotientGroebnerData V k) (p : ℕ) :
    (ambientKoszulProjection P p).comp (quotientDifferential (k := k) ∅ p) =
      (P.differential p).comp (ambientKoszulProjection P (p+1)) := by
  apply LinearMap.ext
  intro x
  have h := (polynomialQuotientData P.order).koszulFactor_chain P bot_le p x
  rw [polynomialQuotientData_differential] at h
  exact h.symm

theorem ambientInitialProjection_chain (P : QuotientGroebnerData V k) (p : ℕ) :
    (ambientInitialProjection P p).comp (quotientDifferential (k := k) ∅ p) =
      (quotientDifferential (k := k) P.family p).comp (ambientInitialProjection P (p+1)) := by
  apply (quotientCoefficientBasis (k := k) (∅ : Family V) (p+1)).ext
  intro t
  rw [LinearMap.comp_apply, LinearMap.comp_apply, quotientDifferential_basis]
  simp only [ambientInitialProjection]
  rw [QuotientGroebnerData.initialKoszulFactor_basis, map_sum]
  rw [show quotientDifferential (k := k) P.family p
      (Finsupp.single t.1 (quotientMonomial (k := k) P.family t.2.val)) =
      ∑ j : {j // j∈t.1.val},
        TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val •
          Finsupp.single (eraseIndex t.1 j)
            (quotientMonomial (k := k) P.family (t.2.val+Finsupp.single j.val 1)) by
      change coordinateDifferential (X : V → MvPolynomial V k)
        (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) P.family)) p
        (Finsupp.single t.1 (quotientMonomial (k := k) P.family t.2.val)) = _
      rw [coordinateDifferential_single]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_comm (X j.val), quotientMonomial_mul_variable]
      simp only [Finsupp.smul_single]]
  apply Finset.sum_congr rfl
  intro j _
  rw [dif_pos (emptyFamily_allowed _), map_zsmul_unit,
    QuotientGroebnerData.initialKoszulFactor_basis]
  rfl

lemma ambientKoszulSection_basis_fine (P : QuotientGroebnerData V k) (p : ℕ)
    (t : QuotientIndex P.family p) :
    ambientKoszulSection P p (quotientCoefficientBasis (k := k) P.family p t) ∈
      quotientPiece (k := k) ∅ (quotientDegree t) p := by
  rw [ambientKoszulSection_basis]
  exact Grading.basis_mem_piece
    (quotientCoefficientBasis (k := k) (∅ : Family V) p) quotientDegree
    ⟨t.1, ⟨t.2.val, emptyFamily_allowed _⟩⟩

lemma basisHomogeneous_preserves {X Y I J : Type*}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (b : Module.Basis I k X) (c : Module.Basis J k Y)
    (w : I → ℕ) (v : J → ℕ) (f : X →ₗ[k] Y)
    (hf : ∀ i, f (b i) ∈ Grading.Piece c v (w i)) :
    Preserves (basisFiltration b w) (basisFiltration c v) f := by
  intro n x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact Submodule.span_mono (Set.image_mono (fun j hj => by
        change v j < n
        change v j = w i at hj
        rw [hj]
        exact hi)) (hf i)
  | zero => simpa only [map_zero] using ((basisFiltration c v).level n).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem ambientKoszulSection_preserves_weight (P : QuotientGroebnerData V k)
    (w : V → ℕ) (p : ℕ) :
    Preserves
      (basisFiltration (quotientCoefficientBasis (k := k) P.family p)
        (fun t => Finsupp.weight w (quotientDegree t)))
      (basisFiltration (quotientCoefficientBasis (k := k) (∅ : Family V) p)
        (fun t => Finsupp.weight w (quotientDegree t))) (ambientKoszulSection P p) :=
  basisHomogeneous_preserves
    (quotientCoefficientBasis (k := k) P.family p)
    (quotientCoefficientBasis (k := k) (∅ : Family V) p)
    (fun t => Finsupp.weight w (quotientDegree t))
    (fun t => Finsupp.weight w (quotientDegree t)) (ambientKoszulSection P p)
    (fun t => piece_regrade (quotientCoefficientBasis (k := k) (∅ : Family V) p)
      quotientDegree (quotientDegree t) (Finsupp.weight w)
      (ambientKoszulSection_basis_fine P p t))

/-- Every positive fine polynomial Koszul cycle has a filling in the same
fine degree and the next exterior degree, over the original ring. -/
theorem ambientKoszul_fine_filling (α : Exponent V) (hα : α ≠ 0) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := k) (V := V) p)
    (hx : x ∈ quotientPiece (k := k) ∅ α p)
    (hdx : quotientPreviousDifferential (k := k) ∅ p x = 0) :
    ∃ y, y ∈ quotientPiece (k := k) ∅ α (p+1) ∧ quotientDifferential (k := k) ∅ p y = x := by
  obtain ⟨e, he⟩ : ∃ e, 0 < α e := by
    by_contra! h
    apply hα
    ext e
    exact Nat.eq_zero_of_le_zero (h e)
  have hu : UnusedVariable (∅ : Family V) e := by simp [UnusedVariable]
  apply quotientCoordinate_filling_of_face_filling ∅ α p ?_ x hx hdx
  intro z hz hdz
  refine ⟨quotientTotalCreation ∅ α e z, quotientTotalCreation_raises hu he p z hz, ?_⟩
  have hc := LinearMap.congr_fun (quotientTotalCreation_contracts (k := k) hu he) z
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hdz, map_zero, add_zero] using hc

theorem ambientInitialProjection_zero_degree_injective
    (P : QuotientGroebnerData V k) (hzero : QuotientAllowed P.family 0) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := k) (V := V) p)
    (hx : x ∈ quotientPiece (k := k) ∅ 0 p)
    (hq : ambientInitialProjection P p x = 0) : x = 0 := by
  have hs : ambientKoszulSection P p (ambientInitialProjection P p x) = x := by
    clear hq
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        have ha : t.2.val = 0 := (add_eq_zero.mp ht).1
        exact ambientKoszulSection_initialProjection_standard P p t (by simpa only [ha] using hzero)
    | zero => simp
    | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
    | smul r x hx ih => simp only [map_smul, ih]
  rw [hq, map_zero] at hs
  exact hs.symm

lemma ambientInitialProjection_basis_fine (P : QuotientGroebnerData V k)
    (p : ℕ) (t : QuotientIndex (∅ : Family V) p) :
    ambientInitialProjection P p (quotientCoefficientBasis (k := k) ∅ p t) ∈
      quotientPiece (k := k) P.family (quotientDegree t) p :=
  (polynomialQuotientData P.order).initialKoszulFactor_basis_homogeneous P id p t

/-- The ambient polynomial filling of a leading ideal cycle. The only
exceptional polynomial Koszul strand, fine degree zero, is ruled out by
the literal initial quotient map and the allowed constant monomial. -/
theorem ambientKoszul_leading_filling (P : QuotientGroebnerData V k)
    (hzero : QuotientAllowed P.family 0) (w : V → ℕ) (p n : ℕ)
    (x : AmbientKoszulCoordinates (k := k) (V := V) p)
    (hx : x ∈ Grading.Piece (quotientCoefficientBasis (k := k) ∅ p)
      (fun a => Finsupp.weight w (quotientDegree a)) n)
    (hdx : quotientPreviousDifferential (k := k) ∅ p x = 0)
    (hqx : ambientInitialProjection P p x = 0) :
    ∃ y, y ∈ Grading.Piece (quotientCoefficientBasis (k := k) ∅ (p+1))
      (fun a => Finsupp.weight w (quotientDegree a)) n ∧ quotientDifferential (k := k) ∅ p y = x := by
  let b := quotientCoefficientBasis (k := k) (∅ : Family V) p
  let S := (b.repr x).support.image quotientDegree
  have hweight (α : Exponent V) (hα : α ∈ S) : Finsupp.weight w α = n := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hα
    exact (Grading.mem_piece _ _ _ _).mp hx a (Finsupp.mem_support_iff.mp ha)
  have hfill (α : Exponent V) (hα : α ∈ S) :
      ∃ y, y ∈ quotientPiece (k := k) ∅ α (p+1) ∧
        quotientDifferential (k := k) ∅ p y = Grading.projection b quotientDegree α x := by
    let z := Grading.projection b quotientDegree α x
    have hz : z ∈ quotientPiece (k := k) ∅ α p := Grading.projection_mem _ _ _ _
    have hdz : quotientPreviousDifferential (k := k) ∅ p z = 0 := by
      have h := LinearMap.congr_fun (fineProjection_commutes b
        (quotientCoefficientBasis (k := k) (∅ : Family V) p.pred)
        quotientDegree quotientDegree (quotientPreviousDifferential (k := k) ∅ p)
        (quotientPreviousDifferential_homogeneous ∅ p) α) x
      simpa only [LinearMap.comp_apply, hdx, map_zero] using h
    have hqz : ambientInitialProjection P p z = 0 := by
      have h := LinearMap.congr_fun (fineProjection_commutes b
        (quotientCoefficientBasis (k := k) P.family p) quotientDegree quotientDegree
        (ambientInitialProjection P p) (ambientInitialProjection_basis_fine P p) α) x
      simpa only [LinearMap.comp_apply, hqx, map_zero] using h
    by_cases hα0 : α = 0
    · subst α
      have hz0 := ambientInitialProjection_zero_degree_injective P hzero p z hz hqz
      exact ⟨0, Submodule.zero_mem _, by simpa only [map_zero] using hz0.symm⟩
    · exact ambientKoszul_fine_filling α hα0 p z hz hdz
  let y : Exponent V → AmbientKoszulCoordinates (k := k) (V := V) (p+1) :=
    fun α => if hα : α ∈ S then (hfill α hα).choose else 0
  have hy (α : Exponent V) (hα : α ∈ S) :
      y α ∈ quotientPiece (k := k) ∅ α (p+1) ∧
        quotientDifferential (k := k) ∅ p (y α) = Grading.projection b quotientDegree α x := by
    simpa only [y, dif_pos hα] using (hfill α hα).choose_spec
  refine ⟨∑ α ∈ S, y α, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro α hα
    simpa only [hweight α hα] using
      piece_regrade _ _ _ (Finsupp.weight w) (hy α hα).1
  · rw [map_sum, Finset.sum_congr rfl (fun α hα => (hy α hα).2)]
    exact Grading.sum_projections b quotientDegree x

/-- A near-cycle in the kernel of the actual polynomial quotient map has
an ambient primitive up to strictly lower weight. This is the exact input
needed by the filtered connecting construction. -/
theorem ambientKoszul_near_cycle_primitive (P : QuotientGroebnerData V k)
    (hzero : QuotientAllowed P.family 0) (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
    (p n : ℕ) (x : AmbientKoszulCoordinates (k := k) (V := V) p)
    (hx : x ∈ (basisFiltration (quotientCoefficientBasis (k := k) ∅ p)
      (fun a => Finsupp.weight w (quotientDegree a))).level (n+1))
    (hdx : quotientPreviousDifferential (k := k) ∅ p x ∈
      (basisFiltration (quotientCoefficientBasis (k := k) ∅ p.pred)
        (fun a => Finsupp.weight w (quotientDegree a))).level n)
    (hqx : ambientKoszulProjection P p x = 0) :
    ∃ y, y ∈ (basisFiltration (quotientCoefficientBasis (k := k) ∅ (p+1))
      (fun a => Finsupp.weight w (quotientDegree a))).level (n+1) ∧
      x-quotientDifferential (k := k) ∅ p y ∈
        (basisFiltration (quotientCoefficientBasis (k := k) ∅ p)
          (fun a => Finsupp.weight w (quotientDegree a))).level n := by
  let b := quotientCoefficientBasis (k := k) (∅ : Family V) p
  let wt : QuotientIndex (∅ : Family V) p → ℕ :=
    fun a => Finsupp.weight w (quotientDegree a)
  let z := Grading.projection b wt n x
  have hz : z ∈ Grading.Piece b wt n := Grading.projection_mem _ _ _ _
  have hdz : quotientPreviousDifferential (k := k) ∅ p z = 0 := by
    have h := LinearMap.congr_fun (basisProjection_commutes b
      (quotientCoefficientBasis (k := k) (∅ : Family V) p.pred) wt
      (fun a => Finsupp.weight w (quotientDegree a)) (quotientPreviousDifferential (k := k) ∅ p)
      (fun a => piece_regrade _ _ _ (Finsupp.weight w)
        (quotientPreviousDifferential_homogeneous ∅ p a)) n) x
    change quotientPreviousDifferential (k := k) ∅ p z = _ at h
    rw [h, LinearMap.comp_apply, basisProjection_lower_zero _ _ n _ hdx]
  have hqi : ambientInitialProjection P p x ∈
      (basisFiltration (quotientCoefficientBasis (k := k) P.family p)
        (fun a => Finsupp.weight w (quotientDegree a))).level n := by
    have hδ := basisStrictLower_level b (quotientCoefficientBasis (k := k) P.family p) wt
      (fun a => Finsupp.weight w (quotientDegree a))
      (ambientKoszulProjection P p-ambientInitialProjection P p)
      ((polynomialQuotientData P.order).koszulFactor_strict_correction P bot_le w htail p)
      n x hx
    have hn := ((basisFiltration (quotientCoefficientBasis (k := k) P.family p)
      (fun a => Finsupp.weight w (quotientDegree a))).level n).neg_mem hδ
    simpa only [LinearMap.sub_apply, hqx, zero_sub, neg_neg] using hn
  have hqz : ambientInitialProjection P p z = 0 := by
    have h := LinearMap.congr_fun (basisProjection_commutes b
      (quotientCoefficientBasis (k := k) P.family p) wt
      (fun a => Finsupp.weight w (quotientDegree a)) (ambientInitialProjection P p)
      (fun a => piece_regrade _ _ _ (Finsupp.weight w)
        (ambientInitialProjection_basis_fine P p a)) n) x
    change ambientInitialProjection P p z = _ at h
    rw [h, LinearMap.comp_apply, basisProjection_lower_zero _ _ n _ hqi]
  obtain ⟨y, hy, hdy⟩ := ambientKoszul_leading_filling P hzero w p n z hz hdz hqz
  refine ⟨y, ?_, ?_⟩
  · apply Submodule.span_mono ?_ hy
    apply Set.image_mono
    intro a ha
    change Finsupp.weight w (quotientDegree a) < n+1
    change Finsupp.weight w (quotientDegree a) = n at ha
    rw [ha]
    exact Nat.lt_succ_self n
  · rw [hdy]
    exact basisProjection_error_lower b wt n x hx

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealCycleLifting -/
section

/-! # Passing actual leading-cycle lifts from a quotient to its ideal

This is the filtered connecting argument for the literal short exact
sequence of Koszul complexes. A polynomial lift is corrected using a
quotient cycle lift and then differentiated. Its image lies in the actual
kernel, is an actual cycle, and differs from the prescribed element by a
strictly lower filtered term.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section

namespace FourPapers.FilteredHomology
open Classical

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

def kernelFiltration (F : Filtration (K := R) A) (q : A →ₗ[R] B) :
    Filtration (K := R) (LinearMap.ker q) where
  level n := (F.level n).comap (LinearMap.ker q).subtype
  zero := by simp only [F.zero, Submodule.comap_bot, Submodule.ker_subtype]
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive x := F.exhaustive x.val

section Connecting
variable {A₂ A₁ A₀ B₂ B₁ B₀ : Type*}
  [AddCommGroup A₂] [Module R A₂] [AddCommGroup A₁] [Module R A₁]
  [AddCommGroup A₀] [Module R A₀] [AddCommGroup B₂] [Module R B₂]
  [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₀] [Module R B₀]
  (F₂ : Filtration (K := R) A₂) (F₁ : Filtration (K := R) A₁)
  (F₀ : Filtration (K := R) A₀)
  (G₂ : Filtration (K := R) B₂) (G₁ : Filtration (K := R) B₁)
  (d₁ : A₂ →ₗ[R] A₁) (d₀ : A₁ →ₗ[R] A₀)
  (D₁ : B₂ →ₗ[R] B₁) (D₀ : B₁ →ₗ[R] B₀)
  (q₂ : A₂ →ₗ[R] B₂) (q₁ : A₁ →ₗ[R] B₁) (q₀ : A₀ →ₗ[R] B₀)
  (hcomm₀ : q₀.comp d₀ = D₀.comp q₁)

include hcomm₀ in
def kernelDifferential : LinearMap.ker q₁ →ₗ[R] LinearMap.ker q₀ :=
  (d₀.domRestrict (LinearMap.ker q₁)).codRestrict _ (by
    intro x
    change q₀ (d₀ x.val) = 0
    calc
      q₀ (d₀ x.val) = D₀ (q₁ x.val) := LinearMap.congr_fun hcomm₀ x.val
      _ = 0 := by
        rw [show q₁ x.val = 0 from x.property, map_zero])

/-- The ambient approximation hypothesis is the actual fine polynomial
Koszul contraction, restricted to positive ordinary degrees. It will be
discharged using creation of a variable with positive fine exponent. -/
theorem liftsCycles_kernel_of_quotient
    (hdd : d₀.comp d₁ = 0) (hcomm₁ : q₁.comp d₁ = D₁.comp q₂)
    (s₂ : B₂ →ₗ[R] A₂) (hsection : q₂.comp s₂ = LinearMap.id)
    (hd₁ : Preserves F₂ F₁ d₁)
    (hq₂ : Preserves F₂ G₂ q₂) (hq₁ : Preserves F₁ G₁ q₁)
    (hs₂ : Preserves G₂ F₂ s₂)
    (hquot : LiftsCycles G₂ G₁ D₁)
    (hambient : ∀ n (x : LinearMap.ker q₁), x.val ∈ F₁.level (n+1) →
      d₀ x.val ∈ F₀.level n →
      ∃ y, y ∈ F₂.level (n+1) ∧ x.val - d₁ y ∈ F₁.level n) :
    LiftsCycles (kernelFiltration F₁ q₁) (kernelFiltration F₀ q₀)
      (kernelDifferential d₀ D₀ q₁ q₀ hcomm₀) := by
  intro n x hx hdx
  have hcomm₁_apply (a : A₂) : q₁ (d₁ a) = D₁ (q₂ a) := LinearMap.congr_fun hcomm₁ a
  have hsection_apply (b : B₂) : q₂ (s₂ b) = b := LinearMap.congr_fun hsection b
  have hxzero : q₁ x.val = 0 := x.property
  obtain ⟨y, hy, herr⟩ := hambient n x hx hdx
  have hqdy : D₁ (q₂ y) ∈ G₁.level n := by
    have he : d₁ y - x.val ∈ F₁.level n := by
      simpa only [neg_sub] using (F₁.level n).neg_mem herr
    have h := hq₁ n _ he
    simpa only [map_sub, hxzero, sub_zero, hcomm₁_apply y] using h
  obtain ⟨z, hz, hDz, hqerr⟩ := hquot n (q₂ y) (hq₂ (n+1) y hy) hqdy
  let a := y - s₂ (q₂ y - z)
  have hsa : s₂ (q₂ y - z) ∈ F₂.level n := hs₂ n _ hqerr
  have ha : a ∈ F₂.level (n+1) :=
    (F₂.level (n+1)).sub_mem hy (F₂.mono (Nat.le_succ n) hsa)
  have hqa : q₂ a = z := by
    dsimp only [a]
    rw [map_sub, hsection_apply]
    abel
  have hdqa : q₁ (d₁ a) = 0 := by
    rw [hcomm₁_apply, hqa, hDz]
  let zI : LinearMap.ker q₁ := ⟨d₁ a, hdqa⟩
  refine ⟨zI, hd₁ (n+1) a ha, ?_, ?_⟩
  · apply Subtype.ext
    exact LinearMap.congr_fun hdd a
  · change x.val - d₁ a ∈ F₁.level n
    have he : x.val - d₁ a = (x.val - d₁ y) + d₁ (s₂ (q₂ y - z)) := by
      dsimp only [a]
      rw [map_sub]
      abel
    rw [he]
    exact (F₁.level n).add_mem herr (hd₁ n _ hsa)

end Connecting
end FourPapers.FilteredHomology

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def quotientCoordinateFiltration (B : Family V) (w : V → ℕ) (p : ℕ) :
    Filtration (K := k) (Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) :=
  basisFiltration (K := k)
    (X := Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
    (quotientCoefficientBasis (k := k) B p)
    (fun a => Finsupp.weight w (quotientDegree a))

lemma ambientKoszulProjection_previous_chain (P : QuotientGroebnerData V k) (p : ℕ) :
    (ambientKoszulProjection P p.pred).comp (quotientPreviousDifferential (k := k) ∅ p) =
      (groebnerPreviousDifferential P.order P.ideal P.generators P.groebner
        P.unitLeading P.family P.standard p).comp (ambientKoszulProjection P p) := by
  cases p with
  | zero => simp only [quotientPreviousDifferential, groebnerPreviousDifferential,
      LinearMap.comp_zero, LinearMap.zero_comp]
  | succ p => exact ambientKoszulProjection_chain P p

def ambientKernelDifferential (P : QuotientGroebnerData V k) (p : ℕ) :
    LinearMap.ker (ambientKoszulProjection P p) →ₗ[k]
      LinearMap.ker (ambientKoszulProjection P p.pred) :=
  kernelDifferential (quotientPreviousDifferential ∅ p)
    (groebnerPreviousDifferential P.order P.ideal P.generators P.groebner
      P.unitLeading P.family P.standard p)
    (ambientKoszulProjection P p) (ambientKoszulProjection P p.pred)
    (ambientKoszulProjection_previous_chain P p)

theorem ambientKernel_cycle_lifts (P : QuotientGroebnerData V k)
    (hzero : QuotientAllowed P.family 0) (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
    (p : ℕ)
    (hquot : LiftsCycles (quotientCoordinateFiltration P.family w (p+1))
      (quotientCoordinateFiltration P.family w p) (P.differential p)) :
    LiftsCycles
      (kernelFiltration (quotientCoordinateFiltration ∅ w p) (ambientKoszulProjection P p))
      (kernelFiltration (quotientCoordinateFiltration ∅ w p.pred)
        (ambientKoszulProjection P p.pred)) (ambientKernelDifferential P p) := by
  refine liftsCycles_kernel_of_quotient
    (quotientCoordinateFiltration ∅ w (p+1)) (quotientCoordinateFiltration ∅ w p)
    (quotientCoordinateFiltration ∅ w p.pred)
    (quotientCoordinateFiltration P.family w (p+1))
    (quotientCoordinateFiltration P.family w p)
    (quotientDifferential ∅ p) (quotientPreviousDifferential ∅ p)
    (P.differential p)
    (groebnerPreviousDifferential P.order P.ideal P.generators P.groebner
      P.unitLeading P.family P.standard p)
    (ambientKoszulProjection P (p+1)) (ambientKoszulProjection P p)
    (ambientKoszulProjection P p.pred) (ambientKoszulProjection_previous_chain P p)
    ?_ (ambientKoszulProjection_chain P p) (ambientKoszulSection P (p+1))
    (ambientKoszulProjection_section P (p+1)) ?_ ?_ ?_
    (ambientKoszulSection_preserves_weight P w (p+1)) hquot ?_
  · cases p with
    | zero => simp only [quotientPreviousDifferential, LinearMap.zero_comp]
    | succ p => exact quotientDifferential_comp ∅ p
  · exact basisHomogeneous_preserves _ _ _ _ _
      (quotientDifferential_basis_regraded ∅ (Finsupp.weight w) p)
  · exact (polynomialQuotientData P.order).koszulFactor_preserves_weight P bot_le w htail (p+1)
  · exact (polynomialQuotientData P.order).koszulFactor_preserves_weight P bot_le w htail p
  · intro n x hx hdx
    exact ambientKoszul_near_cycle_primitive P hzero w htail p n x.val hx hdx x.property

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerIdealBasis -/
section

/-! # An actual triangular basis of an arbitrary ideal

For every nonstandard monomial `u`, the polynomial `u - normalForm u` belongs
to the ideal. These polynomials form a basis of the ideal as a module over
the coefficient ring, provided the given Gröbner basis has unit leading
coefficients.
Their nonstandard coefficients are the identity matrix, and their remaining
terms are strictly smaller in the original monomial order. This gives ideal
coordinates without replacing the ideal by an unproved flat family.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped MonomialOrder
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K V : Type*} [CommRing K] [Nontrivial K]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : Set (MvPolynomial V K)) (hG : m.IsGroebnerBasis G J)
  (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev NonstandardIndex := {a : V →₀ ℕ // a ∉ m.standardMonomials J}

def idealLift (a : NonstandardIndex m J) : J :=
  ⟨monomial a.val 1 - hG.normalForm hu (monomial a.val 1),
    hG.sub_normalForm_mem hu _⟩

theorem normalForm_coeff_nonstandard (f : MvPolynomial V K)
    (a : NonstandardIndex m J) : (hG.normalForm hu f).coeff a.val = 0 := by
  by_contra h
  exact a.property ((mem_restrictSupport_iff K).mp
    (hG.normalForm_mem_restrictSupport hu f) (mem_support_iff.mpr h))

theorem idealLift_nonstandard_coeff (a b : NonstandardIndex m J) :
    (idealLift m J G hG hu a).val.coeff b.val = if a = b then 1 else 0 := by
  change (monomial a.val (1 : K) - hG.normalForm hu (monomial a.val 1)).coeff b.val = _
  rw [coeff_sub, normalForm_coeff_nonstandard m J G hG hu]
  simp only [sub_zero, coeff_monomial]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ (Subtype.ext h₁)).elim
  · exact (h₁ (congrArg Subtype.val h₂)).elim
  · rfl

def idealCoefficientMap : J →ₗ[K] (NonstandardIndex m J →₀ K) :=
  (Finsupp.lsubtypeDomain {a : V →₀ ℕ | a ∉ m.standardMonomials J}).comp
    ((MvPolynomial.basisMonomials V K).repr.toLinearMap.comp (J.restrictScalars K).subtype)

@[simp] theorem idealCoefficientMap_apply (f : J) (a : NonstandardIndex m J) :
    idealCoefficientMap m J f a = f.val.coeff a.val := rfl

theorem idealCoefficientMap_lift (a : NonstandardIndex m J) :
    idealCoefficientMap m J (idealLift m J G hG hu a) = Finsupp.single a 1 := by
  ext b
  rw [idealCoefficientMap_apply, idealLift_nonstandard_coeff]
  simp only [Finsupp.single_apply]

theorem idealLift_linearIndependent : LinearIndependent K (idealLift m J G hG hu) := by
  apply LinearIndependent.of_comp (idealCoefficientMap m J)
  have he : idealCoefficientMap m J ∘ idealLift m J G hG hu =
      fun a : NonstandardIndex m J => Finsupp.single a (1 : K) :=
    funext (idealCoefficientMap_lift m J G hG hu)
  rw [he]
  exact Finsupp.linearIndependent_single_one K (NonstandardIndex m J)

theorem idealLift_spans :
    (⊤ : Submodule K J) ≤ Submodule.span K (Set.range (idealLift m J G hG hu)) := by
  let T := Submodule.span K (Set.range (idealLift m J G hG hu))
  intro x _
  have hx : x.val ∈ T.map (J.restrictScalars K).subtype := by
    have hnf : hG.normalForm hu x.val = 0 := (hG.normalForm_eq_zero_iff hu).mpr x.property
    have he : ((LinearMap.id : MvPolynomial V K →ₗ[K] MvPolynomial V K) -
        hG.normalForm hu) x.val = x.val := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, hnf, sub_zero]
    rw [← he]
    apply polynomialLinearMap_mem
    intro a _
    by_cases ha : a ∈ m.standardMonomials J
    · have hfix : hG.normalForm hu (monomial a 1) = monomial a 1 :=
        hG.normalForm_of_mem_restrictSupport hu (by simpa using ha)
      simp only [LinearMap.sub_apply, LinearMap.id_apply, hfix, sub_self]
      exact Submodule.zero_mem _
    · exact ⟨idealLift m J G hG hu ⟨a, ha⟩,
        Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  obtain ⟨y, hy, he⟩ := hx
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

def groebnerIdealBasis : Module.Basis (NonstandardIndex m J) K J :=
  Module.Basis.mk (idealLift_linearIndependent m J G hG hu)
    (idealLift_spans m J G hG hu)

@[simp] theorem groebnerIdealBasis_apply (a : NonstandardIndex m J) :
    groebnerIdealBasis m J G hG hu a = idealLift m J G hG hu a :=
  Module.Basis.mk_apply _ _ _

theorem groebnerIdealBasis_repr (f : J) (a : NonstandardIndex m J) :
    (groebnerIdealBasis m J G hG hu).repr f a = f.val.coeff a.val := by
  have he : idealCoefficientMap m J = (groebnerIdealBasis m J G hG hu).repr.toLinearMap := by
    apply (groebnerIdealBasis m J G hG hu).ext
    intro b
    change idealCoefficientMap m J (groebnerIdealBasis m J G hG hu b) =
      (groebnerIdealBasis m J G hG hu).repr (groebnerIdealBasis m J G hG hu b)
    rw [(groebnerIdealBasis m J G hG hu).repr_self, groebnerIdealBasis_apply,
      idealCoefficientMap_lift]
  exact (congrArg (fun h : J →ₗ[K] (NonstandardIndex m J →₀ K) => h f a) he).symm

/-- Normal forms of a nonstandard monomial have strictly smaller terms in
the original term order, without introducing a numerical weight vector. -/
theorem normalForm_support_lt_termOrder (a : NonstandardIndex m J)
    (b : V →₀ ℕ) (hb : b ∈ (hG.normalForm hu (monomial a.val 1)).support) :
    b ≺[m] a.val := by
  let f := hG.normalForm hu (monomial a.val 1)
  have hf : f ≠ 0 := by
    intro h
    have hb' : b ∈ f.support := hb
    rw [h, support_zero] at hb'
    exact Finset.notMem_empty b hb'
  have hstd : m.degree f ∈ m.standardMonomials J :=
    (mem_restrictSupport_iff K).mp (hG.normalForm_mem_restrictSupport hu _)
      (m.degree_mem_support hf)
  have hlt : m.degree f ≺[m] a.val := by
    by_contra hn
    have hle : m.toSyn a.val ≤ m.toSyn (m.degree f) := le_of_not_gt hn
    rcases lt_or_eq_of_le hle with hlt | he
    · have hdeg : m.degree (f - monomial a.val 1) = m.degree f := by
        apply m.degree_sub_of_lt
        simpa only [m.degree_monomial, one_ne_zero, ite_false] using hlt
      have hJ : f - monomial a.val 1 ∈ J := by
        simpa only [neg_sub] using J.neg_mem (hG.sub_normalForm_mem hu (monomial a.val 1))
      have hne : f - monomial a.val 1 ≠ 0 := by
        intro hz
        have heq : f = monomial a.val 1 := sub_eq_zero.mp hz
        have hdegf : m.degree f = a.val := by
          simp only [heq, m.degree_monomial, one_ne_zero, ite_false]
        exact (lt_irrefl (m.toSyn a.val)) (hdegf ▸ hlt)
      exact hstd _ hJ hne (hdeg ▸ le_rfl)
    · exact a.property (by simpa only [m.toSyn.injective he] using hstd)
  exact (m.le_degree hb).trans_lt hlt

def monomialOrderBound (n : m.syn) : Submodule K (MvPolynomial V K) :=
  restrictSupport K {a : V →₀ ℕ | m.toSyn a ≤ n}

theorem idealLift_mem_orderBound (a : NonstandardIndex m J) :
    (idealLift m J G hG hu a).val ∈ monomialOrderBound m (m.toSyn a.val) := by
  apply (monomialOrderBound m (m.toSyn a.val)).sub_mem
  · simp [monomialOrderBound]
  · rw [monomialOrderBound, mem_restrictSupport_iff]
    intro b hb
    exact (normalForm_support_lt_termOrder m J G hG hu a b hb).le

theorem idealLift_homogeneous {Γ : Type*} [AddCommMonoid Γ]
    (deg : V → Γ)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K deg))
    (a : NonstandardIndex m J) :
    IsWeightedHomogeneous deg (idealLift m J G hG hu a).val
      (Finsupp.weight deg a.val) := by
  have hm := isWeightedHomogeneous_monomial deg a.val (1 : K) rfl
  exact hm.sub (groebner_normalForm_homogeneous m J G hG hu deg hJ _ _ hm)

/-- The ideal's actual term-order filtration agrees with the filtration by
the leading monomial indices of its triangular basis. -/
theorem ideal_mem_orderBound_iff (f : J) (n : m.syn) :
    f.val ∈ monomialOrderBound m n ↔
      ∀ a ∈ ((groebnerIdealBasis m J G hG hu).repr f).support, m.toSyn a.val ≤ n := by
  constructor
  · intro hf a ha
    apply (mem_restrictSupport_iff K).mp hf
    change a.val ∈ f.val.support
    rw [MvPolynomial.mem_support_iff]
    have h := Finsupp.mem_support_iff.mp ha
    rwa [groebnerIdealBasis_repr] at h
  · intro hf
    rw [← (groebnerIdealBasis m J G hG hu).linearCombination_repr f]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
      Submodule.coe_smul, groebnerIdealBasis_apply]
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    have hb := idealLift_mem_orderBound m J G hG hu a
    rw [monomialOrderBound, mem_restrictSupport_iff] at hb ⊢
    intro b hb'
    exact (hb hb').trans (hf a ha)

include hG hu in
/-- The basis indices are precisely the monomials in the actual initial
ideal. The unit-leading-coefficient hypothesis is what makes this statement
valid over a general coefficient ring. -/
theorem monomial_mem_initial_iff_not_standard (a : V →₀ ℕ) :
    monomial a (1 : K) ∈ Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K))) ↔
      a ∉ m.standardMonomials J := by
  constructor
  · intro ha hstd
    have hs : a ∈ m.standardMonomials
        (Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))) := by
      rwa [m.standardMonomials_span_leadingTerm]
    apply hs (monomial a 1) ha (by simp)
    simp only [m.degree_monomial, one_ne_zero, ite_false, le_refl]
  · intro ha
    rw [hG.mem_standardMonomials_iff] at ha
    push_neg at ha
    obtain ⟨g, hg, hg0, hga⟩ := ha
    have hlead : m.leadingTerm g ∈
        Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K))) :=
      Ideal.subset_span ⟨g, hG.subset hg, rfl⟩
    have hmon := (m.leadingTerm_mem_iff
      ((Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))).restrictScalars K) (hu g hg hg0)).mp hlead
    exact (Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))).mem_of_dvd
      (monomial_one_dvd_monomial_one.mpr hga) hmon

def nonstandardInitialIndexEquiv : NonstandardIndex m J ≃
    {a : V →₀ ℕ // monomial a (1 : K) ∈
      Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))} where
  toFun a := ⟨a.val, (monomial_mem_initial_iff_not_standard m J G hG hu a.val).mpr a.property⟩
  invFun a := ⟨a.val, (monomial_mem_initial_iff_not_standard m J G hG hu a.val).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hG hu in
/-- Every nonzero coefficient of an element of the initial ideal is attached
to a monomial that itself belongs to that ideal. The proof uses the given
unit leading coefficients; no field hypothesis is inserted here. -/
theorem monomial_mem_initial_of_coeff_ne_zero
    (f : MvPolynomial V K)
    (hf : f ∈ Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K))))
    (a : V →₀ ℕ) (ha : f.coeff a ≠ 0) :
    monomial a (1 : K) ∈ Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K))) := by
  have hfG : f ∈ Ideal.span (m.leadingTerm '' G) := by
    rwa [← hG.span_leadingTerm_image]
  obtain ⟨g, hg, hg0, hga⟩ := m.exists_degree_le_of_mem_span_leadingTerm hfG
    (mem_support_iff.mpr ha)
  have hlead : m.leadingTerm g ∈
      Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K))) :=
    Ideal.subset_span ⟨g, hG.subset hg, rfl⟩
  have hmon := (m.leadingTerm_mem_iff
    ((Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))).restrictScalars K) (hu g hg hg0)).mp hlead
  exact (Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))).mem_of_dvd
      (monomial_one_dvd_monomial_one.mpr hga) hmon

end FourPapers.Sublattice

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped MonomialOrder

variable {K V : Type*} [Field K]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))

/-- The ideal itself is a Gröbner basis over a field. This canonical choice
removes any finite-generation or user-supplied-basis hypothesis from the ideal
coordinate construction. -/
def canonicalIdealBasis : Module.Basis (NonstandardIndex m J) K J :=
  groebnerIdealBasis m J (J : Set (MvPolynomial V K)) (m.isGroebnerBasis_self J)
    (fun g _ hg => m.isUnit_leadingCoeff.mpr hg)

end FourPapers.Sublattice

end
end
end


end
