module
public import Mathlib
namespace PalomarFermion
universe uDictionary
/-- Exact identity inverse-pair law at the ring dictionary. -/
public theorem coefficientIdentityInvPair {R : Type uDictionary} [CommRing R] : RingHomInvPair (RingHom.id R) (RingHom.id R) := by infer_instance
/-- Exact identity inverse-pair law at the commutative-semiring dictionary. -/
public theorem coefficientCommutativeIdentityInvPair {R : Type uDictionary} [hR : CommRing R] : @RingHomInvPair R R hR.toCommSemiring.toSemiring hR.toCommSemiring.toSemiring (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) := by infer_instance
/-- Exact identity-surjectivity law at the ring dictionary. -/
public theorem coefficientIdentitySurjective {R : Type uDictionary} [CommRing R] : RingHomSurjective (RingHom.id R) := by infer_instance
/-- Exact identity-surjectivity law at the commutative-semiring dictionary. -/
public theorem coefficientCommutativeIdentitySurjective {R : Type uDictionary} [hR : CommRing R] : @RingHomSurjective R R hR.toCommSemiring.toSemiring hR.toCommSemiring.toSemiring (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) := by infer_instance
/-- The primitive finite set of polynomial indices. -/
public theorem finiteCoordinates (n : ℕ) : Finite (Fin n) := by infer_instance
/-- The primitive finite set of the two separately labeled exterior families. -/
public theorem finiteOddCoordinates (n : ℕ) : Finite (Fin n ⊕ Fin n) := by infer_instance
attribute [instance 2000] coefficientIdentityInvPair coefficientIdentitySurjective
attribute [instance 2100] coefficientCommutativeIdentityInvPair coefficientCommutativeIdentitySurjective finiteCoordinates finiteOddCoordinates
universe uCoordinateModule uCoordinateIndex
/-- The same exact basis coordinates, with both identity inverse-pair projection arguments explicit. -/
public abbrev coordinates {R : Type uDictionary} [CommRing R] {M : Type uCoordinateModule} {I : Type uCoordinateIndex} [AddCommGroup M] [Module R M] (b : Module.Basis I R M) : M →ₗ[R] (I →₀ R) :=
  @LinearEquiv.toLinearMap R R _ _ (RingHom.id R) (RingHom.id R)
    (coefficientCommutativeIdentityInvPair (R := R)) (coefficientCommutativeIdentityInvPair (R := R))
    M (I →₀ R) _ _ _ _ b.repr
/-- Pointwise equality with the original imported basis coordinate accessor. -/
@[simp] public theorem coordinates_apply {R : Type uDictionary} [CommRing R] {M : Type uCoordinateModule} {I : Type uCoordinateIndex} [AddCommGroup M] [Module R M] (b : Module.Basis I R M) (x : M) : coordinates b x = b.repr x := rfl
end PalomarFermion

section BatchFile_2
/- Literal source: PaperVerification/FermionFilteredModuleSpanning.lean -/


/-!
# Descending reduction in an actual weighted basis

This is a module statement, so it applies to a noncommutative superalgebra
without replacing its ideal by a commutative one. Homogeneous relation
vectors may have any index type. Every relation used in the reduction is
replaced by an actual filtered lift, and the finite basis support supplies
the terminating degree bound.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ)

def component (d : ℕ) : M →ₗ[R] M where
  toFun x := b.repr.symm ((b.repr x).filter (fun i ↦ w i = d))
  map_add' x y := by rw [map_add,Finsupp.filter_add,map_add]
  map_smul' a x := by rw [map_smul,Finsupp.filter_smul,map_smul,RingHom.id_apply]

@[simp] theorem repr_component (d : ℕ) (x : M) (i : I) :
    b.repr (component b w d x) i = if w i = d then b.repr x i else 0 := by
  simp only [component,LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.apply_symm_apply,
    Finsupp.filter_apply]

def Bound (d : ℕ) (x : M) : Prop := ∀ i, PalomarFermion.coordinates b x i ≠ 0 → w i ≤ d

def Homogeneous (d : ℕ) (x : M) : Prop := ∀ i, PalomarFermion.coordinates b x i ≠ 0 → w i = d

def HasTop (d : ℕ) (x y : M) : Prop := Bound b w d x ∧ component b w d x = y

theorem bound_zero (d : ℕ) : Bound b w d 0 := by
  intro i hi
  exact (hi (by simp)).elim

theorem bound_add {d : ℕ} {x y : M} (hx : Bound b w d x) (hy : Bound b w d y) :
    Bound b w d (x+y) := by
  change ∀ i, b.repr x i ≠ 0 → w i ≤ d at hx
  change ∀ i, b.repr y i ≠ 0 → w i ≤ d at hy
  change ∀ i, b.repr (x+y) i ≠ 0 → w i ≤ d
  intro i hi
  by_cases hxi : b.repr x i = 0
  · apply hy i
    simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
  · exact hx i hxi

theorem bound_sub {d : ℕ} {x y : M} (hx : Bound b w d x) (hy : Bound b w d y) :
    Bound b w d (x-y) := by
  change ∀ i, b.repr x i ≠ 0 → w i ≤ d at hx
  change ∀ i, b.repr y i ≠ 0 → w i ≤ d at hy
  change ∀ i, b.repr (x-y) i ≠ 0 → w i ≤ d
  intro i hi
  by_cases hxi : b.repr x i = 0
  · apply hy i
    intro hyi
    apply hi
    simp only [map_sub,Finsupp.sub_apply,hxi,hyi,sub_self]
  · exact hx i hxi

theorem bound_smul {d : ℕ} {x : M} (hx : Bound b w d x) (a : R) :
    Bound b w d (a • x) := by
  intro i hi
  apply hx i
  intro hz
  apply hi
  simp only [map_smul,Finsupp.smul_apply,hz,smul_zero]

theorem HasTop.zero (d : ℕ) : HasTop b w d 0 0 :=
  ⟨bound_zero b w d,map_zero _⟩

theorem HasTop.add {d : ℕ} {x x₀ y y₀ : M}
    (hx : HasTop b w d x x₀) (hy : HasTop b w d y y₀) :
    HasTop b w d (x+y) (x₀+y₀) :=
  ⟨bound_add b w hx.1 hy.1,by rw [map_add,hx.2,hy.2]⟩

theorem HasTop.smul {d : ℕ} {x x₀ : M} (hx : HasTop b w d x x₀) (a : R) :
    HasTop b w d (a • x) (a • x₀) :=
  ⟨bound_smul b w hx.1 a,by rw [map_smul,hx.2]⟩

theorem HasTop.sum {J : Type*} (S : Finset J) (x y : J → M) (d : ℕ)
    (h : ∀ j ∈ S, HasTop b w d (x j) (y j)) :
    HasTop b w d (∑ j ∈ S, x j) (∑ j ∈ S, y j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasTop.zero b w d
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj,Finset.sum_insert hj]
      exact HasTop.add b w (h j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk)))

theorem homogeneous_component (d : ℕ) (x : M) : Homogeneous b w d (component b w d x) := by
  change ∀ i, b.repr (component b w d x) i ≠ 0 → w i = d
  intro i hi
  by_contra hn
  exact hi (by simp only [repr_component,if_neg hn])

theorem bound_component (d : ℕ) (x : M) : Bound b w d (component b w d x) :=
  fun i hi ↦ (homogeneous_component b w d x i hi).le

theorem homogeneous_bound {d : ℕ} {x : M} (hx : Homogeneous b w d x) : Bound b w d x :=
  fun i hi ↦ (hx i hi).le

theorem component_of_homogeneous {d : ℕ} {x : M} (hx : Homogeneous b w d x) (e : ℕ) :
    component b w e x = if e=d then x else 0 := by
  apply b.repr.injective
  ext i
  rw [repr_component]
  by_cases hxi : b.repr x i = 0
  · split_ifs <;> simp only [hxi,map_zero,Finsupp.zero_apply]
  · have hw := hx i hxi
    by_cases he : e=d
    · subst e
      simp only [hw,if_true]
    · simp only [hw,if_neg he,if_neg (Ne.symm he),map_zero,Finsupp.zero_apply]

theorem homogeneous_basis (i : I) : Homogeneous b w (w i) (b i) := by
  change ∀ j, b.repr (b i) j ≠ 0 → w j = w i
  classical
  intro j hj
  have hij : i=j := by
    by_contra hn
    exact hj (by simp only [Module.Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hn)])
  exact congrArg w hij.symm

theorem hasTop_basis (i : I) : HasTop b w (w i) (b i) (b i) := by
  exact ⟨homogeneous_bound b w (homogeneous_basis b w i),by
    rw [component_of_homogeneous b w (homogeneous_basis b w i),if_pos rfl]⟩

theorem exists_bound (x : M) : ∃ d, Bound b w d x := by
  classical
  refine ⟨(b.repr x).support.sup w,?_⟩
  intro i hi
  exact Finset.le_sup (f := w) (Finsupp.mem_support_iff.mpr hi)

theorem bound_pred_of_component_zero {d : ℕ} {x : M}
    (hx : Bound b w (d+1) x) (hz : component b w (d+1) x=0) : Bound b w d x := by
  change ∀ i, b.repr x i ≠ 0 → w i ≤ d+1 at hx
  change ∀ i, b.repr x i ≠ 0 → w i ≤ d
  intro i hi
  have hle := hx i hi
  have hne : w i ≠ d+1 := by
    intro he
    have hh := congrArg (fun y ↦ b.repr y i) hz
    apply hi
    simpa only [repr_component,if_pos he,map_zero,Finsupp.zero_apply] using hh
  omega

theorem eq_zero_of_bound_zero_component_zero {x : M}
    (hx : Bound b w 0 x) (hz : component b w 0 x=0) : x=0 := by
  apply b.repr.injective
  ext i
  by_cases hi : b.repr x i=0
  · simpa only [map_zero,Finsupp.zero_apply] using hi
  · have he := Nat.eq_zero_of_le_zero (hx i hi)
    have hh := congrArg (fun y ↦ b.repr y i) hz
    exact (hi (by simpa only [repr_component,if_pos he,map_zero,Finsupp.zero_apply] using hh)).elim

theorem component_mem_span (v : E → M) (degree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (degree e) (v e))
    (x : M) (hx : x ∈ Submodule.span R (Set.range v)) (d : ℕ) :
    component b w d x ∈ Submodule.span R (Set.range v) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨e,rfl⟩ := hx
      rw [component_of_homogeneous b w (hv e)]
      split_ifs
      · exact Submodule.subset_span ⟨e,rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using Submodule.zero_mem (Submodule.span R (Set.range v))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- Every homogeneous component of a relation has an actual bounded lift. -/
theorem relation_component_lifts (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (x : M) (hx : x ∈ Submodule.span R (Set.range g)) (d : ℕ) :
    ∃ y ∈ Submodule.span R (Set.range f), Bound b w d y ∧
      component b w d y = component b w d x := by
  classical
  have hg (j : J) : Homogeneous b w (degree j) (g j) := by
    rw [← (hf j).2]
    exact homogeneous_component b w _ _
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      by_cases hd : d=degree j
      · subst d
        refine ⟨f j,Submodule.subset_span ⟨j,rfl⟩,(hf j).1,?_⟩
        rw [(hf j).2,component_of_homogeneous b w (hg j),if_pos rfl]
      · refine ⟨0,Submodule.zero_mem _,bound_zero b w d,?_⟩
        rw [map_zero,component_of_homogeneous b w (hg j),if_neg hd]
  | zero => exact ⟨0,Submodule.zero_mem _,bound_zero b w d,rfl⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨u,hu,hub,huc⟩ := ihx
      obtain ⟨v,hv,hvb,hvc⟩ := ihy
      exact ⟨u+v,Submodule.add_mem _ hu hv,bound_add b w hub hvb,by rw [map_add,huc,hvc,map_add]⟩
  | smul a x hx ih =>
      obtain ⟨y,hy,hyb,hyc⟩ := ih
      exact ⟨a • y,Submodule.smul_mem _ a hy,bound_smul b w hyb a,by rw [map_smul,hyc,map_smul]⟩

/-- A homogeneous spanning family modulo the leading relations spans modulo
their actual filtered lifts. No regularity or associated-graded equality is
assumed. The argument is finite descending reduction in the given basis. -/
theorem spanning_lifts (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤) :
    Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range f)=⊤ := by
  let C := Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range f)
  have step (d : ℕ) (x : M) (hx : Bound b w d x) :
      ∃ z ∈ C, Bound b w d (x-z) ∧ component b w d (x-z)=0 := by
    have hm : x ∈ Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g) := by
      rw [hspan]
      trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨y,hy,hyb,hyc⟩ := relation_component_lifts b w f g degree hf j hj d
    refine ⟨component b w d u+y,Submodule.add_mem C
      ((show Submodule.span R (Set.range v) ≤ C from le_sup_left)
        (component_mem_span b w v vdegree hv u hu d))
      ((show Submodule.span R (Set.range f) ≤ C from le_sup_right) hy),
      bound_sub b w hx (bound_add b w (bound_component b w d u) hyb),?_⟩
    have hid : component b w d (component b w d u)=component b w d u := by
      rw [component_of_homogeneous b w (homogeneous_component b w d u),if_pos rfl]
    rw [map_sub,map_add,hid,hyc,← huj,map_add,sub_self]
  have hmem : ∀ d x, Bound b w d x → x ∈ C := by
    intro d
    induction d with
    | zero =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step 0 x hx
        have he := eq_zero_of_bound_zero_component_zero b w hb hc
        rw [sub_eq_zero.mp he]
        exact hz
    | succ d ih =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step (d+1) x hx
        have hh := ih (x-z) (bound_pred_of_component_zero b w hb hc)
        simpa only [sub_add_cancel] using Submodule.add_mem C hh hz
  apply top_unique
  intro x hx
  obtain ⟨d,hd⟩ := exists_bound b w x
  exact hmem d x hd

end PaperVerification.Fermion.BasisFiltered
end
end
end BatchFile_2

section BatchFile_3
/- Literal source: PaperVerification/FermionFilteredInitial.lean -/


/-!
# Initial relations from actual bounded reduction and independence

The initial submodule is defined from the leading components of the actual
relation submodule.  Bounded reduction proves that it equals the homogeneous
relations once the same representatives are independent in the deformed
quotient.  No equality of dimensions or initial ideals is assumed.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R M I J E Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q] (b : Module.Basis I R M) (w : I → ℕ)

theorem bound_mono {d e : ℕ} {x : M} (hde : d ≤ e) (hx : Bound b w d x) :
    Bound b w e x := fun i hi ↦ (hx i hi).trans hde

theorem component_eq_zero_of_bound_lt {d e : ℕ} {x : M}
    (hde : d < e) (hx : Bound b w d x) : component b w e x=0 := by
  apply b.repr.injective
  ext i
  rw [repr_component,map_zero,Finsupp.zero_apply]
  split_ifs with hi
  · by_contra hxi
    have hw := hx i hxi
    omega
  · rfl

def initialSubmodule (N : Submodule R M) : Submodule R M :=
  Submodule.span R {y | ∃ x ∈ N, ∃ d, Bound b w d x ∧ component b w d x=y}

/-- Reduction preserves the degree bound and explicitly tracks the leading
part of the actual relation used. -/
theorem bounded_representative
    (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤)
    (d : ℕ) (x : M) (hx : Bound b w d x) :
    ∃ z ∈ Submodule.span R (Set.range v), Bound b w d z ∧
      x-z ∈ Submodule.span R (Set.range f) ∧
      component b w d (x-z) ∈ Submodule.span R (Set.range g) := by
  have hg (j : J) : Homogeneous b w (degree j) (g j) := by
    rw [← (hf j).2]
    exact homogeneous_component b w _ _
  have step (e : ℕ) (y : M) (hy : Bound b w e y) :
      ∃ u ∈ Submodule.span R (Set.range v), ∃ a ∈ Submodule.span R (Set.range f),
        Bound b w e u ∧ Bound b w e a ∧
        component b w e (y-u-a)=0 ∧
        component b w e a ∈ Submodule.span R (Set.range g) := by
    have hm : y ∈ Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g) := by
      rw [hspan]
      trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a,ha,hab,hac⟩ := relation_component_lifts b w f g degree hf j hj e
    refine ⟨component b w e u,component_mem_span b w v vdegree hv u hu e,a,ha,
      bound_component b w e u,hab,?_,?_⟩
    · have huu : component b w e (component b w e u)=component b w e u := by
        rw [component_of_homogeneous b w (homogeneous_component b w e u),if_pos rfl]
      rw [map_sub,map_sub,huu,hac,← huj,map_add]
      abel
    · rw [hac]
      exact component_mem_span b w g degree hg j hj e
  induction d generalizing x with
  | zero =>
      obtain ⟨u,hu,a,ha,hub,hab,hc,hg⟩ := step 0 x hx
      have hz := eq_zero_of_bound_zero_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      have he : x-u=a := sub_eq_zero.mp hz
      exact ⟨u,hu,hub,by rw [he]; exact ha,by rw [he]; exact hg⟩
  | succ d ih =>
      obtain ⟨u,hu,a,ha,hub,hab,hc,hg⟩ := step (d+1) x hx
      have hb : Bound b w d (x-u-a) :=
        bound_pred_of_component_zero b w
          (bound_sub b w (bound_sub b w hx hub) hab) hc
      obtain ⟨z,hz,hzb,hr,ht⟩ := ih (x-u-a) hb
      have he : x-(u+z)=a+((x-u-a)-z) := by abel
      refine ⟨u+z,Submodule.add_mem _ hu hz,
        bound_add b w hub (bound_mono b w (Nat.le_succ d) hzb),?_,?_⟩
      · rw [he]
        exact Submodule.add_mem _ ha hr
      · rw [he,map_add,component_eq_zero_of_bound_lt b w (Nat.lt_succ_self d)
          (bound_sub b w hb hzb),add_zero]
        exact hg

/-- The actual leading submodule equals the homogeneous relation submodule.
The proof uses the independent representatives, not a dimension assertion. -/
theorem initialSubmodule_eq_of_basis [Fintype E]
    (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤)
    (q : M →ₗ[R] Q) (hker : q.ker=Submodule.span R (Set.range f))
    (hli : LinearIndependent R (fun e ↦ q (v e))) :
    initialSubmodule b w q.ker=Submodule.span R (Set.range g) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨x,hx,d,hb,rfl⟩
    obtain ⟨z,hz,hzb,hr,ht⟩ := bounded_representative b w f g degree hf v vdegree hv hspan d x hb
    have hqz : q z=0 := by
      have hqr : q (x-z)=0 := by
        apply LinearMap.mem_ker.mp
        rwa [hker]
      rw [map_sub,LinearMap.mem_ker.mp hx,zero_sub,neg_eq_zero] at hqr
      exact hqr
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hz
    have hzero : ∑ e, c e • q (v e)=0 := by
      simpa only [map_sum,map_smul] using (congrArg q hc).trans hqz
    have hcoef := Fintype.linearIndependent_iff.mp hli c hzero
    have hz0 : z=0 := by
      rw [← hc]
      simp only [hcoef,zero_smul,Finset.sum_const_zero]
    change component b w d x ∈ Submodule.span R (Set.range g)
    simpa only [hz0,sub_zero] using ht
  · apply Submodule.span_le.mpr
    rintro y ⟨j,rfl⟩
    apply Submodule.subset_span
    refine ⟨f j,?_,degree j,(hf j).1,(hf j).2⟩
    rw [hker]
    exact Submodule.subset_span ⟨j,rfl⟩

end PaperVerification.Fermion.BasisFiltered
end
end
end BatchFile_3
