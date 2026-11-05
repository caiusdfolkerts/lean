module
public import consolidated.homothety_fiber_comparison
public import consolidated.homothety_shared_class_neighbors

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetySharedCentralImpossible.lean -/




@[expose] public section

/-!
# The shared-vertex obstruction for a new central homothety

A shared central vertex supplies the crossing neighbor between its two
owner classes. Matchings into two further minimum classes identify the
same fiber rows. The two owner vertices then have three common actual
neighbors. Rigidity of their actual K₂,₃ forces the two distinct original
homotheties to coincide.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

theorem shared_central_impossible_of_unique_ownership
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y∈P.vertices,∃ j,f y=a j•y+b j)
    (hmin : ∀ j,(noncentralClass P f a b j).card=
      d+1-finrank ℝ (parameterDirectionSpan a b))
    (hr : 2 ≤ d+1-finrank ℝ (parameterDirectionSpan a b))
    (hm : 4 ≤ Fintype.card I)
    (hunique : ∀ j,∀ z∈centralVertices P a b,∀ w∈centralVertices P a b,
      f z=a j•z+b j → f w=a j•w+b j → z=w)
    {z : E d} (hz : z∈centralVertices P a b)
    {i h : I} (hih : i≠h) (hzi : f z=a i•z+b i) (hzh : f z=a h•z+b h) : False := by
  let J := (Finset.univ : Finset I) \ {i,h}
  have hJ : 2 ≤ J.card := by
    dsimp [J]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_pair hih]
    omega
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp (by omega : 1<J.card)
  have hj' : j≠i ∧ j≠h := by simpa [J] using hj
  have hk' : k≠i ∧ k≠h := by simpa [J] using hk
  have hsharei : ∀ w∈centralVertices P a b,f w=a i•w+b i →
      ∃ l,l≠i ∧ f w=a l•w+b l := by
    intro w hw hwi
    have hwz := hunique i w hw z hz hwi hzi
    exact ⟨h,hih.symm,by simpa only [hwz] using hzh⟩
  have hshareh : ∀ w∈centralVertices P a b,f w=a h•w+b h →
      ∃ l,l≠h ∧ f w=a l•w+b l := by
    intro w hw hwh
    have hwz := hunique h w hw z hz hwh hzh
    exact ⟨i,hih,by simpa only [hwz] using hzi⟩
  have hneveri (l : I) (hli : l≠i) (hlh : l≠h) :
      ∀ w∈centralVertices P a b,f w=a i•w+b i → f w≠a l•w+b l := by
    intro w hw hwi hwl
    have hwz := hunique i w hw z hz hwi hzi
    have hzl : f z=a l•z+b l := hwz ▸ hwl
    exact (third_owner_eq f a b hind hih hzi hzh hzl).elim hli hlh
  have hneverh (l : I) (hli : l≠i) (hlh : l≠h) :
      ∀ w∈centralVertices P a b,f w=a h•w+b h → f w≠a l•w+b l := by
    intro w hw hwh hwl
    have hwz := hunique h w hw z hz hwh hzh
    have hzl : f z=a l•z+b l := hwz ▸ hwl
    exact (third_owner_eq f a b hind hih hzi hzh hzl).elim hli hlh
  have hsizei : 2 ≤ (noncentralClass P f a b i).card := by rw [hmin]; exact hr
  have hsizeh : 2 ≤ (noncentralClass P f a b h).card := by rw [hmin]; exact hr
  obtain ⟨Mij,hMij,eij⟩ := exists_sharedCentral_crossing_matching
    P hP f hf a b hind hcover hsharei hj'.1 (hneveri j hj'.1 hj'.2) (hmin i) hsizei
  obtain ⟨Mhj,hMhj,ehj⟩ := exists_sharedCentral_crossing_matching
    P hP f hf a b hind hcover hshareh hj'.2 (hneverh j hj'.1 hj'.2) (hmin h) hsizeh
  obtain ⟨Mik,hMik,eik⟩ := exists_sharedCentral_crossing_matching
    P hP f hf a b hind hcover hsharei hk'.1 (hneveri k hk'.1 hk'.2) (hmin i) hsizei
  obtain ⟨Mhk,hMhk,ehk⟩ := exists_sharedCentral_crossing_matching
    P hP f hf a b hind hcover hshareh hk'.2 (hneverh k hk'.1 hk'.2) (hmin h) hsizeh
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega :
    0<(noncentralClass P f a b i).card)
  let u : noncentralClass P f a b i := ⟨x,hx⟩
  have hsur : Function.Surjective Mhj :=
    ((Fintype.bijective_iff_injective_and_card Mhj).mpr ⟨hMhj,by
      rw [Fintype.card_coe,Fintype.card_coe,hmin h,hmin j]⟩).2
  obtain ⟨v,hv⟩ := hsur (Mij u)
  have hvj : (Mhj v).val=(Mij u).val := congrArg Subtype.val hv
  have huf := crossing_fibers_equal P f hf a b hind.injective
    u.property (Mij u).property hj'.1 (eij u)
  have hvf := crossing_fibers_equal P f hf a b hind.injective
    v.property (Mhj v).property hj'.2 (ehj v)
  rw [hvj] at hvf
  have huvF : parameterFiber P a b u.val=parameterFiber P a b v.val := huf.trans hvf.symm
  have hukF := crossing_target_mem_fiber P f hf a b hind.injective
    u.property (Finset.mem_filter.mp (Mik u).property).1 hk'.1 (eik u)
  have hvkF := crossing_target_mem_fiber P f hf a b hind.injective
    v.property (Finset.mem_filter.mp (Mhk v).property).1 hk'.2 (ehk v)
  rw [←huvF] at hvkF
  obtain ⟨Bk,hBk⟩ := exists_minimumClass_basis P hP f hf a b hind.injective
    hcover k (hmin k) (by omega)
  have hkv : (Mhk v).val=(Mik u).val := minimumClass_same_fiber_unique
    P f a b k Bk hBk (Mhk v).property (Mik u).property hvkF hukF
  have huP := (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
  have hvP := (Finset.mem_filter.mp (Finset.mem_filter.mp v.property).1).1
  have hzP := (Finset.mem_filter.mp hz).1
  have hjP := (Finset.mem_filter.mp (Finset.mem_filter.mp (Mij u).property).1).1
  have hkP := (Finset.mem_filter.mp (Finset.mem_filter.mp (Mik u).property).1).1
  have e_jv : GeneralVertexStep P v.val (Mij u).val := hvj ▸ ehj v
  have e_kv : GeneralVertexStep P v.val (Mik u).val := hkv ▸ ehk v
  have euz : GeneralVertexStep P u.val z := by
    obtain ⟨y,⟨hy,huy⟩,_⟩ := sharedCentral_minimumClass_other_neighbor
      P hP f hf a b hind hcover hsharei (hmin i) hsizei u.property h hih.symm
    have hyz := neighbor_toward_shared_class_is_center P f hf a b hind.injective
      hih.symm hz hzi hzh u.property hy huy
    exact hyz ▸ huy
  have evz : GeneralVertexStep P v.val z := by
    obtain ⟨y,⟨hy,hvy⟩,_⟩ := sharedCentral_minimumClass_other_neighbor
      P hP f hf a b hind hcover hshareh (hmin h) hsizeh v.property i hih
    have hyz := neighbor_toward_shared_class_is_center P f hf a b hind.injective
      hih hz hzh hzi v.property hy hvy
    exact hyz ▸ hvy
  have huv : u.val≠v.val := by
    intro he
    exact noncentral_not_other_parameter P f a b hind.injective u.property hih.symm
      (he ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp v.property).1).2)
  have hzj : z≠(Mij u).val := by
    intro he
    exact (Finset.mem_filter.mp (Mij u).property).2
      (he ▸ (Finset.mem_filter.mp hz).2)
  have hzk : z≠(Mik u).val := by
    intro he
    exact (Finset.mem_filter.mp (Mik u).property).2
      (he ▸ (Finset.mem_filter.mp hz).2)
  have hjkpoints : (Mij u).val≠(Mik u).val := by
    intro he
    exact noncentral_not_other_parameter P f a b hind.injective (Mij u).property hjk.symm
      (he ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp (Mik u).property).1).2)
  let uu : P.vertices := ⟨u.val,huP⟩
  let vv : P.vertices := ⟨v.val,hvP⟩
  let pts : Fin 3 → P.vertices := ![⟨z,hzP⟩,⟨(Mij u).val,hjP⟩,⟨(Mik u).val,hkP⟩]
  have hpts : Function.Injective pts := by
    intro q r he
    have hv := congrArg Subtype.val he
    fin_cases q <;> fin_cases r
    all_goals simp only [pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hv
    all_goals first | rfl | exact (hzj hv).elim | exact (hzj hv.symm).elim |
      exact (hzk hv).elim | exact (hzk hv.symm).elim |
      exact (hjkpoints hv).elim | exact (hjkpoints hv.symm).elim
  have eu (q : Fin 3) : GeneralVertexStep P uu.val (pts q).val := by
    fin_cases q
    · exact euz
    · exact eij u
    · exact eik u
  have ev (q : Fin 3) : GeneralVertexStep P vv.val (pts q).val := by
    fin_cases q
    · exact evz
    · exact e_jv
    · exact e_kv
  obtain ⟨α,c,H⟩ := Papers.ActualRigidity.k23_homothety P uu vv pts
    (fun he => huv (congrArg Subtype.val he)) hpts eu ev f
    (fun q => hf uu.val uu.property (pts q).val (pts q).property (eu q))
    (fun q => hf vv.val vv.property (pts q).val (pts q).property (ev q))
  have Hu : f u.val=α•u.val+c := H uu.val (Set.mem_insert _ _)
  have Hv : f v.val=α•v.val+c := H vv.val (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have Hz : f z=α•z+c := H z (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ ⟨0,rfl⟩))
  have hiParam : (α,c)=parameterVector a b i := homothety_parameters_eq_of_two_points
    euz.2.1 (Hu.symm.trans (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).2)
    (Hz.symm.trans hzi)
  have hhParam : (α,c)=parameterVector a b h := homothety_parameters_eq_of_two_points
    evz.2.1 (Hv.symm.trans (Finset.mem_filter.mp (Finset.mem_filter.mp v.property).1).2)
    (Hz.symm.trans hzh)
  exact hih (hind.injective (hiParam.symm.trans hhParam))

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

