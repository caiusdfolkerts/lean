module
prelude
public import TenGraphEdges

@[expose] public section
namespace Papers.RationalityTen.FastTenGraphEdges
open GrowthRenaming
set_option maxHeartbeats 0

def first (edge : Fin 45) : Fin 10 :=
  Fin.ofNat 10 (Nat.land (810920607990572664732450050533245137802995380707655680 >>> (4 * edge.val)) 15)
def second (edge : Fin 45) : Fin 10 :=
  Fin.ofNat 10 (Nat.land (919121535505433609095521379442923578748084253412901665 >>> (4 * edge.val)) 15)
def encode (a b : Fin 10) : Fin 45 :=
  if a = b then 0 else
    let lo := min a.val b.val
    let hi := max a.val b.val
    Fin.ofNat 45 (lo * (19 - lo) / 2 + (hi - lo - 1))

theorem first_eq (edge : Fin 45) : first edge = TenGraphEdges.first edge := by
  have h : (List.finRange 45).all (fun e => decide (first e = TenGraphEdges.first e)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h edge (List.mem_finRange edge))

theorem second_eq (edge : Fin 45) : second edge = TenGraphEdges.second edge := by
  have h : (List.finRange 45).all (fun e => decide (second e = TenGraphEdges.second e)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h edge (List.mem_finRange edge))

theorem encode_eq (a b : Fin 10) : encode a b = TenGraphEdges.encode a b := by
  have h : (List.finRange 10).all (fun a => (List.finRange 10).all
      (fun b => decide (encode a b = TenGraphEdges.encode a b))) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp h a (List.mem_finRange a)) b (List.mem_finRange b))

def edgeMap (code : Nat) (edge : Fin 45) : Fin 45 :=
  encode (TenGraphEdges.vertexMap code (first edge))
    (TenGraphEdges.vertexMap code (second edge))

theorem edgeMap_eq (code : Nat) (p : Bijection (Fin 10))
    (h : p.forward = TenGraphEdges.vertexMap code) (edge : Fin 45) :
    edgeMap code edge = TenGraphEdges.edgeMap p edge := by
  simp only [edgeMap, encode_eq, first_eq, second_eq, TenGraphEdges.edgeMap, h]

#print axioms edgeMap_eq
end Papers.RationalityTen.FastTenGraphEdges
