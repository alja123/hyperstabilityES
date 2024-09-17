

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph
open Classical
#check Fintype.exists_le_sum_fiber_of_nsmul_le_sum

#check SimpleGraph.sum_degrees_eq_twice_card_edges

#check SimpleGraph.degree

#check SimpleGraph.minDegree
#check SimpleGraph.IsTree

#check injective_iff_map_eq_one
set_option linter.unusedVariables false

open Finset
--open scoped BigOperators

namespace SimpleGraph

universe u

variable {VG : Type u} (G : SimpleGraph VG)
variable {VT : Type u} (T : SimpleGraph VT)



section TreeEmbed

variable [Fintype VG] [DecidableRel G.Adj]
variable [Fintype VT] [DecidableRel T.Adj]
variable (k: ℕ )

variable [Fintype (Sym2 VG)]
variable [Fintype (Sym2 VT)]


--def  jj: VG →  VG:= by exact fun a => a



theorem bla (v a b :VG): ∃ (f: G →g  G), f v=v := by
have h:G↪g G := by exact Embedding.refl
have h4: ∃ (f: VG →  VG), ∀ (w:VG), f w=w := by exact Exists.intro (fun a => a) (congrFun rfl)

rcases h4 with ⟨ j, hj⟩
have h5: j v = v:= by exact hj v

have h6: G.Adj a b → G.Adj (j a) (j b) := by
  intro hx
  have h7: j a = a:= by exact hj a
  rw[h7]
  have h8: j b = b:= by exact hj b
  rw[h8]
  exact hx
have h9: ∀ {c d: VG}, G.Adj c d → G.Adj (j c) (j d) := by
  intro c d
  intro hx
  have h7: j c = c:= by exact hj c
  rw[h7]
  have h8: j d = d:= by exact hj d
  rw[h8]
  exact hx

use RelHom.mk j @h9
exact h5


theorem hom_from_graph_no_edges   (vT :VT)(vG :VG):(∀ {c d : VT}, ¬ T.Adj c d)→ ∃ (f: T →g  G), f vT=vG := by
have h4: ∃ (g: VT →  VG),  g vT=vG := by exact exists_apply_eq vT vG
rcases h4 with ⟨j, hj⟩
intro h6
have h5: ∀ {c d: VT}, T.Adj c d → G.Adj (j c) (j d):= by exact fun {c d} a => (h6 a).elim

-- let jj:  T→g G:= RelHom.mk j @h5
-- have higj: jj vT= vG:= by exact hj

use RelHom.mk j @h5
exact hj




theorem nonsingleton  (c d: VT): (c≠d)→ Fintype.card VT≠ 1:= by
intro h
have h2: Nonempty VT := by exact Nonempty.intro c
inhabit VT
--have h1: Fintype.card VT≠ 0:= by exact Fintype.card_ne_zero

#check Finset.card_singleton.{u} c
have hdisj : Disjoint ({c}: Finset VT) ({d}: Finset VT):= by exact disjoint_singleton.mpr h



--have hd1: Finset.card ({d} : Finset VT)  = 1 := by  exact rfl
--have hd2: Finset.card ({c}: Finset VT )  = 1 := by  exact rfl
--have hd3: Finset.card (disjUnion ({c}:Finset VT) ({d}: Finset VT) hdisj )  = 2 := by  exact rfl
have Hin: Fintype.card VT≥ Finset.card (disjUnion ({c}:Finset VT) ({d}: Finset VT) hdisj ) :=
  by exact  card_le_univ (({c}: Finset VT).disjUnion ({d}: Finset VT) hdisj)
exact Ne.symm (Nat.ne_of_lt Hin)


theorem sizeone_implies_all_elements_equal (x y: VT): Fintype.card VT= 1 → (x=y):= by
contrapose
exact fun a => nonsingleton x y a


theorem one_vertex_implies_no_edges : (Fintype.card VT=1)→ (∀ {c d : VT}, ¬ T.Adj c d) := by
intro h1
--have h3: Fintype.card VT≥ 1:= by exact Nat.le_of_eq (id h1.symm)
--have h2: Nonempty VT := by exact Fintype.card_pos_iff.mp h3
--inhabit VT
intro c d
have h7:  Fintype.card VT= 1 → (c=d):= by exact sizeone_implies_all_elements_equal c d

have h2: c=d:= by exact h7 h1
have h4: ¬T.Adj c c:= by exact SimpleGraph.irrefl T
exact Eq.mpr_not (congrArg (T.Adj c) (id h2.symm)) h4


theorem hom_from_graph_with_one_vertex   (vT :VT)(vG :VG):(Fintype.card VT=1)→ ∃ (f: T →g  G), f vT=vG := by
intro h2
have h3: (∀ {c d : VT}, ¬ T.Adj c d):= by exact fun {c d} => one_vertex_implies_no_edges T h2
exact hom_from_graph_no_edges G T vT vG h3




theorem inj_hom_from_graph_with_one_vertex   (vT :VT)(vG :VG):
(Fintype.card VT=1)→ ∃ (f: T →g  G), (f vT=vG)∧ (Function.Injective f.toFun) := by
intro h2
--have h3: (∀ {c d : VT}, ¬ T.Adj c d):= by exact fun {c d} => one_vertex_implies_no_edges T h2
have  h4: ∃ (f: T →g  G), f vT=vG := by exact hom_from_graph_with_one_vertex G T vT vG h2
rcases h4 with ⟨ff, hh⟩

have hi2: Function.Injective ff.toFun:= by
    intro a b  c
    have d: a=b:= by apply sizeone_implies_all_elements_equal a b h2
    exact d
use ff
variable (a:ℕ)


 #check not_forall_not
 #check not_exists_not



theorem tree_has_a_low_deg_vertex (hTree : T.IsTree):∃x: VT, T.degree x≤ 1:= by
by_contra h'
have hsum: (Finset.univ.sum fun (v : VT) => T.degree v) = 2 * T.edgeFinset.card:=
    by exact sum_degrees_eq_twice_card_edges T
have hedges: Finset.card T.edgeFinset + 1 = Fintype.card VT := by exact IsTree.card_edgeFinset hTree
have hsum2: (Finset.univ.sum fun (v : VT) => T.degree v) = 2* (Fintype.card VT -1):= by exact
    (Mathlib.Tactic.Ring.mul_congr rfl (congrFun (congrArg HSub.hSub (id hedges.symm)) 1)
      (id hsum.symm)).symm
have h2p:¬(∃x: VT, T.degree x≤  1)↔ ∀ x: VT,  T.degree x> 1:= by simp
have hpos:   ∀ x: VT,  T.degree x> 1:= by
       rw [h2p.symm]
       exact h'

--have hpos':∀ x: VT,  T.degree x≥  2:= by exact fun x => hpos x
have hnewsum: (Finset.univ.sum fun (v : VT) => T.degree v) ≥ (Finset.univ.sum fun (v : VT) => 2) := by
  exact  GCongr.sum_le_sum fun i a => hpos i
have  hsum4: (Finset.univ.sum fun (v : VT) => 1) = Fintype.card VT:= by exact
  Fintype.card_eq_sum_ones.symm
have  hsum3: (Finset.univ.sum fun (v : VT) => 2) = 2*(Finset.univ.sum fun (v : VT) => 1):= by exact
  (mul_sum univ (fun i => 1) 2).symm
--have hnewsum2: (Finset.univ.sum fun (v : VT) => T.degree v)≥ 2*(Fintype.card VT):= by calc
--  ∑ v : VT, T.degree v ≥ (Finset.univ.sum fun (v : VT) => 2) := by exact hnewsum
--  _=2*(Finset.univ.sum fun (v : VT) => 1):= by exact hsum3
--  _=2*(Fintype.card VT):= by exact congrArg (HMul.hMul 2) hsum4
--have heq: 2* (Fintype.card VT -1)≥ 2*(Fintype.card VT):= by exact le_of_le_of_eq hnewsum2 hsum2
have heq2:0 ≥   2:= by linarith
--have heq3:2> 0:= by exact Nat.zero_lt_two
exact Nat.not_succ_le_zero 1 heq2


theorem connected_min_degree_1 (hConnected : T.Preconnected)(hSize : Fintype.card VT≥ 2)(x: VT): T.degree x≠ 0:= by
have h1: ∃ (y:VT), y≠ x:= by exact Fintype.exists_ne_of_one_lt_card hSize x
rcases h1 with ⟨y, hy ⟩
--have hReach: T.Reachable x y := by exact hConnected x y
have hWalk:Nonempty (T.Walk x y):= by exact hConnected x y
--classical
--inhabit T.Walk x y
have hp:∃(w: T.Walk x y), (1=1) := by exact (exists_const (T.Walk x y)).mpr rfl
rcases hp with ⟨w, hw ⟩
have hlength: w.length≠ 0:= by
  by_contra a
  #check SimpleGraph.Walk.eq_of_length_eq_zero
  have heq: x=y := by apply SimpleGraph.Walk.eq_of_length_eq_zero a
  exact hy (id heq.symm)
have hlength2: w.length≥ 1:= by exact Nat.one_le_iff_ne_zero.mpr hlength
have hv0: x=w.getVert 0 := by exact (Walk.getVert_zero w).symm
have hadj: T.Adj (w.getVert 0) (w.getVert 1):= by exact Walk.adj_getVert_succ w hlength2
have hadj2: (T.Adj (w.getVert 0) (w.getVert 1))↔ (T.Adj (x) (w.getVert 1)):= by
  exact Eq.to_iff (congrFun (congrArg T.Adj (id hv0.symm)) (w.getVert 1))
have hadj3:(T.Adj (w.getVert 0) (w.getVert 1))→(T.Adj (x) (w.getVert 1)):= hadj2.1
--have hadj4: T.Adj (x) (w.getVert 1):= by exact hadj3 hadj
have hne1: (w.getVert 1)∈ T.neighborFinset x := by
  exact (mem_neighborFinset T x (w.getVert 1)).mpr (hadj3 hadj)
--have hne2: Nonempty (T.neighborFinset x ):= by use (w.getVert 1)
have hne3: (T.neighborFinset x ).card ≠ 0:= by exact card_ne_zero_of_mem hne1

--let GG:T.Subgraph:= by exact SimpleGraph.singletonSubgraph T x
--have hTin: T≤ T := by exact fun ⦃v w⦄ a => a
--let TSub: T.Subgraph:= by exact SimpleGraph.toSubgraph T hTin
--let TSet: Finset VT:= by  (VT.elems) \   ({x}: Finset VT)
-- have hem: TSet=∅:=by exact Finset.sdiff_self {x}
--let GDel:T.Subgraph:= by exact SimpleGraph.Subgraph.deleteVerts TSub  ({x}: Set VT)
--let TDel:SimpleGraph ↑GDel.verts:= by exact induce GDel.verts T
--have  h:=   Finset.fintypeCoeSort ({x}: Finset VT)
--have h22: Fintype h:= by
exact hne3

--theorem path_vertices_correspond_get? (x y:VT)(C: T.Walk x y)(i :ℕ )(hi:i<  C.support.length):C.getVert i=C.support.get ⟨ i, hi⟩ := by

theorem path_vertices_distinct (x y:VT)(C: T.Walk x y)(hPath:C.IsPath)(i j:ℕ )(hi:i≤  C.length)(hij:i≠ j):C.support.get? i≠ C.support.get? j:= by
by_contra h
have h2: C.support.Nodup:= by exact hPath.support_nodup
have h3: C.support.length = C.length+1 := by exact Walk.length_support C
have hi':i<  C.support.length:= by calc
  i≤ C.length:= by exact hi
  _=C.support.length-1:= by exact Nat.eq_sub_of_add_eq (id h3.symm)
  _<C.support.length:= by simp
have h1:i=j:= by exact List.get?_inj hi' h2 h
exact hij h1


--theorem path_min_deg_2 (x y z:VT)(C: T.Walk x z)(hCycle:C.IsPath)(hy: y∈ C.support)(hyx: y≠ x)(hyz: y≠ z):T.degree y≥ 2:= by
--have hsplit: ∃ (q : T.Walk x y) (r : T.Walk y z), C = q.append r:= by
--  exact  Walk.mem_support_iff_exists_append.mp hy
--rcases hsplit with  ⟨q, r, hqr⟩


theorem subgraph_of_acyclic (H: SimpleGraph VG)(hSubs:H≤ G)(hAcyclic: G.IsAcyclic):H.IsAcyclic:= by
by_contra h
have hAcyc: ¬ (∀  (v : VG) (c : H.Walk v v), ¬ (c.IsCycle)):=  by exact h
have heq: ¬ (∀  (v : VG) (c : H.Walk v v), ¬ (c.IsCycle))↔ ∃   (v : VG) (c : H.Walk v v),  (c.IsCycle):= by simp
have hex: ∃   (v : VG) (c : H.Walk v v),  (c.IsCycle):= by apply heq.1 hAcyc
rcases hex with ⟨v, c, hc ⟩
let cG:G.Walk v v := by exact SimpleGraph.Walk.mapLe hSubs c
have hcyc: cG.IsCycle:= by exact Walk.IsCycle.mapLe hSubs hc
exact hAcyclic cG hcyc

theorem induced_subgraph_of_acyclic (S: Set VG)(H: SimpleGraph ↑S)(hH: H=induce S G)(hAcyclic: G.IsAcyclic):H.IsAcyclic:= by
by_contra h
have hAcyc: ¬ (∀  (v : ↑S) (c : H.Walk v v), ¬ (c.IsCycle)):=  by exact h
have heq: ¬ (∀  (v : ↑S) (c : H.Walk v v), ¬ (c.IsCycle))↔ ∃   (v : ↑S) (c : H.Walk v v),  (c.IsCycle):= by simp
have hex: ∃   (v : ↑S) (c : H.Walk v v),  (c.IsCycle):= by apply heq.1 hAcyc
rcases hex with ⟨v, c, hc ⟩
--let f:↑S→ VG:= by exact fun a=> a
have f:H↪g G:= by rw[hH];  exact Embedding.induce S
let g:H→gG:= by exact f.toHom
have hfinj:Function.Injective f:= by exact RelEmbedding.injective f

have fInj: Function.Injective (Walk.map g : H.Walk v v → G.Walk (g v) (g v)):= by
  apply SimpleGraph.Walk.map_injective_of_injective
  exact hfinj
let cG:G.Walk (g v) (g v) := Walk.map g c
have hcGCy:cG.IsCycle:= by
  refine Walk.map_isCycle_of_injective ?hinj hc
exact hAcyclic cG hcGCy

--have hcyc: cG.IsCycle:= by exact Walk.IsCycle.mapLe hSubs hc



theorem at_most_one_neighbour(hOrder: Fintype.card VT≥ 2)(lT:VT)(hDegree: T.degree lT≤ 1):∃ (lT':VT), (lT'≠ lT)∧ (∀ (y: VT), (T.Adj lT y)→(y=lT')):= by
by_cases hzero:T.degree lT=0

let VTT: Finset VT:= Finset.univ
let VTS: Finset VT:= ({lT}: Finset VT)
let VT': Finset VT:= VTT\ VTS
have hVT': Finset.card VT'>0:= by
  have h1: VTS⊆ VTT := by exact subset_univ VTS
  calc
    Finset.card VT' = Finset.card VTT-Finset.card VTS:= by exact card_sdiff h1
    _= Finset.card VTT-1:= by exact rfl
    _= Fintype.card VT-1:= by exact rfl
    _≥ 2-1:= by exact Nat.sub_le_sub_right hOrder 1
    _=1:= by exact rfl


have hex: ∃ (x:VT), x∈ VT' := by exact Multiset.card_pos_iff_exists_mem.mp hVT'
rcases hex with ⟨x, hx ⟩
have hneq: x≠lT:= by
  have hin: lT∈ VTS:=by exact mem_singleton.mpr rfl
  have hin2: ¬ lT∈ VT':=by exact not_mem_sdiff_of_mem_right hin
  exact ne_of_mem_of_not_mem hx hin2

have h1:(∀ (y: VT), (T.Adj lT y)→(y=x)):= by
  intro y hAdj
  have h2:y∈ T.neighborFinset lT:= by exact (mem_neighborFinset T lT y).mpr hAdj
  have h3:(T.neighborFinset lT)≠ ∅ := by exact ne_empty_of_mem h2
  have h4: T.degree lT≠ 0:= by calc
    T.degree lT=Finset.card (T.neighborFinset lT):= by exact rfl
    _≠ 0:= by exact card_ne_zero_of_mem h2
  exfalso
  exact h4 hzero
use x, hneq, h1


have hDeg1: T.degree lT = 1:=by
  have h1: T.degree lT>0:= by exact Nat.zero_lt_of_ne_zero hzero
  exact (Nat.le_antisymm h1 hDegree).symm

have hNonempty2: Finset.card (T.neighborFinset lT)>0:= by exact Nat.zero_lt_of_ne_zero hzero
have hex: ∃ (x:VT), x∈  (T.neighborFinset lT):= by
  exact Multiset.card_pos_iff_exists_mem.mp hNonempty2
rcases hex with ⟨x, hx ⟩
have hAdj: T.Adj lT x := by exact (mem_neighborFinset T lT x).mp hx
have hneq: x≠ lT:= by exact Adj.ne' hAdj

have hUnique:∀ (y : VT), T.Adj lT y → y = x:= by
  intro y hy
  by_contra neq
  have hin: y∈ (T.neighborFinset lT):= by exact (mem_neighborFinset T lT y).mpr hy
  have hsubset2:{y}⊆ T.neighborFinset lT:= by exact singleton_subset_iff.mpr hin
  have hsubset3:{x,y}⊆ T.neighborFinset lT:= by exact insert_subset hx hsubset2
  have hxysize:Finset.card {x, y}=2:= by exact card_pair fun a => neq (id a.symm)
  have hsize2: Finset.card (T.neighborFinset lT)≥ 2:= by calc
    Finset.card (T.neighborFinset lT)≥Finset.card {x, y}:= by exact card_le_card hsubset3
    _=2:= by exact hxysize
  have hsize3: Finset.card (T.neighborFinset lT)≠ 1:=by exact Ne.symm (Nat.ne_of_lt hsize2)
  exact hsize3 hDeg1

use x



theorem acyclic_has_a_low_deg_vertex (hAcyclic : T.IsAcyclic)(x:VT):∃x: VT, T.degree x≤ 1:= by
let C:Set VT:={y| T.Reachable x y }
have Creachable:(a:VT)→ (b: VT) → (a∈ C)→ (b∈ C)→ T.Reachable a b := by
  intro a b ha hb
  have hxa: T.Reachable x a:= by exact ha
  have hxb: T.Reachable x b:= by exact hb
  exact Reachable.trans (id (Reachable.symm hxa)) hb
have htrans: (a:VT)→ (b: VT) → (a∈ C)→ (T.Adj a b) → (b∈ C):= by
  intro a b ha hab
  have hxa: T.Reachable x a:= by exact ha
  have hab: T.Reachable a b:= by exact Adj.reachable hab
  have hxb: T.Reachable x b:= by exact Reachable.trans ha hab
  exact hxb
have hxinC:x∈ C:= by
  have hxx: T.Reachable x x:= by exact Reachable.refl x
  exact Creachable x x (Creachable x x hxx hxx) hxx
let typeC:={w// w∈ C}
let Cgraph: SimpleGraph typeC:= T.induce  C

let f: VT → typeC := fun a=> if ha_in_C:(a∈ C)
  then
      ⟨a, ha_in_C⟩ --(funn  aa h123)
  else  ⟨ x, hxinC⟩


have hpreconnected: Cgraph.Preconnected:=  by
  intro a b
  have hTreach:T.Reachable ↑a ↑b:= by
    have haC:↑a∈ C:= by exact Subtype.coe_prop a
    have hbC:↑b∈ C:= by exact Subtype.coe_prop b
    exact Creachable (↑a) (↑b) haC hbC
  have nem:Nonempty (T.Walk (↑a) (↑b)):= by exact hTreach
  inhabit (T.Walk (↑a) (↑b))
  have hexW: ∃ (W:T.Walk (↑a) (↑b)), (1=1):= by exact (exists_const (T.Walk ↑a ↑b)).mpr rfl
  rcases hexW with ⟨W,_ ⟩
  have WinC:∀ (i:ℕ ), ((i ≤  W.length) →  (W.getVert i∈ C)):= by
    intro i hi1
    induction' i with i hi
    have W0:W.getVert 0=(↑a):=by simp
    have ainC:(↑a)∈ C:= by exact Subtype.coe_prop a
    exact Set.mem_of_eq_of_mem W0 ainC
    have hismall:i<W.length:= by exact hi1
    have hadj: T.Adj (W.getVert i) (W.getVert (i+1)):= by exact Walk.adj_getVert_succ W hismall
    apply htrans (W.getVert i) (W.getVert (i+1))
    have hleq:i≤ W.length:= by exact Nat.le_of_succ_le hi1
    exact hi hleq
    exact hadj

  have h0a:(W.getVert 0)=↑a:= by exact Walk.getVert_zero W
  have hlb:↑b=(W.getVert W.length):= by exact (Walk.getVert_length W).symm
  have fa: f ↑a=a:= by exact dif_pos a.property
  have fb: f ↑b=b:= by exact dif_pos b.property

  have WReachC:∀ (i:ℕ ), (i ≤  W.length) →  (Cgraph.Reachable a (f (W.getVert i))) := by
    intro i hi1
    induction' i with i hi
    rw [h0a]
    have _:↑a∈ C:= by exact Subtype.coe_prop a
    rw [fa]

    have ile:i≤ W.length := by exact Nat.le_of_succ_le hi1
    have hii:Cgraph.Reachable a (f (W.getVert i)):= by exact hi ile
    have hadj: T.Adj (W.getVert i) (W.getVert (i+1)):= by exact Walk.adj_getVert_succ W hi1
    have hin1: (W.getVert i)∈ C:= by exact Creachable x (W.getVert i) hxinC (WinC i ile)
    have hin2:(W.getVert (i+1))∈ C:= by
      exact Creachable x (W.getVert (i + 1)) hxinC (htrans (W.getVert i) (W.getVert (i + 1)) hin1 hadj)
    let v1:= (⟨(W.getVert i), hin1 ⟩: typeC )
    let v2:= (⟨(W.getVert (i+1)), hin2 ⟩: typeC )
    have fv1: f (W.getVert i)=v1:= by exact dif_pos hin1
    have fv2: f (W.getVert (i+1))=v2:= by exact dif_pos hin2
    have hii2:Cgraph.Reachable  v1 v2:= by exact Adj.reachable hadj
    rw [fv2]
    have hii':Cgraph.Reachable a v1:= by rw[fv1.symm]; exact hi ile
    exact Reachable.trans hii' hii2

  rw [ fb.symm, hlb]
  apply WReachC; exact Nat.le_refl W.length

have hacyclic: Cgraph.IsAcyclic:=  by exact induced_subgraph_of_acyclic T C Cgraph rfl hAcyclic

have hconnected: Cgraph.Connected:= by
  refine (connected_iff Cgraph).mpr ?_
  constructor
  exact hpreconnected
  exact Nonempty.intro (f x)

have htree: Cgraph.IsTree:= by exact { isConnected := hconnected, IsAcyclic := hacyclic }
have hx: ∃ (x: typeC), Cgraph.degree x ≤ 1:= by exact tree_has_a_low_deg_vertex Cgraph htree
rcases hx with ⟨x', hx ⟩

use x'
by_contra hc
have hg22:T.degree ↑x' >   1:=by exact Nat.gt_of_not_le hc
have hg2:T.degree ↑x' ≥    2:=by exact hg22
have hcardNx:Finset.card (T.neighborFinset x')≥ 2:=  by exact hg22
have twoneighbours: ∃(y z: VT), (y∈ (T.neighborFinset x'))∧ (z∈ (T.neighborFinset x')) ∧ (y≠ z):= by
  exact  one_lt_card_iff.mp hg22
rcases twoneighbours with ⟨y,z,hyz⟩

have yNx:  (y∈ (T.neighborFinset x')):= by exact hyz.1

have yxadj: T.Adj x' y := by
     exact (mem_neighborFinset T (↑x') y).mp yNx

have yinC:y∈ C:= by
  apply htrans x'
  exact Subtype.coe_prop x'
  exact yxadj

have zNx:  (z∈ (T.neighborFinset x')):= by exact hyz.2.1

have zxadj: T.Adj x' z := by
    exact (mem_neighborFinset T (↑x') z).mp zNx

have zinC:z∈ C:= by
  apply htrans x'
  exact Subtype.coe_prop x'
  exact zxadj

have heq:y=z:= by
  let y':=(⟨y, yinC ⟩: typeC)
  let z':=(⟨z, zinC ⟩: typeC)
  have x'y': Cgraph.Adj x' y' := by exact yxadj
  have x'z': Cgraph.Adj x' z' := by exact zxadj
  have y'N: y'∈ Cgraph.neighborFinset x':= by exact (mem_neighborFinset Cgraph x' y').mpr yxadj
  have z'N: z'∈ Cgraph.neighborFinset x':= by exact (mem_neighborFinset Cgraph x' z').mpr zxadj
  have hcardN: (Cgraph.neighborFinset x').card≤ 1:= by exact hx
  have y'z': y'=z':= by
    by_contra yzneq
    let ys:= ({y'}: Finset typeC)
    let zs:= ({z'}: Finset typeC)
    let yzs:= ({y', z'}: Finset typeC)
    have yzcard: yzs.card=2:= by exact card_pair yzneq
    have yscont: ys⊆ Cgraph.neighborFinset x':= by exact singleton_subset_iff.mpr y'N
    have zscont: zs⊆ Cgraph.neighborFinset x':= by exact singleton_subset_iff.mpr z'N
    have yzscont: yzs⊆ Cgraph.neighborFinset x':= by calc
      yzs=ys∪ zs:=by exact rfl
      _⊆ Cgraph.neighborFinset x':= by exact union_subset yscont zscont

    #check card_le_card
    have hcard: (Cgraph.neighborFinset x').card>1:= by calc
      (Cgraph.neighborFinset x').card≥ yzs.card:= by apply card_le_card yzscont
      _=2:= by exact yzcard
      _>1:= by exact Nat.one_lt_two
    have hneg: ¬ ((Cgraph.neighborFinset x').card ≤ 1):= by exact Nat.not_le_of_lt hcard
    exact hneg hx

  have hyy':y=↑y':= by exact rfl
  have hzz':z=↑z':= by exact rfl
  rw [hyy', hzz']
  exact congrArg Subtype.val y'z'


exact hyz.2.2 heq

theorem card_greater_1_implies_element (hCard:Fintype.card VT ≥  1): ∃(v:VT), (1=1):= by
have nonempt1:Fintype.card VT>0 := by exact hCard
have nonemp: Nonempty VT := by exact Fintype.card_pos_iff.mp nonempt1
exact (exists_const VT).mpr rfl

theorem embed_acyclic_min_degree
(k:ℕ):
∀(VT: Type u)(hf: Fintype VT)(T: SimpleGraph VT)(hT : T.IsAcyclic)(hDeg : G.minDegree ≥ k+1)(hSize:Fintype.card VT=k+1)(vG:VG),
∃ (f: T →g G), (Function.Injective f.toFun) := by
induction' k  with  k ih
intro VT hf T hT  hDeg hSize vG
case zero
have hex: ∃ (vv:VT),(1=1):= by
  apply card_greater_1_implies_element;
  exact  Nat.le_of_eq (id hSize.symm)
rcases hex with ⟨vv,_ ⟩
have hVT_order:Fintype.card VT=1:= by exact hSize
have hutExists: ∃ (uT:VT), T.degree uT≤ 1:= by exact acyclic_has_a_low_deg_vertex T hT vv
rcases hutExists with ⟨uT, huT ⟩
have h5hkjh:∃ (f: T →g  G),  (f uT= vG)∧ (Function.Injective f.toFun) :=
by exact inj_hom_from_graph_with_one_vertex G T uT vG  hVT_order
rcases h5hkjh with ⟨f, hf⟩
use f, hf.2


--case succ
--intro
intro VT hf T hT hDeg hSize vG
have hex: ∃ (vv:VT),(1=1):= by
  apply card_greater_1_implies_element;
  calc
    Fintype.card VT = k + 1 + 1:= by exact hSize
    _≥ 1:= by exact Nat.le_add_left 1 (k + 1)
rcases hex with ⟨vv,_ ⟩
have hltExists: ∃ (lT:VT), T.degree lT≤ 1:= by exact acyclic_has_a_low_deg_vertex T hT vv
rcases  hltExists with ⟨lT, hlT_leaf ⟩

let VTT: Finset VT:= Finset.univ
let VTS: Finset VT:= ({lT}: Finset VT)
have h1Size: Finset.card VTT=Fintype.card VT:= by exact rfl
have h2Size: Finset.card VTS=1:= by exact rfl

have xu1:lT∈ VTS:= by exact mem_singleton.mpr rfl

let VT': Finset VT:=  VTT \ VTS

have hVT'_membership: ∀(x:VT), (x≠ lT)→ (x∈ VT'):= by
  intro x hx
  have huT_inVT'0:x∈ VTSᶜ := by
    simp
    exact not_mem_singleton.mpr hx
  have huT_inVT'1:(x∈ VTT):= by exact mem_univ x
  have huT_inVT'2:x∈  VTT \ VTS:=by exact huT_inVT'0
  exact huT_inVT'0
have hVT'_membership2: ∀(x:VT), (lT≠ x)→ (x∈ VT'):= by
  exact fun x a =>   hVT'_membership x (id (Ne.symm a))


--have huTVT':uT∈  VT':=by exact hVT'_membership uT (id (Ne.symm hLeaf))

have h3Size: Finset.card VT'=(Finset.card VTT)-(Finset.card VTS):= by
  have hcont: VTS⊆ VTT:= by exact subset_univ VTS
  exact card_sdiff hcont


let typeVT':= { x // x ∈ VT' }

let T':SimpleGraph typeVT':= by exact induce VT' T
have hsiz: (Fintype.card typeVT')=(Finset.card VT'):= by exact Fintype.card_coe VT'

have hSize': Fintype.card typeVT'=k+1:= by calc
   Fintype.card typeVT'=(Finset.card VT'):= by exact hsiz
   _=(Finset.card VTT)-(Finset.card VTS):= by exact h3Size
   _=Fintype.card VT-1:= by exact rfl
   _=k+1+1-1:= by exact congrFun (congrArg HSub.hSub hSize) 1
   _=k+1:= by simp


have hNonempty0: Fintype.card typeVT'≥ 1:= by calc
  Fintype.card typeVT'=k+1:= by exact hSize'
  _≥ 1:= by exact Nat.le_add_left 1 k

have hNonempty: Nonempty VT':= by exact Fintype.card_pos_iff.mp hNonempty0
inhabit typeVT'
have hAcyclic':T'.IsAcyclic:= by
  exact induced_subgraph_of_acyclic T (fun x => x ∈ VT'.val) T' rfl hT
have hDeg':  G.minDegree ≥ k+1:= by exact Nat.le_of_succ_le hDeg

have hInduction: ∃ (f: T' →g G),  (Function.Injective f.toFun):= by
  apply ih
  exact hAcyclic'
  exact hDeg'
  exact hSize'
  exact vG

rcases hInduction with ⟨f', hf'⟩

let VTT2: Finset typeVT':= Finset.univ
let imset:Finset VG:=image f' VTT2
have hSize'': Finset.card imset≤ k+1:= by calc
  Finset.card imset≤Finset.card VTT2:= by exact card_image_le
  _=k+1:= by exact hSize'


--have hf'2:f' ⟨uT, huTVT' ⟩ =vG:= by exact hf'.1

have lT'existence: ∃ (lT':VT), (lT'≠ lT)∧ (∀ (y: VT), (T.Adj lT y)→(y=lT')):= by
  have hSize1: Fintype.card VT≥ 2:= by linarith
  exact at_most_one_neighbour T hSize1 lT hlT_leaf
rcases lT'existence with ⟨lT', lT'Property⟩
have hlT':lT'≠ lT:=by exact lT'Property.1
have h3lT': ∀(x: VT), T.Adj lT x → x=lT' := by exact lT'Property.2
have h2lT': lT'∈ VT' := by exact hVT'_membership lT' hlT'
let f'lT':= (f'.toFun ⟨lT', h2lT' ⟩)

have hDegree_lT': G.degree (f'lT')≥  k+2:= by calc
  G.degree (f'lT')≥ G.minDegree := by
    exact    minDegree_le_degree G (f'lT')
  _≥ k+2:=by exact hDeg

let sDiff:Finset VG:=   ((G.neighborFinset (f'lT'))\ imset )
have hsDiff_size: Finset.card sDiff≥ 1:= by calc
  Finset.card sDiff =Finset.card  ((G.neighborFinset (f'lT'))\ imset ):= by exact rfl
  _≥ (Finset.card (G.neighborFinset (f'lT')))- (Finset.card imset):= by
    exact le_card_sdiff imset (G.neighborFinset f'lT')
  _≥ (k+2)-   (Finset.card imset):= by exact Nat.sub_le_sub_right hDegree_lT' imset.card
  _≥ (k+2)-(k+1):= by exact Nat.sub_le_sub_left hSize'' (k + 2)
  _=1:= by simp
have hsDiff_size': Finset.card sDiff≠ 0 := by exact Ne.symm (Nat.ne_of_lt hsDiff_size)
have hNonempty: sDiff≠ ∅ :=  by
  exact  Ne.symm (ne_of_apply_ne card fun a => hsDiff_size' (id a.symm))
have hexvNew: ∃ (vNew: VG), (vNew∈ sDiff):= by exact Multiset.card_pos_iff_exists_mem.mp hsDiff_size
rcases hexvNew with ⟨vNew, hvNew ⟩



let f: VT → VG := fun a=> if ha_in_VT':(a∈ VT')
  then
     f' ⟨a, ha_in_VT'⟩ --(funn  aa h123)
  else  vNew


--have hvt: f uT= vG :=by calc
--  f uT= f' ⟨uT, huTVT'⟩:= by exact dif_pos huTVT'
 -- _= vG:= by  exact hf'.1

have hImage_il: f lT = vNew := by
  have hLoc_lT: lT∉VT':= by exact not_mem_sdiff_of_mem_right xu1
  exact (Ne.dite_eq_right_iff fun h a => hLoc_lT h).mpr hLoc_lT


have hImagef_lT': f lT' = f'lT':= by
  have hLoc: f lT'= f' ⟨lT', h2lT'⟩:= by exact dif_pos h2lT'
  exact hLoc

have hHomolT: ∀ (d:VT), T.Adj lT d → G.Adj (f lT) (f d):= by
  intro d hAdj
  have hd: d=lT':= by exact h3lT' d hAdj
  have hcont: sDiff⊆ (G.neighborFinset f'lT'):= by
    exact    sdiff_subset (G.neighborFinset f'lT') imset
  have hfd2: vNew∈ (G.neighborFinset f'lT'):= by exact hcont hvNew
  have hAdj2:G.Adj f'lT' vNew:= by
    exact (mem_neighborFinset G f'lT' vNew).mp (hcont hvNew)
  have hAdj3:G.Adj  vNew f'lT':= by exact id (adj_symm G hAdj2)
  rw [hImage_il]
  rw [hd, hImagef_lT']
  exact hAdj3

have hHomolT2: ∀ (d:VT), T.Adj  d lT → G.Adj (f d) (f lT):= by
  intro d hd
  apply symm
  exact hHomolT d (id (adj_symm T hd))

have hHomo: ∀ (c d:VT), T.Adj c d → G.Adj (f c) (f d):= by
  intro c d hAdj
  by_cases hc_in:c=lT
  rw [hc_in]
  apply hHomolT
  rw [hc_in.symm]
  exact hAdj

  by_cases hd_in:d=lT
  rw [hd_in]
  apply hHomolT2
  rw [hd_in.symm]
  exact hAdj

  have hcin: c∈ VT':= by exact hVT'_membership c hc_in
  have hcim: f c= f' ⟨c, hcin⟩:= by exact dif_pos hcin
  have hdin: d∈ VT':= by exact hVT'_membership d hd_in
  have hdim: f d= f' ⟨d, hdin⟩:= by exact dif_pos hdin

  rw [hcim, hdim]
  exact Hom.map_adj f' hAdj

--have hHomo':T.Adj _ _ → G.Adj (f _) (f _):= by exact?
have hfInj: ∀ (c d:VT), (c=lT)→ (d≠ lT)→ f c≠ f d:= by
  intro c d hc  hd
  have hdin: d∈ VT':= by exact hVT'_membership d hd
  have hdim: f d= f' ⟨d, hdin⟩:= by exact dif_pos hdin
  have hcim: f c= vNew:= by
    rw [hc]
    exact hImage_il
  have hd2:  ⟨d, hdin⟩∈ VTT2:= by  exact mem_univ (⟨d, hdin⟩: typeVT')
  have hd3:f' ⟨d, hdin⟩∈ imset:= by exact mem_image_of_mem (⇑f') hd2
  have hd4:f' ⟨d, hdin⟩ ∉ sDiff:= by exact not_mem_sdiff_of_mem_right hd3
  have hd5: vNew≠ f' ⟨d, hdin⟩:= by
    simp
    by_contra h
    have hh: vNew∉ sDiff:= by rw[h]; exact hd4
    exact hh hvNew
  rw[hdim, hcim]; exact hd5

have hInjective: Function.Injective f:= by
  intro c d hcd
  by_cases hc: c=lT
  by_cases hd: d=lT
  rw[hc, hd]

  have hcont:f c ≠ f d := by exact hfInj c d hc hd
  exfalso
  exact hcont hcd

  by_cases hd: d=lT
  have hcont:f d ≠ f c := by exact hfInj d c hd hc
  exfalso
  exact hfInj d c hd hc (id hcd.symm)

  have cin: c∈ VT':= by exact hVT'_membership c hc
  have din: d∈ VT':= by exact hVT'_membership d hd
  by_contra hcont
  have hneq: (⟨c, cin⟩:  typeVT') ≠   (⟨d, din⟩:  typeVT'):= by
    apply (Subtype.coe_ne_coe).1--Subtype.ne_of_val_ne hcont
    exact hcont
  have hf'neq: f' ⟨c, cin⟩≠ f' ⟨d, din⟩:= by exact fun a => hneq (hf' a)
  have hfc: f c= f' ⟨c, cin⟩:= by exact dif_pos cin
  have hfd: f d= f' ⟨d, din⟩:= by exact dif_pos din
  have hfcd: f c ≠ f d := by rw[hfc, hfd]; exact hf'neq
  exact hfcd hcd


let fhom: T→g G:=  RelHom.mk f @hHomo
use fhom
