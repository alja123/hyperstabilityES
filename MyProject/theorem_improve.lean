import MyProject
import MyProject.Subgraph
import MyProject.theorem_combine
import Mathlib.Combinatorics.SimpleGraph.Connectivity


open Classical
open Finset

namespace SimpleGraph



universe u
variable {V : Type u} {K : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel K.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]

variable (iV:Inhabited V)
variable (KComplete: K=completeGraph V)



lemma connected_components_contained
(G: SimpleGraph V)
(H C: Subgraph G)
(Com : List (Set V))
(cover: Components_cover_graph H Com)
(disjoint: Components_disjoint Com)
(noedges: No_edges_between_components H Com)
(Cconnected:  C.Connected)
(CinH: C≤ H)
:
∃ (ComC: Set V), ComC ∈ Com ∧ C.verts ⊆ ComC
:= by
have Csub: C.verts⊆ H.verts:= by
    apply subgraphs_vertex_sets_subsets G
    exact CinH
have Cnonemp: C.verts.Nonempty:= by
  exact Subgraph.Connected.nonempty Cconnected
let u:V := Cnonemp.some
have uinC: u∈C.verts:= by
  dsimp[u]
  exact Set.Nonempty.some_mem Cnonemp
have uinH:u∈H.verts:= by
  dsimp[u]
  exact Csub uinC

unfold Components_cover_graph at cover
have hiex: _:= by exact cover u uinH
rcases hiex with ⟨i, hi⟩

use Com.get! i
have ile: i<Com.length:= by
  have h1: i<Com.length:= by
    exact hi.left
  exact h1
have geteq: Com.get! i=Com.get ⟨ i, ile ⟩:= by
  exact (get_eq_get2! Set.instInhabited Com i ile).symm
constructor
rw[geteq]
exact List.get_mem Com i ile

refine Set.diff_eq_empty.mp ?h.right.a
by_contra cont
rw [← @Set.not_nonempty_iff_eq_empty] at cont
simp only [ Decidable.not_not] at cont
let v:V := cont.some


have vinC: v∈ (C.verts \ Com.get! i):= by
  dsimp[v]
  exact Set.Nonempty.some_mem cont
simp only [ Set.mem_diff] at vinC

have vinH:v∈H.verts:= by
  dsimp[v]
  exact Csub vinC.1
have hjex: _:= by exact cover v vinH
rcases hjex with ⟨j, hj⟩

have ineqj: i≠j:= by
  by_contra cont1
  rw[cont1.symm] at hj
  exact vinC.2 hj.2

have Wex:  ∃ (W : G.Walk u v), W.toSubgraph ≤ C:= by
  have conequiv:_:=by exact (Subgraph.connected_iff_forall_exists_walk_subgraph C).1 Cconnected
  apply conequiv.2
  exact uinC
  exact vinC.1
rcases Wex with ⟨W, WsubC⟩
let S: Set ℕ  := {n: ℕ  | W.getVert n ∉  Com.get! i}
let t: ℕ := sInf S
have h0: 0∉  S:= by
  have eqq: W.getVert 0=u:= by
    exact Walk.getVert_zero W
  dsimp[S]
  simp only [Walk.getVert_zero,  Decidable.not_not]
  exact hi.2
have hl: W.length∈  S:= by
  have eqq: W.getVert W.length=v:= by
    exact Walk.getVert_length W
  dsimp[S]
  rw[eqq]
  exact vinC.2
have tub: t≤ W.length:= by
  dsimp[t, S]
  exact Nat.sInf_le hl



have tin: t∈ S:= by
  dsimp[t]
  apply Nat.sInf_mem
  use W.length

/-have tne: t≠ W.length:= by
  by_contra cont2
  rw[cont2] at tin
  dsimp[S] at tin
  have eqq: W.getVert W.length=v:= by
    exact Walk.getVert_length W
  rw[eqq] at tin-/


have tne0: t≠0:= by
  dsimp[t]
  by_contra cont2
  dsimp[t] at tin
  rw[cont2] at tin
  exact h0 tin
have tmnin: t-1∉ S:= by
  dsimp[t]
  refine Nat.not_mem_of_lt_sInf ?hm
  refine Nat.sub_one_lt_of_le ?hm.h₀ ?hm.h₁
  refine Nat.zero_lt_of_ne_zero ?hm.h₀.h
  exact tne0
  simp
#check SimpleGraph.Walk.toSubgraph_adj_iff
have teq: t-1+1=t:= by
  apply Nat.sub_add_cancel
  dsimp[t]
  refine Nat.one_le_iff_ne_zero.mpr ?h.a
  exact tne0

have hinC: W.toSubgraph.Adj (W.getVert (t-1)) (W.getVert (t-1+1)):= by
  apply Walk.toSubgraph_adj_getVert
  refine Nat.sub_one_lt_of_le ?hi.h₀ tub
  exact Nat.zero_lt_of_ne_zero tne0

dsimp[S ]at tmnin
simp only [Decidable.not_not] at tmnin
dsimp[S] at tin
rw[teq] at hinC




have tinH:(W.getVert t)∈H.verts:= by
  have h1: (W.getVert t)∈W.toSubgraph.verts:= by
    exact W.toSubgraph.edge_vert (id (Subgraph.adj_symm W.toSubgraph hinC))
  have winc: W.toSubgraph.verts⊆ C.verts:= by
    apply subgraphs_vertex_sets_subsets G
    exact WsubC
  have winh: C.verts⊆ H.verts:= by
    apply subgraphs_vertex_sets_subsets G
    exact CinH
  exact winh (winc h1)
have hkex: _:= by exact cover (W.getVert t) tinH
rcases hkex with ⟨k, hk⟩

have ineqj: i≠k:= by
  by_contra cont1
  rw[cont1.symm] at hk
  exact tin hk.2

have nonadj: ¬(H.Adj (W.getVert (t-1)) (W.getVert t)):= by
  unfold No_edges_between_components at noedges
  apply noedges
  use hi.1
  use hk.1
  exact ineqj
  exact tmnin
  exact hk.2
have adj: H.Adj (W.getVert (t-1)) (W.getVert t):= by
  have h2: W.toSubgraph ≤ H:= by
    exact Preorder.le_trans W.toSubgraph C H WsubC CinH
  exact subgraph_implies_adjacency_inherited h2 hinC
exact h0 fun a ↦ nonadj adj


def large_enough: ℕ → ℕ := fun ε => max ( max (gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))   (gg1 (gg1 (gg2 (gg1 ε))))) 1


theorem version4
(G: Subgraph K)
(ε d C: ℕ )
(C_large: C ≥ large_enough ε )
(d_ge_C: d ≥ C)
(G_has_no_d_paths: ¬ Has_length_d_path (G) (d))
(Hedges: ε *G.edgeSet.toFinset.card ≥ d*G.verts.toFinset.card)
:
∃(H: Subgraph K),
(H≤ G)
∧
(ε *H.edgeSet.toFinset.card+ G.edgeSet.toFinset.card≥ ε *G.edgeSet.toFinset.card)
∧
(∀ (Comp: Subgraph K), Comp≤ H∧  Comp.Connected
  → ∃ (Cover: Finset V),
    Cover.card≤ C* d
      ∧ ∀ (u v : V), (u ∈ Comp.verts) ∧  (v ∈ Comp.verts) ∧  (H.Adj u v) →
        (u∈ Cover ∨ v∈ Cover))

:= by
have CPositive: C≥ 1:= by
  unfold large_enough at C_large
  exact le_of_max_le_right C_large
have dPositive: d>0:= by
  exact lt_of_lt_of_le CPositive d_ge_C
by_cases case: G.verts.toFinset.card=0
use G
simp only [  card_eq_zero] at case
simp at case
have hGemp: G=⊥:=by
  ext v w
  simp
  exact of_eq_false (congrArg (Membership.mem v) case)
  simp
  by_contra cont
  have vin: v∈ G.verts:= by
    exact G.edge_vert cont
  have vnin: v∉ G.verts:= by
    exact of_eq_false (congrArg (Membership.mem v) case)
  exact vnin vin



constructor
simp

constructor
rw[hGemp]
simp


intro Comp ⟨hComp1, hComp2 ⟩
use ∅
constructor
simp

intro u v huv
exfalso
rw[hGemp] at hComp1
simp at hComp1
rw[hComp1] at huv
simp at huv

have Hpos: G.verts.toFinset.card > 0:= by
  exact Nat.zero_lt_of_ne_zero case

have mulpos: ε *G.edgeSet.toFinset.card>0:= by
  calc
    ε *G.edgeSet.toFinset.card ≥ d*G.verts.toFinset.card:= by
        exact Hedges
    _>0:= by
      apply Nat.mul_pos
      exact dPositive
      exact Hpos

have εPositive: ε>0:= by
  exact Nat.pos_of_mul_pos_right mulpos

have GEpos: G.edgeSet.toFinset.card>0:= by
  exact Nat.pos_of_mul_pos_left mulpos

have ex:
  ∃(Sub: Subgraph K), ∃ (Com Cov: List (Set V)),
  Components_cover_graph Sub Com
  ∧
  Components_disjoint Com
  ∧
  No_edges_between_components Sub Com
  ∧
  Components_covered_by_covers Sub Com Cov
  ∧
  Covers_small (gg1 (gg1 (gg2 (gg1 ε)))) d Cov
  ∧
  (ε *Sub.edgeSet.toFinset.card+ G.edgeSet.toFinset.card≥ ε *G.edgeSet.toFinset.card)
  ∧
  (Sub ≤ G)
  ∧
  (Com.length=Cov.length)
  := by
    apply version3
    repeat assumption
    exact Subgraph.subgraphInhabited


    simp only [ card_eq_zero] at case
    simp at case
    have h1: Nonempty (G.verts):= by
      exact Set.nonempty_iff_ne_empty'.mpr case
    let v:V:= h1.some
    refine inhabited_of_nonempty ?iSP.h
    refine Nonempty.intro ?iSP.h.val
    refine { H := ?iSP.h.val.H, s := ?iSP.h.val.s, e := ?iSP.h.val.e, Pa := ?iSP.h.val.Pa }
    exact  G
    exact v
    exact v
    refine
      { Wa := ?iSP.h.val.Pa.Wa, Wa_Is_Path := ?iSP.h.val.Pa.Wa_Is_Path,
        Wa_In_H := ?iSP.h.val.Pa.Wa_In_H }
    exact Walk.nil' v
    exact Walk.IsPath.nil
    simp
    dsimp[v]
    exact Subtype.coe_prop h1.some

    repeat assumption
    calc
        d≥ C:= by
          exact d_ge_C
        _≥ max (gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))   (gg1 (gg1 (gg2 (gg1 ε)))):= by
          unfold large_enough at C_large
          exact le_of_max_le_left C_large
        _≥ _:= by
          exact     Nat.le_max_left (gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))            (gg1 (gg1 (gg2 (gg1 ε))))
    repeat assumption


rcases ex with ⟨Sub, ex1⟩
rcases ex1 with ⟨Com, Cov, a1, a2, a3, a4, a5, a6, a7, a8⟩
use Sub
constructor
exact a7
constructor
exact a6

intro Comp ⟨hComp1, hComp2⟩

have ComCex:  ∃ (ComC: Set V), ComC ∈ Com ∧ Comp.verts ⊆ ComC:= by
  apply connected_components_contained
  exact a1
  exact a2
  repeat assumption
rcases ComCex with ⟨ComC, hComC1, hComC2⟩

unfold Components_covered_by_covers at a4
have hiex: ∃ (i: Fin (Com.length)), Com.get i=ComC:= by
  exact List.mem_iff_get.mp hComC1
rcases hiex with ⟨⟨i, hi1⟩ , hi2⟩
have geteq:  Com.get! i = ComC:= by
  rw[hi2.symm]
  simp
  exact List.getD_eq_get Com default hi1

use (Cov.get! i).toFinset
constructor

unfold Covers_small at a5
calc
  (Cov.get! i).toFinset.card
  ≤gg1 (gg1 (gg2 (gg1 ε))) * d:= by
    apply a5
    rw[a8.symm]
    exact hi1
  _≤ C * d:= by
    gcongr
    calc
      _≥ max (gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))   (gg1 (gg1 (gg2 (gg1 ε)))):= by
          unfold large_enough at C_large
          exact le_of_max_le_left C_large
      _≥ _:= by
          exact
            Nat.le_max_right (gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))
              (gg1 (gg1 (gg2 (gg1 ε))))




intro u v ⟨ huv1, huv2, huv3⟩
simp only [Set.mem_toFinset]
apply a4
exact hi1
rw[geteq]
exact hComC2 huv1
rw[geteq]
exact hComC2 huv2
exact huv3







theorem version5
(G: Subgraph K)
(ε: ℚ)
(εPositive: ε >0)
(d C: ℕ )
(C_large: C ≥ large_enough (Nat.ceil (1/ε)) )
(d_ge_C: d ≥ C)
(G_has_no_d_paths: ¬ Has_length_d_path (G) (d))
(Hedges: (G.edgeSet.toFinset.card: ℚ) ≥ ε*d*(G.verts.toFinset.card: ℚ ))
:
∃(H: Subgraph K),
(H≤ G)
∧
((H.edgeSet.toFinset.card: ℚ )≥ (1-ε) *(G.edgeSet.toFinset.card: ℚ))
∧
(∀ (Comp: Subgraph K), Comp≤ H∧  Comp.Connected
  → ∃ (Cover: Finset V),
    Cover.card≤ C* d
      ∧ ∀ (u v : V), (u ∈ Comp.verts) ∧  (v ∈ Comp.verts) ∧  (H.Adj u v) →
        (u∈ Cover ∨ v∈ Cover))

:= by
let ei: ℕ := Nat.ceil (1/ε)
have Hedges1: ei*G.edgeSet.toFinset.card ≥ d*G.verts.toFinset.card:=by
  have h1: ((ei*G.edgeSet.toFinset.card: ℕ ): ℚ  )≥ ((d*G.verts.toFinset.card: ℕ ): ℚ ):= by
    simp only [Nat.cast_mul]
    calc
      ↑ei * ↑G.edgeSet.toFinset.card ≥ ei *(ε*d*(G.verts.toFinset.card: ℚ )):= by
        gcongr
      _≥  (1/ε)*(ε*d*(G.verts.toFinset.card: ℚ )):= by
        gcongr
        dsimp[ei]
        exact Nat.le_ceil (1 / ε)
      _= (ε /ε)*(d*(G.verts.toFinset.card: ℚ )):= by
        ring_nf
      _= d*(G.verts.toFinset.card: ℚ ):= by
        field_simp

  apply Nat.cast_le.mp h1


have ex:
  ∃(H: Subgraph K),
  (H≤ G)
  ∧
  (ei *H.edgeSet.toFinset.card+ G.edgeSet.toFinset.card≥ ei *G.edgeSet.toFinset.card)
  ∧
  (∀ (Comp: Subgraph K), Comp≤ H∧  Comp.Connected
    → ∃ (Cover: Finset V),
      Cover.card≤ C* d
        ∧ ∀ (u v : V), (u ∈ Comp.verts) ∧  (v ∈ Comp.verts) ∧  (H.Adj u v) →
          (u∈ Cover ∨ v∈ Cover)):= by
    apply version4
    repeat assumption

rcases ex with ⟨H, hH1, hH2,  ex2⟩
use H
constructor
exact hH1
constructor
have rat1: ((ei * H.edgeSet.toFinset.card + G.edgeSet.toFinset.card: ℕ ): ℚ ) ≥ ((ei * G.edgeSet.toFinset.card: ℕ  ): ℚ ):= by
  exact
    nat_le_rat (ei * G.edgeSet.toFinset.card)
      (ei * H.edgeSet.toFinset.card + G.edgeSet.toFinset.card) hH2
simp only [Nat.cast_add, Nat.cast_mul] at rat1
have rat2: (ei * H.edgeSet.toFinset.card : ℚ )≥  ((↑ei -1)* ↑G.edgeSet.toFinset.card: ℚ ):= by
  linarith
have rat3: ( H.edgeSet.toFinset.card : ℚ )≥  ((ei -1)* ↑G.edgeSet.toFinset.card/ei: ℚ ):= by
  calc
    (H.edgeSet.toFinset.card: ℚ)= H.edgeSet.toFinset.card*(ei/ei):= by
      field_simp
    _=ei * H.edgeSet.toFinset.card /ei:= by
      ring_nf
    _≥ _:= by
      gcongr

calc
  (H.edgeSet.toFinset.card: ℚ)≥ ((ei -1)* ↑G.edgeSet.toFinset.card/ei: ℚ ):=by
    exact rat3
  _= (ei/ei -1/ei)* G.edgeSet.toFinset.card:= by
    ring_nf
  _= (1-1/ei)* G.edgeSet.toFinset.card:= by
    field_simp
  _≥  (1-ε)* G.edgeSet.toFinset.card:= by
    gcongr
    dsimp[ei]
    calc
      1 / ↑⌈1 / ε⌉₊ ≤1 / (1 / ε):= by
        gcongr
        simp
        exact Nat.le_ceil ε⁻¹
      _= ε:= by
        ring_nf
        field_simp
        --


exact ex2





/-
theorem version4
(G: Subgraph K)
(ε d: ℕ )
(εPositive: ε >0)
(dPositive: d>0)

(dggε: d ≥ gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))

(no_paths: ¬ Has_length_d_path (H) (d))
(HNonempty: H.edgeSet.toFinset.card>0)
(Hedges: ε *H.edgeSet.toFinset.card ≥ d*H.verts.toFinset.card)
:
∃(Sub: Subgraph G), ∃ (Com Cov: List (Set V)),
Components_cover_graph Sub Com
∧
Components_disjoint Com
∧
No_edges_between_components Sub Com
∧
Components_covered_by_covers Sub Com Cov
∧
Covers_small (gg1 (gg1 (gg2 (gg1 ε)))) d Cov
∧
(ε *Sub.edgeSet.toFinset.card+ H.edgeSet.toFinset.card≥ ε *H.edgeSet.toFinset.card)
:= by
apply version3
repeat assumption
-/
