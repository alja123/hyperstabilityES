import MyProject

import MyProject.path.path_forests
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 170000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )




/-
lemma Cut_dense_long_path
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u: V)
(u_in_H: u ∈ H.verts)
(d: ℕ)
(hd: p*d < H.verts.toFinset.card)
:
∃ (v: V), ∃ (P: SubgraphPath H u v), P.Wa.length+1= d+1
:=by
-/

lemma subtract_one_mult2
(a: ℕ)
: 2*a-a=a:=by
calc
  2*a-a=2*a-1*a:= by ring_nf
  _=(2-1)*a:= by exact (Nat.mul_sub_right_distrib 2 1 a).symm
  _=1*a:=by exact rfl
  _=a:= by ring_nf

lemma Cut_dense_long_path_avoiding_0
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u: V)
(u_in_H: u ∈ H.verts)
(d: ℕ)
(hd: 8*p*d < H.verts.toFinset.card)
(Fb: Set V)
(hu: u ∉ Fb)
(FbSmall: 4*p*(Fb).toFinset.card ≤ H.verts.toFinset.card)
:
∃ (v: V), ∃ (P: SubgraphPath H u v), P.Wa.length+1= d+1∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)
:=by

let Hd: Subgraph G:= H.deleteVerts Fb
have Hd_cutdense: cut_dense G Hd (4*p) :=by
  apply cut_dense_delete_vertices H H_cut_dense Fb
  repeat assumption


have hud: u ∈ Hd.verts := by
  dsimp[Hd]
  simp
  exact ⟨u_in_H, hu⟩



have ex: ∃ (v: V), ∃ (P: SubgraphPath Hd u v), P.Wa.length+1= d+1:= by
  apply Cut_dense_long_path Hd Hd_cutdense u hud
  --4 * p * d < Hd.verts.toFinset.card
  have h2:  H.verts.toFinset.card≤  2*Hd.verts.toFinset.card:=by
    dsimp [Hd]
    simp only [   Set.toFinset_diff]
    calc
      2*(H.verts.toFinset \ Fb.toFinset).card
      ≥2*(H.verts.toFinset.card - Fb.toFinset.card):=by
        gcongr
        exact le_card_sdiff Fb.toFinset H.verts.toFinset
      _=2*H.verts.toFinset.card - 2*Fb.toFinset.card:= by
        exact Nat.mul_sub_left_distrib 2 H.verts.toFinset.card Fb.toFinset.card
      _≥ 2*H.verts.toFinset.card - (4*p*(Fb).toFinset.card):= by
        gcongr
        calc
          2=2*1:= by ring_nf
          _≤ (4*p):= by
            gcongr
            exact Nat.AtLeastTwo.prop
            exact pPositive
      _≥  2*H.verts.toFinset.card -H.verts.toFinset.card := by
        gcongr
      _=H.verts.toFinset.card:= by
        exact subtract_one_mult2 H.verts.toFinset.card


  have h1: 2*(4 * p * d) < 2*(Hd.verts.toFinset.card):= by
    calc
      2*(4 * p * d) = 8*p*d:= by ring_nf
      _<H.verts.toFinset.card:= by exact hd
      _≤  2*Hd.verts.toFinset.card:= by exact h2
  exact Nat.lt_of_mul_lt_mul_left h1
  exact Nat.succ_mul_pos 3 pPositive

rcases ex with ⟨v, hv⟩
rcases hv with ⟨P, hP⟩

have hPHd:  (P.Wa.support.toFinset.toSet) ⊆ Hd.verts:= by
  calc
    (P.Wa.support.toFinset.toSet)⊆ P.Wa.toSubgraph.verts:= by simp
    _⊆ Hd.verts:= by
      apply  subgraphs_vertex_sets_subsets G
      exact P.Wa_In_H

have hdisj1: Disjoint (Hd.verts)  Fb:= by
  dsimp[Hd]
  exact Set.disjoint_sdiff_left

have hdisj2: Disjoint (P.Wa.support.toFinset.toSet)  Fb:= by
  exact Set.disjoint_of_subset hPHd (fun ⦃a⦄ a ↦ a) hdisj1

have PinH: P.Wa.toSubgraph≤ H:= by
  calc
    P.Wa.toSubgraph≤ Hd:= by exact P.Wa_In_H
    _≤ H:= by exact Subgraph.deleteVerts_le

let P': SubgraphPath H u v:=
  {Wa:= P.Wa
  ,Wa_Is_Path:= P.Wa_Is_Path
  ,Wa_In_H:= PinH
  }
use v
use P'


lemma card_subtract_inter_finset
(A B: Finset V)
:
((A)\ B).card= A.card-(A∩ B).card
:= by
refine (Nat.sub_eq_of_eq_add' ?h).symm
exact (card_inter_add_card_sdiff A B).symm

lemma card_subtract_inter_finset2
(A B: Finset V)
:
((A)\ B).card= A.card-(B∩ A).card
:= by
rw[inter_comm]
exact card_subtract_inter_finset A B

lemma card_subtract_inter
(A B: Set V)
:
((A).toFinset\ B.toFinset).card= A.toFinset.card-(B∩ A).toFinset.card
:= by
calc
((A).toFinset\ B.toFinset).card
= (A.toFinset).card-(B.toFinset∩ A.toFinset).card:= by
  exact card_subtract_inter_finset2 A.toFinset B.toFinset
_=(A.toFinset.card-(B∩ A).toFinset.card):= by
  simp

lemma card_subtract_inter2
(A B: Set V)
:
((A).toFinset\ B.toFinset).card= A.toFinset.card-(A∩ B).toFinset.card
:= by
calc
((A).toFinset\ B.toFinset).card
= (A.toFinset).card-(A.toFinset∩ B.toFinset).card:= by
  exact card_subtract_inter_finset A.toFinset B.toFinset
_=(A.toFinset.card-(A∩ B).toFinset.card):= by
  simp


lemma card_subtract_inter3
(A B: Set V)
:
(A\ B).toFinset.card=A.toFinset.card-(B∩ A).toFinset.card
:= by
simp only [Set.toFinset_diff]
exact card_subtract_inter A B

lemma card_subtract_inter4
(A B: Set V)
:
(A\ B).toFinset.card=A.toFinset.card-(A∩ B).toFinset.card
:= by
simp only [Set.toFinset_diff]
exact card_subtract_inter2 A B


lemma Cut_dense_long_path_avoiding
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u: V)
(u_in_H: u ∈ H.verts)
(d: ℕ)
(hd: 8*p*d < H.verts.toFinset.card)
(Fb: Set V)
(hu: u ∉ Fb)
(FbSmall: 4*p*(Fb∩ H.verts).toFinset.card ≤ H.verts.toFinset.card)
:
∃ (v: V), ∃ (P: SubgraphPath H u v), P.Wa.length+1= d+1∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)∧ v∈ H.verts
:=by
let Hd: Subgraph G:= H.deleteVerts Fb
have Hd_cutdense: cut_dense G Hd (4*p) :=by
  let Fb':Set V:=Fb∩ H.verts
  have h1: H.deleteVerts Fb=H.deleteVerts Fb':= by
    exact Subgraph.deleteVerts_inter_verts_set_right_eq.symm
  dsimp[Hd]
  rw[h1]
  apply cut_dense_delete_vertices H H_cut_dense Fb'
  repeat assumption
  dsimp [Fb']
  simp
  simp at FbSmall
  exact FbSmall
  repeat assumption


have hud: u ∈ Hd.verts := by
  dsimp[Hd]
  simp
  exact ⟨u_in_H, hu⟩





have ex: ∃ (v: V), ∃ (P: SubgraphPath Hd u v), P.Wa.length+1= d+1:= by
  apply Cut_dense_long_path Hd Hd_cutdense u hud
  --4 * p * d < Hd.verts.toFinset.card
  have h2:  H.verts.toFinset.card≤  2*Hd.verts.toFinset.card:=by
    dsimp [Hd]
    simp only [   Set.toFinset_diff]
    calc
      2*(H.verts.toFinset \ Fb.toFinset).card
      =2*(H.verts.toFinset.card - (Fb∩ H.verts).toFinset.card):=by
        congr
        exact card_subtract_inter H.verts Fb
      _=2*H.verts.toFinset.card - 2*(Fb∩ H.verts).toFinset.card:= by
        exact Nat.mul_sub_left_distrib 2 H.verts.toFinset.card (Fb∩ H.verts).toFinset.card
      _≥ 2*H.verts.toFinset.card - (4*p*((Fb∩ H.verts)).toFinset.card):= by
        gcongr
        calc
          2=2*1:= by ring_nf
          _≤ (4*p):= by
            gcongr
            exact Nat.AtLeastTwo.prop
            exact pPositive
      _≥  2*H.verts.toFinset.card -H.verts.toFinset.card := by
        gcongr
      _=H.verts.toFinset.card:= by
        exact subtract_one_mult2 H.verts.toFinset.card


  have h1: 2*(4 * p * d) < 2*(Hd.verts.toFinset.card):= by
    calc
      2*(4 * p * d) = 8*p*d:= by ring_nf
      _<H.verts.toFinset.card:= by exact hd
      _≤  2*Hd.verts.toFinset.card:= by exact h2
  exact Nat.lt_of_mul_lt_mul_left h1
  exact Nat.succ_mul_pos 3 pPositive

rcases ex with ⟨v, hv⟩
rcases hv with ⟨P, hP⟩

have hPHd:  (P.Wa.support.toFinset.toSet) ⊆ Hd.verts:= by
  calc
    (P.Wa.support.toFinset.toSet)⊆ P.Wa.toSubgraph.verts:= by simp
    _⊆ Hd.verts:= by
      apply  subgraphs_vertex_sets_subsets G
      exact P.Wa_In_H

have hdisj1: Disjoint (Hd.verts)  Fb:= by
  dsimp[Hd]
  exact Set.disjoint_sdiff_left

have hdisj2: Disjoint (P.Wa.support.toFinset.toSet)  Fb:= by
  exact Set.disjoint_of_subset hPHd (fun ⦃a⦄ a ↦ a) hdisj1

have PinH: P.Wa.toSubgraph≤ H:= by
  calc
    P.Wa.toSubgraph≤ Hd:= by exact P.Wa_In_H
    _≤ H:= by exact Subgraph.deleteVerts_le

let P': SubgraphPath H u v:=
  {Wa:= P.Wa
  ,Wa_Is_Path:= P.Wa_Is_Path
  ,Wa_In_H:= PinH
  }

have hvin: v∈ H.verts:=by
  have h6: v∈{v:V|v∈ P.Wa.support}:= by
    simp
  have h7: {v:V|v∈ P.Wa.support}⊆ H.verts:=by
    calc
      {v:V|v∈ P.Wa.support}⊆ P.Wa.toSubgraph.verts:=by    simp
      _⊆ H.verts:=by
        apply subgraphs_vertex_sets_subsets
        exact PinH
  exact h7 h6

use v
use P'

lemma disjoint_elim
{A B: Set V}
(h: Disjoint A B)
{a: V}
{ha: a ∈ A}
:
a ∉ B
:= by
by_contra cont
have h1: {a}≤ A:= by simp; assumption
have h2: {a}≤ B:= by simp; assumption
apply h h1 h2
exact rfl


lemma disjoint_elim2
{A B: Set V}
(h: Disjoint A B)
{a: V}
{ha: a ∈ B}
:
a ∉ A
:= by
by_contra cont
have h1: {a}≤ A:= by simp; assumption
have h2: {a}≤ B:= by simp; assumption
apply h h1 h2
exact rfl

lemma Walk_start_not_in_tail
{a b: V}
(P: Walk G a b)
(hP: P.IsPath)
:
a ∉ P.support.tail
:=by
have h2: P.support= a::P.support.tail:= by
  exact Walk.support_eq_cons P
have h3: P.support.Nodup:= by exact hP.support_nodup
refine List.singleton_disjoint.mp ?_
rw[h2] at h3
exact List.disjoint_of_nodup_append h3



lemma outside_list_imp_outside_tail
(a: V)
(l: List V)
(h: a ∉ l)
:
a ∉ l.tail
:= by
have h1: List.Sublist l.tail l:= by
  exact List.tail_sublist l
by_contra cont
have h3: a∈ l:= by exact List.mem_of_mem_tail cont
exact h h3

lemma Fb_disj_to_tail_disj
(Fb: Set V)
{a b c d:V}
(P: Walk G a b)
(Q: Walk G c d)
(QIsPath: Q.IsPath)
(hFb: {v:V|v∈ P.support}\ {c}⊆ Fb)
(disj: Disjoint {v:V|v∈ Q.support}  Fb)
:
P.support.Disjoint Q.support.tail
:= by
refine List.disjoint_left.mpr ?_
intro v hv
by_cases h: v=c
rw[h]
exact Walk_start_not_in_tail  Q QIsPath
simp at h
have h1: v∈ Fb:= by
  apply hFb
  simp
  constructor
  exact hv
  exact h
have h3:v∉ Q.support:= by
  apply disjoint_elim2 disj
  exact h1
exact outside_list_imp_outside_tail v Q.support h3



lemma Cut_Dense_path_avoiding_connecting_long
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
(Fb: Set V)
(FbSmall: 8*p*(Fb∩ H.verts).toFinset.card ≤ H.verts.toFinset.card)
(hu: u ∉ Fb)
(hv: v ∉ Fb)
(uvdiff: u ≠ v)
(d: ℕ)
--(hd: p*d < H.verts.toFinset.card)
(hd: 8*p*(d+1) < H.verts.toFinset.card)
:
∃ (P: SubgraphPath H u v), P.Wa.length≥ d ∧ (Disjoint {v:V| v∈ P.Wa.support}  Fb)
:= by

have hd':  8*p*d < H.verts.toFinset.card:=by
  calc
    8*p*d≤ 8*p*(d+1):= by
      gcongr
      exact Nat.le_add_right d 1
    _<H.verts.toFinset.card:= by exact hd

let Fb2:Set V:= Fb ∪ {v}

have hu2: u ∉ Fb2:= by
  dsimp [Fb2]
  simp
  constructor
  exact uvdiff
  exact hu
have Fb2Small: 2*(4*p*(Fb2∩ H.verts).toFinset.card )≤ 2*(H.verts.toFinset.card):= by
  dsimp[Fb2]
  calc
    2*(4*p*((Fb ∪ {v})∩ H.verts).toFinset.card)
    =8*p*((Fb ∪ {v})∩ H.verts).toFinset.card:= by ring_nf
    _=8*p*((Fb∩ H.verts).toFinset∪  ({v}∩ H.verts).toFinset).card:=by
      congr
      simp only [ Set.toFinset_inter]
      rw [@Set.toFinset_union]
      exact union_inter_distrib_right Fb.toFinset ({v}) H.verts.toFinset
    _≤ 8*p*((Fb∩ H.verts).toFinset.card+  ({v}∩ H.verts).toFinset.card):= by
      gcongr
      simp
      apply card_union_le --(Fb ∩ H.verts).toFinset ({v} ∩ H.verts).toFinset
    _=8*p*(Fb∩ H.verts).toFinset.card+ 8*p*({v}∩ H.verts).toFinset.card:= by
      ring_nf
    _≤  H.verts.toFinset.card+8*p*1:= by
      gcongr
      refine card_le_one_iff_subset_singleton.mpr ?h₂.bc.a
      use v
      simp
      right
      exact v_in_H
    _≤ H.verts.toFinset.card+H.verts.toFinset.card:= by
      gcongr
      calc
        H.verts.toFinset.card≥ 8 * p * (d+1):=by
          exact Nat.le_of_succ_le hd
        _≥ 8 * p * (1):= by
          gcongr
          simp
        _=_:= by
          ring_nf
    _= 2*H.verts.toFinset.card:=by ring_nf
have Fb2Small: 4*p*(Fb2∩ H.verts).toFinset.card ≤ H.verts.toFinset.card:= by
  apply Nat.le_of_mul_le_mul_left
  exact Fb2Small
  exact Nat.zero_lt_two

have ex: ∃ (v2: V), ∃ (P: SubgraphPath H u v2), P.Wa.length+1= d+1∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb2)∧ (v2∈ H.verts):= by
  apply Cut_dense_long_path_avoiding H H_cut_dense u u_in_H d hd' Fb2 hu2 _
  repeat assumption
  simp
  simp at Fb2Small
  exact Fb2Small

rcases ex with ⟨v2, hv2⟩
rcases hv2 with ⟨P, ⟨ hP1, hP2, hP3⟩ ⟩

let Fb3:Set V:= Fb ∪ {v:V|v∈ P.Wa.support}\ {v2}

have v2_Fb2: v2∉ Fb2:= by
  simp at hP2
  have h1: v2∈ {a: V|a∈ P.Wa.support}:= by
    simp
  apply disjoint_elim hP2
  exact h1

have v2_Fb: v2∉ Fb:= by
  dsimp [Fb2] at v2_Fb2
  have h1: Fb⊆ Fb2:= by
    dsimp [Fb2]
    exact Set.subset_union_left Fb {v}
  exact fun a ↦ v2_Fb2 (h1 a)


have Fb3Small: 2*(4*p*(Fb3∩ H.verts).toFinset.card )≤ 2*(H.verts.toFinset.card):= by
  dsimp[Fb3]
  calc
    2*(4*p*((Fb ∪ {v:V|v∈ P.Wa.support}\ {v2})∩ H.verts).toFinset.card)
    =8*p*((Fb ∪ {v:V|v∈ P.Wa.support}\ {v2})∩ H.verts).toFinset.card:= by ring_nf
    _=8*p*((Fb∩ H.verts).toFinset∪  (( {v:V|v∈ P.Wa.support}\ {v2})∩ H.verts).toFinset).card:=by
      congr
      simp only [ Set.toFinset_inter]
      rw [@Set.toFinset_union]
      exact union_inter_distrib_right Fb.toFinset ( {v:V|v∈ P.Wa.support}\ {v2}).toFinset H.verts.toFinset
    _≤ 8*p*((Fb∩ H.verts).toFinset.card+  (( {v:V|v∈ P.Wa.support}\ {v2})∩ H.verts).toFinset.card):= by
      gcongr
      simp
      apply card_union_le --(Fb ∩ H.verts).toFinset ({v} ∩ H.verts).toFinset
    _=8*p*(Fb∩ H.verts).toFinset.card+ 8*p*(( {v:V|v∈ P.Wa.support}\ {v2})∩ H.verts).toFinset.card:= by
      ring_nf
    _≤  H.verts.toFinset.card+8*p*(d+1):= by
      gcongr
      calc
        ({v | v ∈ P.Wa.support} \ {v2} ∩ H.verts).toFinset.card
        ≤ {v | v ∈ P.Wa.support}.toFinset.card:= by
          gcongr
          intro v hv
          simp
          simp at hv
          aesop
        _≤ P.Wa.support.toFinset.card:= by
          gcongr
          intro v hv
          simp
          simp at hv
          aesop
        _≤ P.Wa.support.length:= by
          --simp
          exact List.toFinset_card_le P.Wa.support
        _=P.Wa.length+1:=by
          apply Walk.length_support
        _=d+1:= by

          exact hP1


    _≤ H.verts.toFinset.card+H.verts.toFinset.card:= by
      gcongr

    _= 2*H.verts.toFinset.card:=by ring_nf



have Fb3Small: 4*p*(Fb3∩ H.verts).toFinset.card ≤ H.verts.toFinset.card:= by
  apply Nat.le_of_mul_le_mul_left
  exact Fb3Small
  exact Nat.zero_lt_two




have hv': v ∉ Fb3:= by
  dsimp [Fb3]
  --dsimp [Fb2]
  simp
  constructor
  exact hv
  have h1: v ∉  {a: V|a∈ P.Wa.support}:= by
    simp at hP2
    have hv3:v∈ Fb2:= by
      dsimp[Fb2]
      simp
    apply disjoint_elim2 hP2
    exact hv3
  simp at h1
  intro h
  exfalso
  exact h1 h

have hv2: v2 ∉ Fb3:= by
  dsimp [Fb3]
  simp
  exact v2_Fb

have ex2: ∃ (Q: SubgraphPath H v2 v), Q.Wa.length≤ 40*p∧ (Disjoint (Q.Wa.support.toFinset.toSet)  Fb3):= by
  apply Cut_Dense_path_avoiding H H_cut_dense v2 v _ _ Fb3
  repeat assumption
  simp
  simp at Fb3Small
  exact Fb3Small
  repeat assumption

rcases ex2 with ⟨Q, hQ1, hQ2⟩

let W12: Walk G u v:=P.Wa.append Q.Wa

have   W12_Is_Path: W12.IsPath:= by
  dsimp[W12]
  refine append_paths u v2 v P.Wa Q.Wa ?Ppath ?Qpath ?disj
  exact P.Wa_Is_Path
  exact Q.Wa_Is_Path
  apply Fb_disj_to_tail_disj Fb3 P.Wa Q.Wa--Fb2 u v2 v P.Wa Q.Wa Q.Wa_Is_Path hP2 hQ2
  exact Q.Wa_Is_Path
  dsimp[Fb3]
  simp
  simp at hQ2
  exact hQ2



have   Wa_In_H: W12.toSubgraph≤ H:= by
  dsimp[W12]
  simp
  constructor
  exact P.Wa_In_H
  exact Q.Wa_In_H


let R: SubgraphPath H u v:=⟨W12, W12_Is_Path, Wa_In_H⟩

use R
constructor
calc
  R.Wa.length
  =W12.length:= by dsimp[R];
  _=(P.Wa.length+Q.Wa.length):= by
    dsimp[W12]
    exact Walk.length_append P.Wa Q.Wa
  _≥ (P.Wa.length+0):= by
    gcongr
    simp
  _= P.Wa.length:= by ring_nf
  _= d:= by exact Nat.succ_inj'.mp hP1



dsimp[R]
dsimp[W12]
simp

have h8: {v_1 | v_1 ∈ P.Wa.support ∨ v_1 ∈ Q.Wa.support}={v:V|v∈ P.Wa.support} ∪ {v:V|v∈ Q.Wa.support}:= by
  ext v
  simp
rw[h8]

have ha: Disjoint {v:V|v∈ P.Wa.support} Fb:= by
  have h4: Fb⊆ Fb2:= by
    dsimp[Fb2]
    simp
  simp at hP2
  apply Set.disjoint_of_subset_right
  exact h4
  exact hP2


have hb: Disjoint {v:V|v∈ Q.Wa.support} Fb:= by
  have h4: Fb⊆ Fb3:= by
    dsimp[Fb3]
    simp
  simp at hQ2
  apply Set.disjoint_of_subset_right
  exact h4
  exact hQ2

exact Disjoint.union_left ha hb



/-
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
(Fb: Set V)
(FbSmall: 4*p*(Fb∩ H.verts).toFinset.card ≤ H.verts.toFinset.card)
(hu: u ∉ Fb)
(hv: v ∉ Fb)
-/

lemma Cut_Dense_path_avoiding_connecting_long_2
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u v: V)
(v_in_H: v ∈ H.verts)
(u_in_H: u ∈ H.verts)
(Fb: Set V)
(FbSmall: 8*p*(Fb∩ H.verts).toFinset.card ≤ H.verts.toFinset.card)
(hu: u ∉ Fb)
(hv: v ∉ Fb)
(uvdiff: u ≠ v)
--(d: ℕ)
--(hd: p*d < H.verts.toFinset.card)
--(hd: 8*p*(d+1) < H.verts.toFinset.card)
(Horder: H.verts.toFinset.card≥ m)
(mggp:  m≥ 18*p)
:
∃ (P: SubgraphPath H u v), P.Wa.length≥ (m/(40*p)) ∧ (Disjoint {v:V| v∈ P.Wa.support}  Fb)
:= by

let d:ℕ := m/(40*p)

have hd: d= m/(40*p):= by
  exact rfl
rw[hd.symm]
apply Cut_Dense_path_avoiding_connecting_long
exact pPositive

repeat assumption
rw[hd]
calc
  8 * p * (m / (40 * p) + 1)
  = 8*p*(m/(40*p))+ 8*p:= by
      ring_nf
  _= (2*8*p*(m/(40*p)))/2+ 8*p:= by
    congr
    refine (Nat.div_eq_of_eq_mul_right ?_ ?_).symm
    exact Nat.zero_lt_two
    ring_nf
  _≤ m/2+8*p:= by
    gcongr
    calc
      2 * 8 * p * (m / (40 * p))
      ≤ 2 * 8 * p * (m / (16 * p)):= by
        gcongr
        exact Nat.le_of_ble_eq_true rfl
      _=(16 * p) * (m / (16 * p)):=by
        ring_nf
      _≤ m:= by
        exact Nat.mul_div_le m (16 * p)
  _<m:= by
    calc
      m / 2 + 8 * p
      < m/2+m/2:= by
        gcongr
        refine (Nat.le_div_iff_mul_le ?bc.k0).mpr ?bc.a
        simp
        simp
        ring_nf
        rw[mul_comm]
        calc
          m≥ 18*p:= by exact mggp
          _= 2*p+16*p:= by ring_nf
          _≥ 2*1 + 16 * p:=by
            gcongr
            exact pPositive
          _=_:= by ring_nf

      _=2*(m/2):= by
        ring_nf
      _≤ 2*m/2:= by
        exact Nat.mul_div_le_mul_div_assoc 2 m 2

      _=1*m:= by
        refine Nat.div_eq_of_eq_mul_right ?H1 ?H2
        simp
        ring_nf
      _=m:=by ring_nf
    --m / 2 + 8 * p < m
  _≤ H.verts.toFinset.card:= by
    exact Horder
