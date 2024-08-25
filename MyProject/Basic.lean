--import MyProject

import Mathlib.combinatorics.pigeonhole
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


--set_option maxHeartbeats 400000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable {p m κ pr : ℕ}



---Numbers-----------------------------------
lemma plus_one_leq_than_double
{a:ℕ}
(aPositive: a>0)
: a+1 ≤  a*2 := by
calc
a+1 ≤  a+a:= by
  gcongr
  exact aPositive
_=a*2:= by
  ring_nf



lemma div_assoc_3
{b c : ℕ}
(cPos : c > 0)
:c * (b / c) + c ≥ b:=by
--have h1: c*(b/c)≤b:= by
--  exact Nat.mul_div_le b c
have h2: c*(Nat.succ (b/c))>b:= by
  exact Nat.lt_mul_div_succ b cPos
--have h3: c*(b/c)+c>b:= by
--  calc
--    c*(b/c)+c=c*(b/c+1):= by
--      ring_nf
--    _=c*(Nat.succ (b/c)):= by
--      congr
--    _> b:= by
--     exact h2
exact Nat.le_of_succ_le h2




lemma div_assoc_le2
{a b c:ℕ }
(cPos: c>0)
: a*b/c≤  a*(b/c)+a:= by
calc
a*(b/c)+a=a*(b/c+1):= by
  exact rfl
_≥ a*b/c:=by
  refine Nat.div_le_of_le_mul ?_
  calc
    c * (a * (b / c + 1))
    _=a*(c*(b/c+1)):=by
      ring_nf
    _≥ a*b:=by
      gcongr
      calc
        c * (b / c + 1)
        =c * (b / c) + c:=by
          ring_nf
        _≥ b:=by
         exact div_assoc_3 cPos


lemma div_assoc_le1
{a b c:ℕ }
(cPos: c>0)
(bgec: b≥ c)
: a*b/c≤  2*a*(b/c):= by
calc
a*b/c≤a*(b/c)+a:= by
  exact div_assoc_le2 cPos
_=a*(b/c+1):=by
  ring_nf
_≤a*(b/c+b/c):=by
  gcongr
  refine (Nat.one_le_div_iff cPos).mpr ?bc.bc.a
  exact bgec
_= 2*a*(b/c):=by
  ring_nf




lemma nat_rat_nat (a: ℕ): Nat.floor (a:ℚ)=a:= by
exact rfl

lemma nat_rat_mul (a b c: ℕ)(heq: c=a*b): (c:ℚ)= (a:ℚ) * (b:ℚ ):= by
have h1:(((a*b):ℕ ):ℚ)=(a:ℚ) * (b:ℚ):= by exact Nat.cast_mul a b
calc
  (c:ℚ)= (((a*b):ℕ ):ℚ):=by exact congrArg Nat.cast heq
  _=(a:ℚ) * (b:ℚ):= by exact h1

lemma nat_rat_add (a b c: ℕ)(heq: c=a+b): (c:ℚ)= (a:ℚ) + (b:ℚ ):= by
have h1:(((a+b):ℕ ):ℚ)=(a:ℚ) + (b:ℚ):= by exact Nat.cast_add a b
calc
  (c:ℚ)= (((a+b):ℕ ):ℚ):=by exact congrArg Nat.cast heq
  _=(a:ℚ) + (b:ℚ):= by exact h1

lemma nat_le_rat (a b: ℕ) (hle: a≤ b):(a:ℚ )≤ (b:ℚ) := by
exact Nat.cast_le.mpr hle

lemma nat_eq_rat (a b: ℕ) (hle: a= b):(a:ℚ )= (b:ℚ) := by
exact congrArg Nat.cast hle

lemma nat_divisor_div (a b:ℕ)(ha:0<a): ((b*a)/a=b):= by
apply Nat.mul_div_cancel
exact ha



lemma nat_self_div (a:ℕ)(ha:0<a): (a/a=1):= by
have h0: a≤ a:= by exact Nat.le_refl a
have h1:a/a=(a-a)/a+1:= by exact Nat.div_eq_sub_div ha h0
exact Nat.div_self ha

lemma nat_div_ge (a b e v:ℕ)
(hineq:   v * b≤ a * e)
(hbpos: 0<b):
(a / b+1) * e   ≥ v:= by
have xa:v≤ (a*e)/b ↔ v * b≤ a * e:= by exact Nat.le_div_iff_mul_le'  hbpos
have _:v≤ (a*e)/b:= by apply xa.2; exact hineq
let a':ℚ:= a
let b':ℚ:= b
let e':ℚ:= e
let v':ℚ:= v
have ha'':a'=(a:ℚ):= by exact rfl
have hb''':b'=(b:ℚ):= by exact rfl

have hb':b'>0:= by exact Nat.cast_pos.mpr hbpos
have hineq':   v' * b'≤ a' * e':= by calc
  v' * b'=((v * b):ℕ):= by exact (Nat.cast_mul v b).symm
  _≤ ((a * e):ℕ):= by exact Nat.cast_le.mpr hineq
  _=a' * e':= by exact Nat.cast_mul a e
have h1:v'≤ (a'*e')/b':= by exact (le_div_iff hb').mpr hineq'
have h2: (e'*a')/b'=e'*(a'/b'):= by exact mul_div_assoc  e' a' b'
have h3: (a'/b')≤ Nat.ceil (a'/b'):= by exact Nat.le_ceil (a' / b')
have h4: Nat.ceil (a'/b')≤ Nat.floor (a'/b')+1:= by exact Nat.ceil_le_floor_add_one (a' / b')
have h5: Nat.floor ((a:ℚ) /(b:ℚ))=a/b:=by exact Nat.floor_div_eq_div a b
--have h7: (Nat.ceil (a'/b'):ℚ)≤ ((Nat.floor (a'/b')+1):ℚ):= by  apply Nat.cast_le.mpr
have h7: (Nat.ceil (a'/b'):ℚ)≤ ((Nat.floor (a'/b')+1:ℕ ):ℚ):= by exact  nat_le_rat ⌈a' / b'⌉₊ (⌊a' / b'⌋₊ + 1) h4
have h8: (Nat.floor (a' / b') + 1)=Nat.floor (a' / b') + 1:= by exact rfl

let n:ℕ := ((Nat.floor (a' / b') + 1)) * e
have hn: n= ((Nat.floor (a' / b') + 1)) * e:= by exact rfl

have h6: (n:ℚ )≥ (v:ℚ):= by calc
  (n:ℚ) =  (((Nat.floor (a' / b') + 1) * e:ℕ ):ℚ):= by exact nat_eq_rat n ((Nat.floor (a' / b') + 1) * e) hn
  _=(((Nat.floor (a' / b') + 1:ℕ ) * (e:ℕ )):ℚ):= by exact nat_rat_mul ((Nat.floor (a' / b') + 1)) e ((Nat.floor (a' / b') + 1) * e) hn
  _≥ (Nat.ceil (a'/b'))*e:= by gcongr; sorry
  _=  (Nat.ceil (a'/b'))*e':= by exact rfl
  _≥ (a'/b')*e':= by gcongr; sorry
  _= e'*(a'/b'):= by exact Rat.mul_comm (a' / b') e'
  _= (e'*a')/b':= by exact id h2.symm
  _= (a'*e')/b':= by   rw [Rat.mul_comm]
  _≥ v':= by exact h1
  _=(v:ℚ):= by exact rfl

have h8: Nat.floor (n:ℚ )≥ Nat.floor (v:ℚ):=by gcongr
have h9: Nat.floor (n: ℚ)=n:= by exact nat_rat_nat n
have h10: Nat.floor (v:ℚ)= v:= by exact nat_rat_nat v
have h11:n≥ v:=by calc
  n=Nat.floor (n: ℚ):= by exact rfl
  _≥ Nat.floor (v:ℚ):= by exact h8
  _=v:= by exact h10
--have h12: a/b=⌊ (a:ℚ )/(b:ℚ) ⌋ := by exact?
rw [h5.symm, ha''.symm, hb'''.symm, hn.symm]
exact h11

lemma  Nat_div_ge_simpler (a b v:ℕ)
(hineq:   v * b≤ a )
(hbpos: 0<b):
a / b+1   ≥ v:= by
have h1: v * b≤ a *1:=by calc
  v * b≤ a:= by exact hineq
  _=a*1:= by
    exact (Nat.mul_one a).symm
have h2: (a/b+1) *1≥ v:= by
  exact nat_div_ge a b 1 v h1 hbpos
calc
  a / b+1=(a/b+1)*1:= by ring_nf
  _≥ v:= by exact h2


lemma times_div_ge_sub
(a b: ℕ )
(hbpos: b>0)
: b*(a/b)≥ a-b:= by
refine Nat.sub_le_of_le_add ?h
exact div_assoc_3 hbpos

lemma twice_minus_once
(m:ℕ )
: 2*m-m=m:= by
calc
2*m-m=2*m-1*m:= by
  congr
  exact (Nat.one_mul m).symm
_=(2-1)*m:= by
  exact (Nat.mul_sub_right_distrib 2 1 m).symm
_=1*m:= by
  exact rfl
_=m:= by
  exact Nat.one_mul m


lemma twice_times_fraction_ge (m b:ℕ)
(hb:b>0)
(hm: m≥ 2*b)
: 2*b*(m/b)≥ m:= by
calc
2*b*(m/b)=2*(b*(m/b)):= by
  ring_nf
_≥ 2*(m-b):=by
  gcongr
  apply times_div_ge_sub
  exact hb
_= 2*m-2*b:=by
  exact Nat.mul_sub_left_distrib 2 m b
_≥ 2*m-m:= by
  gcongr
_=m:= by
  exact twice_minus_once m


lemma four_times_half_ge (m:ℕ)
(hm: m≥ 4)
: 4*(m/2)≥ m:= by
calc
4*(m/2)=2*(2*(m/2)):= by
  ring_nf
_≥ 2*(m-2):=by
  gcongr
  apply times_div_ge_sub
  exact Nat.zero_lt_two
_= 2*m-2*2:=by
  exact Nat.mul_sub_left_distrib 2 m 2
_= 2*m-4:=by
  ring_nf
_≥ 2*m-m:= by
  gcongr
_=m:= by
  exact twice_minus_once m


lemma minus_half_halves_ge
(a:ℕ )
: a-a/2≥ a/2:=by
refine (Nat.le_sub_iff_add_le' ?h).mpr ?_
exact Nat.div_le_self a 2
calc
a / 2 + a / 2=2*(a/2):=by
  ring_nf
_≤ a:= by
  exact Nat.mul_div_le a 2


lemma two_quarters_less_than_half
(a:ℕ )
: a/4+a/4≤ a/2:= by
calc
    a/4+a/4=2*(a/4):= by
      ring_nf
    _≤a/2:=by
      refine (Nat.le_div_iff_mul_le' ?hb).mpr ?_
      exact Nat.zero_lt_two
      calc
      2 * (a / 4) * 2
      =4*(a/4):=by ring_nf
      _≤ a:=by exact Nat.mul_div_le a 4

lemma minus_two_quarters_halves
(a b c :ℕ )
(hb: b≤ a/4)
(hc: c≤ a/4)
: a - b - c ≥ a/2:= by
calc
a - b - c ≥ a - a/4 - c:= by
  gcongr
_≥ a - a/4 - a/4:= by
  gcongr
_= a-(a/4+a/4):=by
  exact Nat.sub_sub a (a / 4) (a / 4)
_≥ a-(a/2):= by
  gcongr
  exact two_quarters_less_than_half a
_≥ a/2:= by
  exact minus_half_halves_ge a


/-lemma n_le_n_factorial
(n:ℕ)
(nPositive: n>0)
: n≤ n!:= by
sorry-/

--Basic Set Theory----------------------------------
lemma intersection_contained_in_union
{X Y : Set V}
: X ∩ Y ⊆ X ∪ Y:= by
calc
X ∩ Y ⊆ X:= by
  exact Set.inter_subset_left X Y
_⊆ X ∪ Y:= by
  exact Set.subset_union_left X Y

--hello
lemma subset_implies_card_sum_Set (S T: Set V)
(hContained: S⊆T)
:  (T \ S).toFinset.card +S.toFinset.card = T.toFinset.card:= by
have h1: S.toFinset⊆ T.toFinset:= by
  exact Set.toFinset_subset_toFinset.mpr hContained
have h2: (T\S).toFinset= T.toFinset \ S.toFinset:= by
  exact Set.toFinset_diff T S
rw [h2]
exact card_sdiff_add_card_eq_card h1


lemma Set_card_sum_intersection_difference (S T: Set V)
:  (T∩ S).toFinset.card+(T \ S).toFinset.card  = T.toFinset.card:= by
have h1: (T∩ S).toFinset=T.toFinset∩ S.toFinset:= by
  exact Set.toFinset_inter T S
have h2: (T\S).toFinset= T.toFinset \ S.toFinset:= by
  exact Set.toFinset_diff T S
rw [h2, h1]
exact card_inter_add_card_sdiff T.toFinset S.toFinset


lemma card_union_3
(S T U: Finset V)
:  (S ∪ T ∪ U).card≤ S.card + T.card + U.card := by
calc
(S ∪ T ∪ U).card≤ (S ∪ T).card + U.card:= by
  exact card_union_le (S ∪ T) U
_≤ S.card + T.card + U.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_4
(S T U W: Finset V)
:  (S ∪ T ∪ U ∪ W).card≤ S.card + T.card + U.card + W.card := by
calc
(S ∪ T ∪ U ∪ W).card≤ (S ∪ T).card + U.card + W.card:= by
  exact card_union_3 (S ∪ T) U W
_≤ S.card + T.card + U.card + W.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_5
(S T U W X: Finset V)
:  (S ∪ T ∪ U ∪ W ∪ X).card≤ S.card + T.card + U.card + W.card + X.card := by
calc
(S ∪ T ∪ U ∪ W ∪ X).card≤ (S ∪ T).card + U.card + W.card + X.card:= by
  exact card_union_4  (S ∪ T)  U W X
_≤ S.card + T.card + U.card + W.card + X.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_6
(S T U W X Y: Finset V)
:  (S ∪ T ∪ U ∪ W ∪ X ∪ Y).card≤ S.card + T.card + U.card + W.card + X.card + Y.card := by
calc
(S ∪ T ∪ U ∪ W ∪ X ∪ Y).card≤ (S ∪ T).card + U.card + W.card + X.card + Y.card:= by
  exact card_union_5  (S ∪ T)  U W X Y
_≤ S.card + T.card + U.card + W.card + X.card + Y.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_7
(S T U W X Y Z: Finset V)
:  (S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z).card≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card := by
calc
(S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z).card≤ (S ∪ T).card + U.card + W.card + X.card + Y.card + Z.card:= by
  exact card_union_6  (S ∪ T)  U W X Y Z
_≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_8
(S T U W X Y Z A: Finset V)
:  (S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z ∪ A).card≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card + A.card := by
calc
(S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z ∪ A).card≤ (S ∪ T).card + U.card + W.card + X.card + Y.card + Z.card + A.card:= by
  exact card_union_7  (S ∪ T)  U W X Y Z A
_≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card + A.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_9
(S T U W X Y Z A B: Finset V)
:  (S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z ∪ A ∪ B).card≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card + A.card + B.card := by
calc
(S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z ∪ A ∪ B).card≤ (S ∪ T).card + U.card + W.card + X.card + Y.card + Z.card + A.card + B.card:= by
  exact card_union_8  (S ∪ T)  U W X Y Z A B
_≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card + A.card + B.card:= by
  gcongr
  exact card_union_le S T

lemma card_union_10
(S T U W X Y Z A B C: Finset V)
:  (S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z ∪ A ∪ B ∪ C).card≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card + A.card + B.card + C.card := by
calc
(S ∪ T ∪ U ∪ W ∪ X ∪ Y ∪ Z ∪ A ∪ B ∪ C).card≤ (S ∪ T).card + U.card + W.card + X.card + Y.card + Z.card + A.card + B.card + C.card:= by
  exact card_union_9  (S ∪ T)  U W X Y Z A B C
_≤ S.card + T.card + U.card + W.card + X.card + Y.card + Z.card + A.card + B.card + C.card:= by
  gcongr
  exact card_union_le S T


lemma mem_of_union_elim_left
{X: Type u}
(S T: Finset X)
(a: X)
(h: a ∈ S ∪ T)
(ha: ¬(a∈ S))
:
a ∈ T:= by
have h1: a∈ S ∨ a∈ T:=by
  exact mem_union.mp h
exact Or.elim h1 (fun h2 => False.elim (ha h2)) (fun h2 => h2)

lemma mem_of_union_elim_right
{X: Type u}
(S T: Finset X)
(a: X)
(h: a ∈ T ∪ S)
(ha: ¬(a∈ S))
:
a ∈ T:= by
have h1: a∈ T ∨ a∈ S:=by
  exact mem_union.mp h
have h3: a∈ S ∨ a∈ T:=by
  exact Or.symm h1
exact Or.elim h3 (fun h2 => False.elim (ha h2)) (fun h2 => h2)



/-
lemma mem_of_union_elim_subgraphs
(S T: Finset (Subgraph G))
(a: Subgraph G)
(h: a ∈ S ∪ T)
(ha: ¬(a∈ S))
:a∈ T:=by
exact mem_of_union_elim S T a h ha
-/

--------------Basic graphs-----------------
lemma subgraph_implies_edgesets_subsets
{H K: Subgraph G}
(hHK: H≤ K)
: H.edgeSet⊆ K.edgeSet:= by
refine LE.le.subset ?_
exact Subgraph.edgeSet_mono hHK


lemma subgraph_implies_adjacency_inherited
{H K: Subgraph G}
(hHK: H≤ K)
{v w: V}
(hAdj: H.Adj v w)
: K.Adj v w:= by
refine Subgraph.mem_edgeSet.mp ?_
have h1: s(v,w)∈ H.edgeSet:= by
  exact hAdj
have h2:H.edgeSet⊆ K.edgeSet:= by
  exact subgraph_implies_edgesets_subsets hHK
exact h2 h1


-------subgraph----sup etc
lemma union_of_twograph_families
{A B C: Finset (Subgraph G)}
(hC: C=A∪ B)
: (sSup A: Subgraph G) ⊔ (sSup B: Subgraph G)=(sSup C: Subgraph G):=by
rw[hC]
simp
exact sSup_union.symm

lemma induced_subgraph_subgraph
{S: Set V}
{H: Subgraph G}
(hS: S ⊆ H.verts)
: (H.induce S) ≤ H:= by
have h1: H= H.induce H.verts:= by exact Subgraph.induce_self_verts.symm
nth_rw 2 [h1]
exact Subgraph.induce_mono_right hS

lemma three_graph_sup
(a b c: Subgraph G)
:
c ⊔ a ⊔ b ⊔ a ⊔ b =  c ⊔ a ⊔ b:=by
repeat rw [sup_assoc]
repeat rw[sup_comm c _]
repeat rw[← sup_assoc]
rw[sup_assoc (a⊔ b) _ _]
rw[sup_idem]

lemma union_three_set_idem
(a b c: Set V)
: (a∪ b)∪ (a∪ c)= a∪ b∪ c:= by
  repeat rw [←Set.union_assoc]
  rw[Set.union_comm _ a]
  repeat rw [←Set.union_assoc]
  congr
  exact Set.union_eq_self_of_subset_left fun ⦃a_1⦄ a ↦ a


lemma bigunion_comparision_one_direction
(F: Finset (Subgraph G))
:
a ∈ (⋃ H ∈ F, H.verts).toFinset → a ∈ F.biUnion fun x ↦ x.verts.toFinset
:= by

intro h
refine mem_biUnion.mpr ?_

have h0: a ∈ (⋃ H ∈ F, H.verts):= by
  exact Set.mem_toFinset.mp h
have h1: ∃ H ∈ F, a ∈ H.verts:=by

  have h3:_:= by apply Set.mem_iUnion.1 h0
  rcases h3 with ⟨ x, y⟩
  have h4:_:= by apply Set.mem_iUnion.1 y
  rcases h4 with ⟨ z, h6⟩
  use x



rcases h1 with ⟨ a1, ha1⟩
have h12: a ∈ a1.verts:= by
  exact ha1.2
have h2:a ∈ a1.verts.toFinset:= by
  exact Set.mem_toFinset.mpr h12

use a1
exact ⟨ha1.1, h2⟩




lemma bigunion_equality
(F: Finset (Subgraph G))
:
(⋃ H ∈ F, H.verts).toFinset=(Finset.biUnion F (fun x=>x.verts.toFinset))
--(⋃ H ∈ F, H.verts).toFinset.card≤∑ H∈ F, H.verts.toFinset.card
:= by

ext a

constructor
exact fun a_1 ↦ bigunion_comparision_one_direction F a_1


intro b
refine Set.mem_toFinset.mpr ?_
refine Set.mem_iUnion₂.mpr ?_

have h1: ∃ H ∈ F, a ∈ H.verts.toFinset:=by
  exact mem_biUnion.mp b

rcases h1 with ⟨ a1, ha1⟩
have h11:_:= by
  exact ha1.1
have h12:_:= by
  exact ha1.2
use a1
simp
have h12: a ∈ a1.verts := by exact Set.mem_toFinset.mp h12
exact ⟨h11, h12⟩


lemma bigunion_bound
(F: Finset (Subgraph G))
:
(⋃ H ∈ F, H.verts).toFinset.card ≤∑ H∈ F, H.verts.toFinset.card
:= by
calc
(⋃ H ∈ F, H.verts).toFinset.card
=(Finset.biUnion F (fun x=>x.verts.toFinset)).card:= by
  congr
  exact bigunion_equality F
_≤∑ H∈ F, H.verts.toFinset.card:= by
  exact card_biUnion_le


lemma biunion_max_bound
(F: Finset (Subgraph G))
(M:ℕ)
(hM: ∀ H∈ F, H.verts.toFinset.card ≤ M)
:
(⋃ H ∈ F, H.verts).toFinset.card≤ F.card*M
:= by
calc
(⋃ H ∈ F, H.verts).toFinset.card
≤∑ H∈ F, H.verts.toFinset.card:= by
  exact bigunion_bound F
_≤∑ H∈ F, M:= by
  apply sum_le_sum
  intros a b
  exact hM a b
_=_:= by
  exact sum_const_nat fun x ↦ congrFun rfl

lemma biunion_max_bound2
(M:ℕ)
(t:ℕ)
(F: Finset (Subgraph G))
(hF:F.card≤ t)
(hM: ∀ H∈ F, H.verts.toFinset.card ≤ M)
:
(⋃ H ∈ F, H.verts).toFinset.card≤ t*M
:= by
calc
(⋃ H ∈ F, H.verts).toFinset.card≤F.card*M:= by
  exact biunion_max_bound F M hM
_≤t*M:= by
  gcongr


lemma Sym2_to_tuple (e: Sym2 V):
 ∃ (a b :V), e=s(a,b):= by
let a:V:= (Quot.out e).1
have hea: a∈ e:= by exact Sym2.out_fst_mem e
have h2: ∃ (b : V), e = s(a, b):= by
  exact hea
rcases h2 with ⟨b, h2⟩
exact ⟨a, b, h2⟩




lemma lower_bound_vertices_by_edges
(H: Subgraph G):
(H.verts.toFinset.card).choose 2≥H.edgeSet.toFinset.card
:= by
let U:= { x // x ∈ H.verts }
let K:SimpleGraph U:=H.coe
have h1: (Fintype.card U).choose 2≥  K.edgeFinset.card:= by
  exact card_edgeFinset_le_card_choose_two
have h2: Fintype.card U= (H.verts.toFinset.card):= by
  exact (Set.toFinset_card H.verts).symm
have h3: K.edgeFinset.card= H.edgeSet.toFinset.card:= by
  --simp
  dsimp [K]
  dsimp[U]

  unfold edgeFinset


  refine (card_eq_of_equiv ?i).symm
  simp
  symm
  refine Set.BijOn.equiv ?i.f ?i.h
  let f: { x // x ∈ H.verts }→ V:= fun x=> x.1
  let g: Sym2 { x // x ∈ H.verts } → Sym2 V:= fun x=> Sym2.map f x
  exact g
  constructor
  intro x hx
  have h1: ∃ (a b: { x // x ∈ H.verts }), x=s(a,b):= by
    use (Quot.out x).1
    use (Quot.out x).2
    simp

  rcases h1 with ⟨a, b, h1⟩
  rw[h1]
  rw[h1] at hx
  simp at hx
  simp
  exact hx

  constructor
  intro x  hx y hy hxy
  have hxx: ∃ (a b: { x // x ∈ H.verts }), x=s(a,b):= by
    use (Quot.out x).1
    use (Quot.out x).2
    simp
  have hyy: ∃ (c d: { x // x ∈ H.verts }), y=s(c,d):= by
    use (Quot.out y).1
    use (Quot.out y).2
    simp
  rcases hxx with ⟨a, b, hab⟩
  rcases hyy with ⟨c, d, hcd⟩
  rw[hab, hcd]
  rw[hab, hcd] at hxy
  rw[hab] at hx
  rw[hcd] at hy
  simp at hx hy hxy
  simp
  rcases hxy with ⟨c1, c2⟩ | ⟨c1, c2⟩
  left
  constructor
  exact SetCoe.ext c1
  exact SetCoe.ext c2
  right
  constructor
  exact SetCoe.ext c1
  exact SetCoe.ext c2



  intro x hx
  have hxx: ∃ (a b: V), x=s(a,b):= by
    use (Quot.out x).1
    use (Quot.out x).2
    simp
  rcases hxx with ⟨a, b, hab⟩
  rw[hab]
  rw[hab] at hx
  simp at hx
  simp
  have ha: a∈ H.verts:= by
    exact H.edge_vert hx
  have hb: b∈ H.verts:= by
    exact H.edge_vert (id (Subgraph.adj_symm H hx))
  use s(⟨a, ha⟩, ⟨b, hb⟩)
  simp
  exact hx

--rw[h2, h3] at h1
rw[h3.symm]
rw[h2.symm]
exact h1


lemma square_ge_choose {n:ℕ }: n^2≥n.choose 2:= by
  have h1: n^2=n*n:= by ring_nf
  have h2: n.choose 2= n*(n-1)/2:= by
    exact Nat.choose_two_right n
  have h3: n*(n-1)/2 ≤ n*n:= by calc
    n*(n-1)/2 ≤ n*(n-1):= by exact Nat.div_le_self (n * (n - 1)) 2
    _≤  n*n:= by gcongr; exact Nat.sub_le n 1
  rw[h1, h2]
  exact h3

lemma lower_bound_vertices_by_edges_weaker
(H: Subgraph G):
(H.verts.toFinset.card)^2≥H.edgeSet.toFinset.card
:=by calc
  (H.verts.toFinset.card)^2≥ (H.verts.toFinset.card).choose 2:= by exact square_ge_choose
  _≥H.edgeSet.toFinset.card:= by exact lower_bound_vertices_by_edges H



lemma bernoulli_inequality
(n: ℕ )
:
2^n≥ n:=by
induction' n with n IH
simp

calc
2^(n+1)=2^n*2^1:= by exact rfl
_=2^n+2^n:= by ring_nf
_≥ n+1:=by
  gcongr
  exact Nat.one_le_two_pow
