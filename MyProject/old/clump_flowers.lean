import MyProject

import MyProject.clumpfamily_joining
 --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}


def flower_intersections
(G: SimpleGraph V)
(p m κ pr h γ: ℕ )
(K0: Clump G p m κ pr h)
(F: Finset (Clump G p m κ pr h))
:=∀ (K:Clump G p m κ pr h), (K∈ F)→ (γ*(BSet K0 ∩ BSet K).toFinset.card ≥  m)

@[ext] structure Clump_Flower  (G: SimpleGraph V) (p m κ pr h γ: ℕ ) where
  F: Finset (Clump G p m κ pr h)
  K0:  Clump G p m κ pr h
  hCenter_in_Fam: K0 ∈ F
  Large_Intersections:flower_intersections G p m κ pr h γ (K0) (F)

def flower_contained_in_Gr
(Gr: Subgraph G )
(F: Clump_Flower G p m κ pr h γ)
:=∀ (K:Clump G p m κ pr h), (K∈ F.F)→ (K.Gr≤ Gr)

def L_contains_clump_flower
--(KFam: Finset (Clump G p m κ pr h))
(p m κ pr h γ:ℕ )
(G: SimpleGraph V)
(L: Locally_Dense G p m h)
:=∃ (F: Clump_Flower G p m κ pr h γ), flower_contained_in_Gr L.Gr F

def L_no_clump_flowers
--(KFam: Finset (Clump G p m κ pr h))
(p m κ pr h γ:ℕ )
(G: SimpleGraph V)
(L: Locally_Dense G p m h)
:=∀  (F: Clump_Flower G p m κ pr h γ), ¬ flower_contained_in_Gr L.Gr F


def separated_list (p m κ pr h α : ℕ )

(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h)
:=∀(i j : ℕ ), (i<j)→ (j≤ Li.length)→ (α*(( BSet (List.getD Li i nan))∩( BSet (List.getD Li i nan))).toFinset.card≥ m)


def list_separated_up_to (p m κ pr h α : ℕ )
(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h)(t: ℕ )
:=∀(i j : ℕ ), (i<j)→ (i≤ t)→ (j≤ Li.length)→ (α*(( BSet (List.getD Li i nan))∩( BSet (List.getD Li i nan))).toFinset.card≥ m)




noncomputable def list_BSet --(p m κ pr h : ℕ )
(Li: List (Clump G p m κ pr h))
: Finset (Set V):= Finset.image BSet Li.toFinset

def list_union
(Li: List (Clump G p m κ pr h))
: Set V:= Set.sUnion (list_BSet Li)

--def list_union_from_i (p m κ pr h : ℕ )
--(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h) (i: ℕ )
--: Set V
--:=list_union  (Li.drop (i))

def list_union_dropping_first (p m κ pr h : ℕ )
(Li: List (Clump G p m κ pr h))
: Set V
:=list_union  (Li.drop (1))



def clump_list_dense_at_1 ( p m κ pr h α: ℕ )
(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h)
:=(α*(( BSet (List.headD Li nan))∩( list_union_dropping_first p m κ pr h  Li)).toFinset.card≥ m)

--def clump_list_dense_at_i ( p m κ pr h α i: ℕ )
--(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h)
--:=(α*(( BSet (List.getD Li i nan))∩( list_union_from_i p m κ pr h  Li nan i)).toFinset.card≥ m)

def clump_list_dense_up_to_n ( p m κ pr h α n: ℕ )
(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h)
:=∀ (i: ℕ ), (i< n)→ clump_list_dense_at_1 p m κ pr h α (Li.drop i) nan
--:=∀ (i: ℕ ), (i≤ n)→ clump_list_dense_at_i p m κ pr h α i Li nan


def clump_list_dense ( p m κ pr h α: ℕ )
(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h)
:=
∀ (i: ℕ ),  clump_list_dense_at_1 p m κ pr h α (Li.rotate i) nan


def family_contains_dense_list ( p m κ pr h α: ℕ )
(KFam: Finset (Clump G p m κ pr h))
(nan:  Clump G p m κ pr h)
:=
∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset⊆  KFam)∧
(Li.Nodup)∧
(clump_list_dense p m κ pr h α Li nan)


lemma Tail_toFinset_contained_in_list
(Li: List (Clump G p m κ pr h))
(n: ℕ )
:
(Li.drop (n)).toFinset⊆ Li.toFinset:=by
let Tail: List (Clump G p m κ pr h):= Li.drop (n)
let Head: List (Clump G p m κ pr h):= Li.take (n)
have happend_Head_Tail: Li= Head++Tail:= by
  exact (List.take_append_drop n Li).symm

calc
  Tail.toFinset⊆Head.toFinset∪ Tail.toFinset:=by
    exact subset_union_right Head.toFinset Tail.toFinset
  _=(Head++Tail).toFinset:= by
    dsimp [Tail]
    exact List.toFinset_append.symm
  _=Li.toFinset:= by
    congr
    exact id happend_Head_Tail.symm



lemma List_toFinset_rotation_invariant
(L: List (Clump G p m κ pr h))
(i: ℕ )
:
(L.rotate i).toFinset= L.toFinset:=by
apply List.toFinset_eq_iff_perm_dedup.2
refine List.Perm.dedup ?p
exact List.rotate_perm L i



lemma Order_family_induction_step
(n: ℕ )
(KFam: Finset (Clump G p m κ pr h))
(Li: List (Clump G p m κ pr h))
(nan: Clump G p m κ pr h)
(heqFam: Li.toFinset= KFam)
(hNoDup: Li.Nodup)
(hn: n< Li.length)
(dense_up_to_n:  clump_list_dense_up_to_n p m κ pr h α n Li nan)
(no_dense_sets: ¬ family_contains_dense_list p m κ pr h α KFam nan)
:
∃ (Li': List (Clump G p m κ pr h)),
(Li'.toFinset= KFam)∧
(Li'.Nodup)∧
(clump_list_dense_up_to_n p m κ pr h α (n+1) Li' nan)
:=by
let Tail: List (Clump G p m κ pr h):= Li.drop (n)
let Head: List (Clump G p m κ pr h):= Li.take (n)
have happend_Head_Tail: Li= Head++Tail:= by
  exact (List.take_append_drop n Li).symm
have hsublist: List.Sublist Tail  Li:= by
  exact List.drop_sublist n Li
have hsublistHead: List.Sublist Head  Li:= by
  exact List.take_sublist n Li
have Tail_in_KFam: Tail.toFinset⊆ KFam:= by
  calc
  Tail.toFinset⊆Li.toFinset:= by
    congr
    exact Tail_toFinset_contained_in_list Li n
  _= KFam:= by
    exact heqFam
have Tail_NoDup: Tail.Nodup:= by
  dsimp[Tail]
  exact List.Nodup.sublist hsublist hNoDup

have Tail_not_dense: ¬ clump_list_dense p m κ pr h α Tail nan:=by
  by_contra contr
  have dense_sets:family_contains_dense_list p m κ pr h α KFam nan:=by
    exact ⟨Tail, Tail_in_KFam, Tail_NoDup, contr⟩
  exact no_dense_sets dense_sets

dsimp [clump_list_dense] at Tail_not_dense
push_neg at Tail_not_dense
rcases Tail_not_dense with ⟨i, hi⟩

let Li':=Head++(Tail.rotate i)
use Li'
constructor
calc
  Li'.toFinset= (Head++(Tail.rotate i)).toFinset:= by
    dsimp[Li']
  _=(Head).toFinset∪ (Tail.rotate i).toFinset:=by
    simp
  _=(Head).toFinset∪ (Tail).toFinset:= by
    have h1: (Tail.rotate i).toFinset=(Tail).toFinset:=by
      apply List_toFinset_rotation_invariant
    exact congrArg (Union.union Head.toFinset) h1
  _=(Head++Tail).toFinset:= by
    simp
  _=Li.toFinset:= by
    rw[happend_Head_Tail]
  _=KFam:= by
    exact heqFam

constructor
dsimp [Li']
apply List.Nodup.append
apply List.Nodup.sublist hsublistHead hNoDup
apply List.nodup_rotate.2
apply List.Nodup.sublist hsublist hNoDup

apply List.disjoint_toFinset_iff_disjoint.1
rw[List_toFinset_rotation_invariant]
dsimp[Head, Tail]
apply List.disjoint_toFinset_iff_disjoint.2
apply List.disjoint_take_drop
exact hNoDup
simp

unfold clump_list_dense_up_to_n
intro ii hii
by_cases  hcase: ii≤ n
unfold  clump_list_dense_up_to_n  at dense_up_to_n
have hLiatn: clump_list_dense_at_1 p m κ pr h α (List.drop ii Li) nan:=by
  apply dense_up_to_n
  repeat assumption
unfold clump_list_dense_at_1
have hunioneq: list_union_from_i p m κ pr h Li' nan ii=list_union_from_i p m κ pr h Li nan ii:=by
  unfold list_union_from_i
  dsimp[Li']
  unfold list_union
  unfold list_BSet
  have h12: (List.drop ii (Head ++ Tail.rotate i)).toFinset
    =(List.drop ii Li).toFinset:=by sorry
  rw[h12]
have hatn_eq: Li'.getD ii nan= Li.getD ii nan:=by
  sorry
rw[hunioneq, hatn_eq]
unfold clump_list_dense_at_i at hLiatn
simp
simp at hLiatn
exact hLiatn

have hii_eq: ii=n+1:= by
  apply  Nat.le_antisymm hii
  simp at hcase
  exact hcase

rw[hii_eq]
unfold clump_list_dense_at_i

have hnp1:  (Li'.getD (n + 1) nan)=(Tail.rotate i).headD nan:=by
  sorry
have hnp2: list_union_from_i p m κ pr h Li' nan (n + 1)=list_union p m κ pr h ((Tail.rotate i).drop 1):=by
  sorry
  --simp

--dsimp [Head]

sorry
/-
lemma Order_separated_family_induction_step
(n: ℕ )
(KFam: Finset (Clump G p m κ pr h))
(heqFam: Li.toFinset= KFam)
(Li: List (Clump G p m κ pr h))
(hNoDup: Li.Nodup)
(hn: n< Li.length)
(hSeparated: list_separated_up_to p m κ pr h α Li  nan n)
--(Clump_Decomposition L KFam2)
--(Clump_family_narrow KFam2)
(nan: Clump G p m κ pr h)
(hSeparatedFam: Clump_family_separated KFam)
: ∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧ (Li.Nodup)
∧ (list_separated_up_to p m κ pr h α Li  nan (n+1))
:=by
by_cases hcase: ∃ (i: ℕ ), i>n∧  i≤ Li.length   ∧ (∀ (j: ℕ ), (i≠ j)→ (n<j)→ (j≤ Li.length)→ (α*(( BSet (List.getD Li i nan))∩( BSet (List.getD Li i nan))).toFinset.card≥ m))
rcases hcase with ⟨i, hi, hii, hiii⟩
-/
/-
lemma Order_separated_family
(KFam: Finset (Clump G p m κ pr h))
--(Clump_Decomposition L KFam2)
--(Clump_family_narrow KFam2)
(nan: Clump G p m κ pr h)
(hSeparatedFam: Clump_family_separated KFam)
: ∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧ (Li.Nodup)
∧ (separated_list p m κ pr h α Li  nan)
:=by
let Li0:= KFam.toList

let S: Set ℕ:={n| ∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧ (Li.Nodup)
∧ (list_separated_up_to p m κ pr h α Li  nan n)}

by_cases hcase: ∃ (n: ℕ ), n∈ S ∧ n≥ KFam.card

rcases hcase with ⟨n, hS, hn⟩
dsimp [S] at hS
rcases hS with ⟨Li, hLi, hLi2, hLi3⟩
use Li
constructor
exact hLi
constructor
exact hLi2
unfold separated_list
intro  i j hij hj
have h1: i≤ n:= by
   calc
    i≤ j:= by exact Nat.le_of_succ_le hij
    _≤ Li.length:=by exact hj
    _=KFam.card:=by rw[hLi.symm]; exact (List.toFinset_card_of_nodup hLi2).symm
    _≤ n:=by exact hn
apply hLi3 i j hij h1 hj
-/



/-lemma Clump_decomposition_of_locally_dense
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
(hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L )
: ∃ (KFam2: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam2
∧ Clump_family_narrow KFam2
∧ Clump_family_separated KFam2
:=by-/


--def list_union_from_i (p m κ pr h : ℕ )
--(Li: List (Clump G p m κ pr h))(nan:  Clump G p m κ pr h) (i: ℕ )
--: Set V
--:=Set.sUnion {B: Set V| ∃ (j: ℕ ), B=BSet (List.getD Li j nan)∧ i<j ∧ j≤ Li.length}
