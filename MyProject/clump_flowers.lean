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
variable (p m κ pr h γ α : ℕ)
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (hI:Inhabited (Clump G p m κ pr h))
variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}




noncomputable def list_BSet --(p m κ pr h : ℕ )
(Li: List (Clump G p m κ pr h))
: Finset (Set V):= Finset.image BSet Li.toFinset

def list_union
(Li: List (Clump G p m κ pr h))
: Set V:= Set.sUnion (list_BSet p m κ pr h  Li )

--def list_union_from_i (p m κ pr h : ℕ )
--(Li: List (Clump G p m κ pr h))(:  Clump G p m κ pr h) (i: ℕ )
--: Set V
--:=list_union  (Li.drop (i))

def list_union_dropping_first --(p m κ pr h : ℕ )
(Li: List (Clump G p m κ pr h))
: Set V
:=list_union  p m κ pr h (Li.drop (1))



def clump_list_dense_at_1 --( p m κ pr h α: ℕ )
(Li: List (Clump G p m κ pr h))
:=(α*(( BSet (List.head! Li ))∩( list_union_dropping_first p m κ pr h  Li)).toFinset.card≥ m)

--def clump_list_dense_at_i ( p m κ pr h α i: ℕ )
--(Li: List (Clump G p m κ pr h))(:  Clump G p m κ pr h)
--:=(α*(( BSet (List.getD Li i ))∩( list_union_from_i p m κ pr h  Li  i)).toFinset.card≥ m)

def clump_list_sparse_up_to_n (n:ℕ )--( p m κ pr h α n: ℕ )
(Li: List (Clump G p m κ pr h))
:=∀ (i: ℕ ), (i< n)→ ¬ clump_list_dense_at_1  p m κ pr h α hI  (Li.drop i)
--:=∀ (i: ℕ ), (i≤ n)→ clump_list_dense_at_i p m κ pr h α i Li


def clump_list_dense -- ( p m κ pr h α: ℕ )
(Li: List (Clump G p m κ pr h))
:=
∀ (i: ℕ ),  clump_list_dense_at_1 p m κ pr h α hI (Li.rotate i)


def family_contains_dense_list-- ( p m κ pr h α: ℕ )
(KFam: Finset (Clump G p m κ pr h))
:=
∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset⊆  KFam)∧
(Li.Nodup)∧
(clump_list_dense p m κ pr h α hI Li  )


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



lemma list_drop_tofinset
(L1 L2: List (Clump G p m κ pr h))
(i: ℕ )
(eq1: L1.take i=L2.take i)
(eq2: L1.toFinset=L2.toFinset)
(nodup1: L1.Nodup)
(nodup2: L2.Nodup)
:
(L1.drop i).toFinset=(L2.drop i).toFinset:=by
have eq3:   L1.toFinset=L2.toFinset:=by exact eq2

let Head1: List (Clump G p m κ pr h):= L1.take i
let Tail1: List (Clump G p m κ pr h):= L1.drop i
let Head2: List (Clump G p m κ pr h):= L2.take i
let Tail2: List (Clump G p m κ pr h):= L2.drop i
have eq4:   Head1.toFinset=Head2.toFinset:=by dsimp[Head1, Head2]; exact congrArg List.toFinset eq1

have h1: L1= Head1++Tail1:= by
  exact (List.take_append_drop i L1).symm
have h2: L2= Head2++Tail2:= by
  exact (List.take_append_drop i L2).symm
have h3: Head1.toFinset=Head2.toFinset:= by
  dsimp[Head1, Head2]
  rw[eq1]
rw[h1, h2] at eq2
have h01: (L1.drop i).toFinset=(Tail1).toFinset:= by
  dsimp[Tail1]
have h02: (L2.drop i).toFinset=(Tail2).toFinset:= by
  dsimp[Tail2]
rw[h01, h02]

have h11: (Head1 ++ Tail1).toFinset=(Head1).toFinset ∪ (Tail1).toFinset := by
  exact List.toFinset_append
have h12: (Head2 ++ Tail2).toFinset=(Head2).toFinset ∪ (Tail2).toFinset := by
  exact List.toFinset_append
rw[h11, h12] at eq2

have h21: (Head1).toFinset∩ (Tail1).toFinset=∅ := by
  refine disjoint_iff_inter_eq_empty.mp ?_
  dsimp[Head1, Tail1]
  refine List.disjoint_toFinset_iff_disjoint.mpr ?_
  apply List.disjoint_take_drop
  exact nodup1
  exact Nat.le_refl i
have h31: (Tail1).toFinset=L1.toFinset\ (Head1).toFinset:= by
  rw[h1, h11]
  refine (union_sdiff_cancel_left ?h).symm
  exact disjoint_iff_inter_eq_empty.mpr h21

have h22: (Head2).toFinset∩ (Tail2).toFinset=∅ := by
  refine disjoint_iff_inter_eq_empty.mp ?_
  dsimp[Head2, Tail2]
  refine List.disjoint_toFinset_iff_disjoint.mpr ?_
  apply List.disjoint_take_drop
  exact nodup2
  exact Nat.le_refl i
have h32: (Tail2).toFinset=L2.toFinset\ (Head2).toFinset:= by
  rw[h2, h12]
  apply (union_sdiff_cancel_left _).symm
  exact disjoint_iff_inter_eq_empty.mpr h22
  --apply union_sdiff_cancel_left.symm
  --exact disjoint_iff_inter_eq_empty.mpr h22
rw[h31, h32]
rw[eq3, eq4]



lemma Order_family_induction_step
(n: ℕ )
(KFam: Finset (Clump G p m κ pr h))
(Li: List (Clump G p m κ pr h))
(heqFam: Li.toFinset= KFam)
(hNoDup: Li.Nodup)
(hn: n< Li.length)
(dense_up_to_n:  clump_list_sparse_up_to_n p m κ pr h α hI n Li  )
(no_dense_sets: ¬ family_contains_dense_list p m κ pr h α hI KFam  )
:
∃ (Li': List (Clump G p m κ pr h)),
(Li'.toFinset= KFam)∧
(Li'.Nodup)∧
(clump_list_sparse_up_to_n p m κ pr h α hI (n+1) Li' )
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
    exact Tail_toFinset_contained_in_list p m κ pr h Li n
  _= KFam:= by
    exact heqFam
have Tail_NoDup: Tail.Nodup:= by
  dsimp[Tail]
  exact List.Nodup.sublist hsublist hNoDup

have Tail_not_dense: ¬ clump_list_dense p m κ pr h α hI Tail :=by
  by_contra contr
  have dense_sets:family_contains_dense_list p m κ pr h α hI KFam :=by
    exact ⟨Tail, Tail_in_KFam, Tail_NoDup, contr⟩
  exact no_dense_sets dense_sets

dsimp [clump_list_dense] at Tail_not_dense
push_neg at Tail_not_dense
rcases Tail_not_dense with ⟨i, hi⟩

let Li':=Head++(Tail.rotate i)
have Li'_nodup:Li'.Nodup:=by
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

exact Li'_nodup


unfold clump_list_sparse_up_to_n
intro ii hii
by_cases  hcase: ii< n
unfold  clump_list_sparse_up_to_n  at dense_up_to_n
have hLiatn: ¬ clump_list_dense_at_1 p m κ pr h α hI (List.drop ii Li) :=by
  apply dense_up_to_n
  repeat assumption
unfold clump_list_dense_at_1

have Head_nonemp: List.drop ii Head ≠ []:=by
    dsimp[Head]
    simp
    constructor
    exact hcase
    calc
      ii<n:=by exact hcase
      _≤ n:=by exact Nat.le_refl n
    exact hn

have ii_le_Head:ii ≤ Head.length:=by
  calc
    ii≤ n:=by exact Nat.le_of_lt_succ hii
    _≤ Head.length:=by
      dsimp[Head]
      simp
      exact Nat.le_of_succ_le hn

have take1: List.take ii (Head ++ Tail)=List.take ii (Head):=by
  calc
  List.take ii (Head ++ Tail)=List.take ii (Head)++List.take (ii-Head.length) (Tail):=by
    apply List.take_append_eq_append_take
  _=List.take ii (Head) ++ []:=by
    congr
    refine List.take_eq_nil_iff.mpr ?_
    right
    refine Nat.sub_eq_zero_of_le ?_
    exact ii_le_Head
  _=List.take ii (Head):=by
    exact List.append_nil (List.take ii Head)


have take2: List.take ii (Head ++ Tail.rotate i)=List.take ii (Head):=by
  calc
  List.take ii (Head ++ Tail.rotate i)=List.take ii (Head)++List.take (ii-Head.length) (Tail.rotate i):=by
    apply List.take_append_eq_append_take
  _=List.take ii (Head) ++ []:=by
    congr
    refine List.take_eq_nil_iff.mpr ?_
    right
    refine Nat.sub_eq_zero_of_le ?_
    exact ii_le_Head
  _=List.take ii (Head):=by
    exact List.append_nil (List.take ii Head)

have drop_len_pos: 1 ≤ (List.drop ii Head).length:=by
  dsimp[Head]
  simp
  refine Nat.le_sub_of_add_le ?h
  apply Nat.le_min_of_le_of_le
  exact Nat.one_add_le_iff.mpr hcase
  calc
    1+ii≤ n:=by exact Nat.one_add_le_iff.mpr hcase
    _≤ Li.length:=by exact Nat.le_of_succ_le hn

have hunioneq: list_union_dropping_first p m κ pr h (List.drop ii Li')=list_union_dropping_first p m κ pr h (List.drop ii Li):=by
  unfold list_union_dropping_first
  dsimp[Li']
  unfold list_union
  unfold list_BSet
  have h12: (List.drop 1 (List.drop ii (Head ++ Tail.rotate i))).toFinset
    =(List.drop 1 (List.drop ii Li)).toFinset:=by
    rw[happend_Head_Tail]
    apply list_drop_tofinset
    --List.take 1 (List.drop ii (Head ++ Tail.rotate i)) = List.take 1 (List.drop ii (Head ++ Tail))
    have hx1: List.drop ii (Head ++ Tail.rotate i)=List.drop ii (Head) ++ Tail.rotate i:=by
      apply List.drop_append_of_le_length
      calc
          ii≤ n:=by exact Nat.le_of_lt_succ hii
          _≤ Head.length:=by
            dsimp[Head]
            simp
            exact Nat.le_of_succ_le hn
    have hx2: List.drop ii (Head ++ Tail)=List.drop ii (Head) ++ Tail:=by
      apply List.drop_append_of_le_length
      calc
          ii≤ n:=by exact Nat.le_of_lt_succ hii
          _≤ Head.length:=by
            dsimp[Head]
            simp
            exact Nat.le_of_succ_le hn
    rw[hx1, hx2]

    have hy1: List.take 1 (List.drop ii Head ++ Tail.rotate i)=List.take 1 (List.drop ii Head):=by
      calc
        List.take 1 (List.drop ii Head ++ Tail.rotate i)=List.take 1 (List.drop ii Head)++List.take (1-(List.drop ii Head).length) (Tail.rotate i):=by
          apply List.take_append_eq_append_take
      _=List.take 1 (List.drop ii Head)++[]:=by
        congr
        refine List.take_eq_nil_iff.mpr ?_
        right
        refine Nat.sub_eq_zero_of_le ?_
        exact drop_len_pos
      _=List.take 1 (List.drop ii Head):=by
        exact List.append_nil (List.take 1 (List.drop ii Head))

    have hy2: List.take 1 (List.drop ii Head ++ Tail)=List.take 1 (List.drop ii Head):=by
      calc
        List.take 1 (List.drop ii Head ++ Tail)=List.take 1 (List.drop ii Head)++List.take (1-(List.drop ii Head).length) (Tail):=by
          apply List.take_append_eq_append_take
      _=List.take 1 (List.drop ii Head)++[]:=by
        congr
        refine List.take_eq_nil_iff.mpr ?_
        right
        refine Nat.sub_eq_zero_of_le ?_
        exact drop_len_pos
      _=List.take 1 (List.drop ii Head):=by
        exact List.append_nil (List.take 1 (List.drop ii Head))

    rw[hy1, hy2]




    apply list_drop_tofinset
    --List.take ii (Head ++ Tail.rotate i) = List.take ii (Head ++ Tail)
    rw[take1, take2]
    simp
    --(Head ++ Tail.rotate i).toFinset = (Head ++ Tail).toFinset
    have hx:(Tail.rotate i).toFinset = Tail.toFinset:=by
      exact List_toFinset_rotation_invariant p m κ pr h Tail i
    rw[hx]
    --(Head ++ Tail.rotate i).Nodup
    dsimp [Li'] at Li'_nodup
    exact Li'_nodup

    --(Head ++ Tail).Nodup
    rw[happend_Head_Tail.symm]
    exact hNoDup
    -- (List.drop ii (Head ++ Tail.rotate i)).Nodup
    refine List.Nodup.sublist ?nodup2.a Li'_nodup
    dsimp[Li']
    exact List.drop_sublist ii (Head ++ Tail.rotate i)
    --(List.drop ii (Head ++ Tail)).Nodup
    rw[happend_Head_Tail.symm]
    apply List.Nodup.sublist _ hNoDup
    exact List.drop_sublist ii Li





  rw[h12]


have hatn_eq: (List.drop ii Li').head! = (List.drop ii Li).head! :=by
  dsimp[Li']
  calc
  (List.drop ii (Head ++ Tail.rotate i)).head!
  =((List.drop ii Head) ++ Tail.rotate i).head! :=by
    congr
    apply List.drop_append_of_le_length
    dsimp[Head]
    simp
    constructor
    exact Nat.le_of_lt_succ hii
    calc
      ii≤ n:=by exact Nat.le_of_lt_succ hii
      _≤ Li.length:=by exact Nat.le_of_succ_le hn
  _=((List.drop ii Head)).head!:=by
    refine List.head!_append (Tail.rotate i) ?h
    exact Head_nonemp
  _=(List.drop ii Li).head!:=by
    rw[happend_Head_Tail]
    have h1: List.drop ii (Head ++ Tail)=List.drop ii (Head) ++ Tail:=by
      apply List.drop_append_of_le_length
      calc
          ii≤ n:=by exact Nat.le_of_lt_succ hii
          _≤ Head.length:=by
            dsimp[Head]
            simp
            exact Nat.le_of_succ_le hn
    rw[h1]
    apply (List.head!_append Tail _).symm
    exact Head_nonemp


rw[hunioneq]
rw[hatn_eq]
unfold clump_list_dense_at_1 at hLiatn
simp
simp at hLiatn
exact hLiatn

have hii_eq: ii=n:= by
  apply  Nat.le_antisymm
  exact Nat.le_of_lt_succ hii
  simp at hcase
  exact hcase

rw[hii_eq]
--unfold clump_list_dense_at_1

have drop_n_eq:  (List.drop n Li')=(Tail.rotate i):=by
  dsimp [Li']
  apply List.drop_left'
  dsimp[Head]
  refine List.length_take_of_le ?h.h
  exact Nat.le_of_succ_le hn
rw[drop_n_eq]

exact hi

/-
lemma Order_separated_family_induction_step
(n: ℕ )
(KFam: Finset (Clump G p m κ pr h))
(heqFam: Li.toFinset= KFam)
(Li: List (Clump G p m κ pr h))
(hNoDup: Li.Nodup)
(hn: n< Li.length)
(hSeparated: list_separated_up_to p m κ pr h α Li   n)
--(Clump_Decomposition L KFam2)
--(Clump_family_narrow KFam2)
(: Clump G p m κ pr h)
(hSeparatedFam: Clump_family_separated KFam)
: ∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧ (Li.Nodup)
∧ (list_separated_up_to p m κ pr h α Li   (n+1))
:=by
by_cases hcase: ∃ (i: ℕ ), i>n∧  i≤ Li.length   ∧ (∀ (j: ℕ ), (i≠ j)→ (n<j)→ (j≤ Li.length)→ (α*(( BSet (List.getD Li i ))∩( BSet (List.getD Li i ))).toFinset.card≥ m))
rcases hcase with ⟨i, hi, hii, hiii⟩
-/
/-
lemma Order_separated_family
(KFam: Finset (Clump G p m κ pr h))
--(Clump_Decomposition L KFam2)
--(Clump_family_narrow KFam2)
(: Clump G p m κ pr h)
(hSeparatedFam: Clump_family_separated KFam)
: ∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧ (Li.Nodup)
∧ (separated_list p m κ pr h α Li  )
:=by
let Li0:= KFam.toList

let S: Set ℕ:={n| ∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧ (Li.Nodup)
∧ (list_separated_up_to p m κ pr h α Li   n)}

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
(: Clump G p m κ pr h)
(hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L )
: ∃ (KFam2: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam2
∧ Clump_family_narrow KFam2
∧ Clump_family_separated KFam2
:=by-/


--def list_union_from_i (p m κ pr h : ℕ )
--(Li: List (Clump G p m κ pr h))(:  Clump G p m κ pr h) (i: ℕ )
--: Set V
--:=Set.sUnion {B: Set V| ∃ (j: ℕ ), B=BSet (List.getD Li j )∧ i<j ∧ j≤ Li.length}


/-
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


def separated_list --(p m κ pr h α : ℕ )
(Li: List (Clump G p m κ pr h))
:=∀(i j : ℕ ), (i<j)→ (j≤ Li.length)→ (α*(( BSet (List.get! Li i ))∩( BSet (List.get! Li i ))).toFinset.card≥ m)


def list_separated_up_to --(p m κ pr h α t: ℕ )
(Li: List (Clump G p m κ pr h))(t:ℕ )
:=∀(i j : ℕ ), (i<j)→ (i≤ t)→ (j≤ Li.length)→ (α*(( BSet (List.get! Li i ))∩( BSet (List.get! Li i ))).toFinset.card≥ m)

-/
