import MyProject

import MyProject.path.find_path_forest

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 250000

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




lemma finset_disjoint_left
(v: V)
(T S: Finset V)
(disj: Disjoint S T)
(hv: v∈ S)
:
v∉ T:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine not_disjoint_iff.mpr ?_
  use v
exact h2 disj

lemma finset_disjoint_right
(v: V)
(S T: Finset V)
(disj: Disjoint S T)
(hv: v∈ T)
:
v∉ S:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine not_disjoint_iff.mpr ?_
  use v
exact h2 disj


lemma finset_disjoint_left_list
(v: V)
(T: List V)
(S: Finset V)
(disj: Disjoint S T.toFinset)
(hv: v∈ S)
:
v∉ T:= by
have h1: v∉ T.toFinset:= by exact   finset_disjoint_right v T.toFinset S (id (Disjoint.symm disj)) hv
by_contra cont
have h2: v∈ T.toFinset:= by exact List.mem_toFinset.mpr cont
exact h1 h2


lemma finset_disjoint_right_list
(v: V)
(T: List V)
(S: Finset V)
(disj: Disjoint T.toFinset S )
(hv: v∈ S)
:
v∉ T:= by
have h1: v∉ T.toFinset:= by exact finset_disjoint_right v T.toFinset S disj hv
by_contra cont
have h2: v∈ T.toFinset:= by exact List.mem_toFinset.mpr cont
exact h1 h2


--used
lemma find_pairs_in_M_list
(Ord: List (Clump G p m κ pr h))
(Ver: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)--possibly just subgraph list??
(k: ℕ )
(LM_length: LM.length≥ k)
(Ord_length: Ord.length≥ k)
(hk: 2*k+Ver.length+2≤ m/pr)
:
∃ (S E: List V),
(S.length=k)
∧ (E.length=k)
∧ (List.Disjoint S E)
∧ (List.Disjoint Ver S )
∧ (List.Disjoint E Ver )
∧ (S.Nodup)
∧ (E.Nodup)
∧ (∀ (i: ℕ ), i<k→ (S.get! i)∈ (LM.get! i).verts)
∧ (∀ (i: ℕ ), i<k→ (E.get! i)∈ (LM.get! i).verts)
:= by
induction' k with k IH
use []
use []
constructor
exact rfl
constructor
exact rfl
constructor
exact List.disjoint_nil_left []
constructor
exact List.disjoint_nil_right Ver
constructor
exact List.disjoint_nil_left Ver
constructor
exact List.nodup_nil
constructor
exact List.nodup_nil
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi

-----------induction-------------

have LM_length': LM.length≥ k:= by
  exact Nat.le_of_succ_le LM_length
have Ord_length': Ord.length≥ k:= by
  exact Nat.le_of_succ_le Ord_length
have hk': 2 * k + Ver.length + 2 ≤ m / pr:= by
  calc
     2 * k + Ver.length + 2
     ≤2 * (k+1) + Ver.length + 2:= by
        gcongr
        exact Nat.le_add_right k 1
     _≤ m / pr:= by exact hk

have ind: _:= by exact IH LM_length' Ord_length' hk'

rcases ind with ⟨S, ind2 ⟩
rcases ind2 with ⟨E, Sl, El, SEd, VSd, EVd, Snd, End, Sget, Eget ⟩


have hkl: k<Ord.length:= by exact Ord_length
have hkm: k<LM.length:= by exact LM_length

have MinOrd:LM.get! k ∈ (Ord.get! k).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M k  hkl
  simp at h2
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2



have hcutdense:   near_regular (LM.get! k) m pr:= by
  apply (Ord.get! k).M_Near_Regular
  exact MinOrd
  --apply LM_in_M k MinOrd

have hcard:    (LM.get! k).verts.toFinset.card≥ m/pr:= by
  exact M_order_lower_bound MinOrd

have diff:  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)).card≥ 2:= by
  calc
    ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)).card
    ≥
    (LM.get! k).verts.toFinset.card
    -(S.toFinset∪ E.toFinset∪ Ver.toFinset).card:= by
      exact le_card_sdiff (S.toFinset ∪ E.toFinset ∪ Ver.toFinset) (LM.get! k).verts.toFinset
    _≥  (LM.get! k).verts.toFinset.card
    -(S.toFinset.card+ E.toFinset.card+ Ver.toFinset.card):= by
      gcongr
      exact card_union_3 S.toFinset E.toFinset Ver.toFinset
    _≥ (m/pr) -((k+1)+(k+1) + Ver.length):= by
      gcongr
      calc
        S.toFinset.card
        ≤ S.length:= by exact List.toFinset_card_le S
        _= k := by exact Sl
        _≤ k+1:= by exact Nat.le_add_right k 1
      calc
        E.toFinset.card
        ≤ E.length:= by exact List.toFinset_card_le E
        _= k := by exact El
        _≤ k+1:= by exact Nat.le_add_right k 1
      exact List.toFinset_card_le Ver
    _= m/pr- (2*(k+1)+Ver.length):= by ring_nf
    _≥ 2:= by exact Nat.le_sub_of_add_le' hk

have hex: ∃ ( T: Finset V), T⊆ ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset))∧ T.card=2:= by
  exact
    exists_smaller_set ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset)) 2
      diff
rcases hex with ⟨T, hT1, hT2⟩
rw [@card_eq_two] at hT2
rcases hT2 with ⟨s, e, hse1, hse2 ⟩
have sinT: s∈ T:= by rw[hse2]; exact mem_insert_self s {e}
have einT: e∈ T:= by rw[hse2]; simp


have sin2: s∈ ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  exact hT1 sinT
have ein2: e∈ ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  exact hT1 einT

have Tsubs: (LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset)⊆  (LM.get! k).verts.toFinset:= by
  exact sdiff_subset (LM.get! k).verts.toFinset (S.toFinset ∪ E.toFinset ∪ Ver.toFinset)
have  sin3: s∈ (LM.get! k).verts.toFinset:= by
  exact Tsubs (hT1 sinT)
have  ein3: e∈ (LM.get! k).verts.toFinset:= by
  exact Tsubs (hT1 einT)

have Sint2: Disjoint S.toFinset  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  --refine disjoint_iff_inter_eq_empty.mp ?_
  simp
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro h5 h6 h7
  exfalso
  exact h6 ha


have Sint3: Disjoint E.toFinset  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  --refine disjoint_iff_inter_eq_empty.mp ?_
  simp
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro h5 h6 h7
  exfalso
  exact h7 ha

have Sint4: Disjoint Ver.toFinset  ((LM.get! k).verts.toFinset\ (S.toFinset∪ E.toFinset∪ Ver.toFinset)):= by
  --refine disjoint_iff_inter_eq_empty.mp ?_
  simp
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro h5 h6 h7
  exact ha


let S':List V:= S++[s]
let E':List V:= E++[e]
use S'
use E'
--Slength
constructor
dsimp[S']
simp
exact Sl
--Elength
constructor
dsimp[E']
simp
exact El
--Disjointness SE
constructor
dsimp[S', E']
simp
constructor
constructor
exact SEd

exact
  finset_disjoint_left_list s E
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint3)) (hT1 sinT)
constructor
exact
  finset_disjoint_left_list e S
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint2)) (hT1 einT)

exact id (Ne.symm hse1)
constructor
---disjointness S Ver
dsimp[S']
simp
constructor
exact VSd

exact
  finset_disjoint_left_list s Ver
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint4)) (hT1 sinT)

constructor
---disjointness E Ver
dsimp[E']
simp
constructor
exact EVd

exact
  finset_disjoint_left_list e Ver
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint4)) (hT1 einT)

constructor
--S'nodup---
dsimp[S']
refine
  List.Nodup.append Snd ?h.right.right.right.right.right.left.d₂
    ?h.right.right.right.right.right.left.dj
exact List.nodup_singleton s
simp
exact
  finset_disjoint_left_list s S
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint2)) (hT1 sinT)


constructor
--E'nodup---
dsimp[E']
refine List.nodup_middle.mpr ?h.right.right.right.right.right.right.left.a
simp
constructor
exact
  finset_disjoint_left_list e E
    ((LM.get! k).verts.toFinset \ (S.toFinset ∪ E.toFinset ∪ Ver.toFinset))
    (id (Disjoint.symm Sint3)) (hT1 einT)

exact End
--in graphs
constructor
dsimp[S']
intro i hi
by_cases case: i<k
have h1: (S ++ [s]).get! i =S.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id Sl.symm)
rw[h1]
apply   Sget i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (S ++ [s]).get! k =[s].get! (k-S.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right S [s] default k
  exact Nat.le_of_eq Sl
rw[Sl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
simp only [Set.mem_toFinset] at sin3
exact sin3


dsimp[E']
intro i hi
--simp
by_cases case: i<k
have h1: (E ++ [e]).get! i =E.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id El.symm)
rw[h1]
apply   Eget i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (E ++ [e]).get! k =[e].get! (k-E.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right E [e] default k
  exact Nat.le_of_eq El
rw[El] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
simp only [Set.mem_toFinset] at ein3
exact ein3

lemma BSetPlusM_verts_in_Gr
(K:Clump G p m κ pr h)
:
BSetPlusM K⊆ K.Gr.verts:=by
unfold BSetPlusM
unfold BSet
intro v hv
simp at hv
rcases hv with case|case
exact case.1
rcases case with ⟨  Mi, hMi1, hMi2⟩
have h1: Mi≤ K.Gr:= by
  exact M_in_Gr p m κ pr h K Mi hMi1
have h2: Mi.verts ⊆ K.Gr.verts:= by
  apply subgraphs_vertex_sets_subsets G
  exact h1
exact h2 hMi2

lemma BSetPlusM_verts_in_some_Hi
(K:Clump G p m κ pr h)
(v: V)
(hv: v∈ BSetPlusM K)
:
∃ (Hi: Subgraph G), Hi∈ K.H∧ v∈ Hi.verts
:=by
have h1: v∈ K.Gr.verts:= by
  have h2: BSetPlusM K⊆ K.Gr.verts:= by
    exact BSetPlusM_verts_in_Gr K
  exact h2 hv
rw[K.H_Partition_K.symm] at h1
simp at h1
exact h1


---------------------------------------------------------
--used
lemma add_Ver_to_M_list
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)

(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k)
(Ord_length: Ord.length> k)
(Ver_length: Ver.length> k)
(S_length: S.length> k)
--new
(narrow: Clump_family_narrow  (Ord.toFinset))
(γggκ: γ ≥ 16 * κ ^ (2 * (100 * (pr*pr*h)).factorial))
(pLarge: p≥ 20)
(mLarge: m≥ 20)
(mggpr: m ≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ p)
(κggh: κ ≥ h)
(Ord_In_H: ∀(i: ℕ ), i<Ord.length→ ((Ord.get! i).Gr≤ H))
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list! iSub HL γ k)
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! i).verts)
∧ (∀ (i: ℕ ), i<k→ (S.get! i)∈ (HL.get! i).verts)
∧ (∀ (i: ℕ ), i<k→ (HL.get! i)≤ H)
∧ (∀ (i: ℕ ), i<k→ (HL.get! i).verts.toFinset.card≥ m)

:= by
unfold Vertex_list_in_clump_list_BSetPlusM at VerInOrd


induction' k with k IH
use []
constructor
exact rfl
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi

intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
-----------induction-------------


have LM_length': LM.length> k:= by
  exact Nat.lt_of_succ_lt LM_length
have Ord_length': Ord.length> k:= by
  exact Nat.lt_of_succ_lt Ord_length
have Ver_length': Ver.length> k:= by
  exact Nat.lt_of_succ_lt Ver_length
have S_length': S.length> k:= by
  exact Nat.lt_of_succ_lt S_length
have hSinLM: ∀ i < k, S.get! i ∈ (LM.get! i).verts:= by
  intro i hi
  apply hSML i
  exact Nat.lt_add_right 1 hi
have ind: _:= by exact IH hSinLM LM_length' Ord_length' Ver_length' S_length'
--have hk':k ≤ kmax:= by
--  exact Nat.le_of_succ_le hk

rcases ind with ⟨HL, HLl, Hcd,VerHL,SHL, InH , Large ⟩


have hkl: k<Ord.length:= by exact Ord_length'
have hkm: k<LM.length:= by exact LM_length'




have MinOrd:LM.get! k ∈ (Ord.get! k).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M k  hkl
  simp at h2
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2


have MinOrd:Ver.get! k ∈  BSetPlusM (Ord.get! k) ∩ BSetPlusM (Ord.get! (k + 1)):= by
  apply VerInOrd
  exact Nat.lt_sub_of_add_lt Ord_length
have MinOrd2:Ver.get! k ∈  BSetPlusM (Ord.get! k):= by
  exact Set.mem_of_mem_inter_left MinOrd

have Hi_ex: ∃ (Hi: Subgraph G), Hi∈  (Ord.get! k).H ∧ Ver.get! k∈ Hi.verts:= by
  apply BSetPlusM_verts_in_some_Hi
  exact MinOrd2
rcases Hi_ex with ⟨Hi, hHi, hVerHi⟩


let K:Subgraph G:= (Ord.get! k).C ⊔Hi
have Kcut_dense: cut_dense G K γ:= by
  apply clump_add_Hi_cut_dense
  exact mPositive
  exact pPositive
  exact κPositive
  exact iSub
  --γ ≥ 16 * κ ^ (2 * (100 * (Ord.get! k).k).factorial)
  have h1: (Ord.get! k).k ≤ pr * pr * h:= by
    unfold Clump_family_narrow at narrow
    apply narrow
    have h1: Ord.get! k =Ord.get ⟨k, ?_⟩ := by
      simp
      refine List.getD_eq_get Ord default ?_
    rw[h1]
    simp
    refine List.get_mem Ord k ?_
    exact hkl
  calc
    16 * κ ^ (2 * (100 * (Ord.get! k).k).factorial)
    ≤16 * κ ^ (2 * (100 * (pr*pr*h)).factorial):= by
      gcongr
      exact κPositive
    _≤ γ := by exact γggκ

  exact hHi
  exact pLarge
  exact mLarge
  exact mggpr
  exact prggp
  exact hggp
  exact κggh


let HL':List (Subgraph G):= HL++[K]
use HL'

constructor
dsimp[HL']
simp
exact HLl


-----cutdense
constructor
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
apply   Hcd i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
exact Kcut_dense

constructor
----Ver in HL
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact VerHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]
exact Set.mem_union_right (Ord.get! k).C.verts hVerHi

----S in HL
constructor
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact SHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]

have hSinMM: S.get! k ∈(LM.get! k).verts:= by
  apply hSML k
  exact lt_add_one k

unfold M_list_in_clump_list at LM_in_M
have hMM: LM.get! k ∈ (Ord.get! k).M:= by
  have h55:_:=by
    apply LM_in_M k
    exact Ord_length'
  simp at h55
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h55
  exact h55
have In_C:(LM.get! k).verts⊆ (Ord.get! k).C.verts:= by
  apply M_verts_contained_in_C_verts_set
  exact hMM

exact Set.mem_union_left Hi.verts (In_C hSinMM)

dsimp[HL']
constructor
intro i hi
by_cases case: i< k
simp
rw[List.getD_append]
simp at InH
apply InH
exact case
rw[HLl]
exact case
have ieq: i=k:= by
  simp at case
  exact Nat.eq_of_le_of_lt_succ case hi
rw[ieq]
simp
rw[List.getD_append_right]
rw[HLl]
simp
dsimp[K]
simp
constructor
calc
  (Ord.getD k default).C
  ≤(Ord.getD k default).Gr:= by
    exact (Ord.getD k default).C_In_K
  _≤ H:= by
    simp at Ord_In_H
    apply Ord_In_H
    exact Ord_length'
    --

have h3: Hi≤ (Ord.get! k).Gr:= by
  apply (Ord.get! k).H_In_K
  exact hHi
exact Preorder.le_trans Hi (Ord.get! k).Gr H h3 (Ord_In_H k Ord_length')

exact Nat.le_of_eq HLl


intro i hi
by_cases case: i< k
simp
rw[List.getD_append]
simp at Large
apply Large
exact case
rw[HLl]
exact case
have ieq: i=k:= by
  simp at case
  exact Nat.eq_of_le_of_lt_succ case hi
rw[ieq]
simp only [List.get!_eq_getD]
rw[List.getD_append_right]
rw[HLl]
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le]
dsimp[K]
rw [@Set.toFinset_union]
calc
  ((Ord.get! k).C.verts.toFinset ∪ Hi.verts.toFinset).card
  ≥ ( Hi.verts.toFinset).card:= by
    gcongr
    simp
  _≥ m:= by
    apply (Ord.get! k).H_Order
    exact hHi
rw[HLl ]
--exact Set.mem_union_right (Ord.get! k).C.verts hVerHi














------------------------------------------------------------------------------------------




lemma add_Ver_to_M_list_starts_alt
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k+1+1→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k+1+1)
(Ord_length: Ord.length> k+1+1)
(Ver_length: Ver.length> k+1)
(S_length: S.length> k+1+1)

--new
(narrow: Clump_family_narrow  (Ord.toFinset))
(γggκ: γ ≥ 16 * κ ^ (2 * (100 * (pr*pr*h)).factorial))
(pLarge: p≥ 20)
(mLarge: m≥ 20)
(mggpr: m ≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ p)
(κggh: κ ≥ h)
(Ord_In_H: ∀(i: ℕ ), i<Ord.length→ ((Ord.get! i).Gr≤ H))
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list! iSub HL γ (k))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! (i)).verts)
∧ (∀ (i: ℕ ), i<k→ (S.tail.get! (i))∈ (HL.get! i).verts)
∧ (∀ i < k , HL.get! i ≤ H)
∧ (∀ (i: ℕ ), i<k→ (HL.get! i).verts.toFinset.card≥ m)
:= by
unfold Vertex_list_in_clump_list_BSetPlusM at VerInOrd


induction' k with k IH
use []
constructor
exact rfl
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi

constructor
intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi

intro i hi
exfalso
have h : ¬ (i<0):= by
  exact Nat.not_lt_zero i
exact h hi
-----------induction-------------


have LM_length': LM.length> k+1+1:= by
  exact Nat.lt_of_succ_lt LM_length
have Ord_length': Ord.length> k+1+1:= by
  exact Nat.lt_of_succ_lt Ord_length
have Ver_length': Ver.length> k+1:= by
  exact Nat.lt_of_succ_lt Ver_length
have S_length': S.length> k+1+1:= by
  exact Nat.lt_of_succ_lt S_length
have hSinLM: ∀ i < k+1+1, S.get! i ∈ (LM.get! i).verts:= by
  intro i hi
  apply hSML i
  exact Nat.lt_add_right 1 hi
have ind: _:= by exact IH hSinLM LM_length' Ord_length' Ver_length' S_length'
--have hk':k ≤ kmax:= by
--  exact Nat.le_of_succ_le hk

rcases ind with ⟨HL, HLl, Hcd,VerHL,SHL, InH, Large  ⟩


have hkl: k+1+1<Ord.length:= by exact Ord_length'
have hkm: k+1+1<LM.length:= by exact LM_length'

have kml:  k < Ord.length - 1:= by
  apply Nat.lt_sub_of_add_lt
  exact Nat.lt_of_succ_lt Ord_length'



have MinOrd:LM.get! (k+1+1) ∈ (Ord.get! (k+1+1)).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M (k+1+1)  hkl
  simp at h2
  simp
  have h3: LM.getD (k+1+1) default=LM.get ⟨k+1+1, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD (k+1+1) ⊥=LM.get ⟨k+1+1, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2


have MinOrd:Ver.get! k ∈  BSetPlusM (Ord.get! k) ∩ BSetPlusM (Ord.get! (k + 1)):= by
  apply VerInOrd
  exact kml
have MinOrd2:Ver.get! k ∈  BSetPlusM (Ord.get! (k+1)):= by
  exact Set.mem_of_mem_inter_right MinOrd

have Hi_ex: ∃ (Hi: Subgraph G), Hi∈  (Ord.get! (k+1)).H ∧ Ver.get! k∈ Hi.verts:= by
  apply BSetPlusM_verts_in_some_Hi
  exact MinOrd2
rcases Hi_ex with ⟨Hi, hHi, hVerHi⟩


let K:Subgraph G:= (Ord.get! (k+1)).C ⊔Hi
have Kcut_dense: cut_dense G K γ:= by
  apply clump_add_Hi_cut_dense
  exact mPositive
  exact pPositive
  exact κPositive
  exact iSub
  --γ ≥ 16 * κ ^ (2 * (100 * (Ord.get! k).k).factorial)
  have h1: (Ord.get! (k+1)).k ≤ pr * pr * h:= by
    unfold Clump_family_narrow at narrow
    apply narrow
    have h1: Ord.get! (k+1) =Ord.get ⟨k+1, ?_⟩ := by
      simp
      refine List.getD_eq_get Ord default ?_
    rw[h1]
    simp
    apply  List.get_mem Ord (k+1)
    exact Nat.add_lt_of_lt_sub kml
  calc
    16 * κ ^ (2 * (100 * (Ord.get! (k+1)).k).factorial)
    ≤16 * κ ^ (2 * (100 * (pr*pr*h)).factorial):= by
      gcongr
      exact κPositive
    _≤ γ := by exact γggκ

  exact hHi
  exact pLarge
  exact mLarge
  exact mggpr
  exact prggp
  exact hggp
  exact κggh


let HL':List (Subgraph G):= HL++[K]
use HL'

constructor
dsimp[HL']
simp
exact HLl


-----cutdense
constructor
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
apply   Hcd i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
exact Kcut_dense

constructor
----Ver in HL
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact VerHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]
exact Set.mem_union_right (Ord.get! (k+1)).C.verts hVerHi

----S in HL
constructor
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact SHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! k =[K].get! (k-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default k
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]

have hSinMM: S.tail.get! k ∈(LM.get! (k+1)).verts:= by
  have h1:  S.tail.get! k= S.get! (k+1):= by
    have h5: S.tail= S.drop 1:= by
      simp
    rw[h5]
    have h22: k < (S.drop 1).length:= by
      simp
      rw [@Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_lt S_length'
    have h2: (S.drop 1).get! k=(S.drop 1).get ⟨ k, h22⟩:= by
      simp only [List.get!_eq_getD]
      apply List.getD_eq_get (S.drop 1) default
    rw[add_comm]
    have h33: (1+k)< S.length:= by
      rw[add_comm]
      exact Nat.lt_of_succ_lt S_length'

    have h3: S.get! (1+k)=S.get  ⟨ 1+k, h33⟩:= by
      simp
      apply List.getD_eq_get S default
    rw[h2, h3]

    rw[List.get_drop]

  rw[h1]
  apply hSML (k  +1)
  simp --exact lt_add_one k

unfold M_list_in_clump_list at LM_in_M
have hMM: LM.get! (k+1) ∈ (Ord.get! (k+1)).M:= by
  have h55:_:=by
    apply LM_in_M (k+1)
    exact Nat.add_lt_of_lt_sub kml
  simp at h55
  simp
  have hkm2: k+1< LM.length:= by
    exact Nat.lt_of_succ_lt LM_length'
  have h3: LM.getD (k+1) default=LM.get ⟨k+1, hkm2 ⟩:= by
    exact List.getD_eq_get LM default hkm2
  have h4: LM.getD (k+1) ⊥=LM.get ⟨k+1, hkm2 ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm2
  rw[h3]
  rw[h4] at h55
  exact h55
have In_C:(LM.get! (k+1)).verts⊆ (Ord.get! (k+1)).C.verts:= by
  apply M_verts_contained_in_C_verts_set
  exact hMM

exact Set.mem_union_left Hi.verts (In_C hSinMM)
constructor
dsimp[HL']
intro i hi
by_cases case: i< k
simp
rw[List.getD_append]
simp at InH
apply InH
exact case
rw[HLl]
exact case
have ieq: i=k:= by
  simp at case
  exact Nat.eq_of_le_of_lt_succ case hi
rw[ieq]
simp
rw[List.getD_append_right]
rw[HLl]
simp
dsimp[K]
simp
constructor
calc
  (Ord.getD (k+1) default).C
  ≤(Ord.getD (k+1) default).Gr:= by
    exact (Ord.getD (k+1) default).C_In_K
  _≤ H:= by
    simp at Ord_In_H
    apply Ord_In_H
    exact Nat.add_lt_of_lt_sub kml
    --

have h3: Hi≤ (Ord.get! (k+1)).Gr:= by
  apply (Ord.get! (k+1)).H_In_K
  exact hHi
have h77:  k + 1 < Ord.length:= by exact Nat.add_lt_of_lt_sub kml
exact Preorder.le_trans Hi (Ord.get! (k+1)).Gr H h3 (Ord_In_H (k+1) h77)

exact Nat.le_of_eq HLl


intro i hi
by_cases case: i< k
simp
rw[List.getD_append]
simp at Large
apply Large
exact case
rw[HLl]
exact case
have ieq: i=k:= by
  simp at case
  exact Nat.eq_of_le_of_lt_succ case hi
rw[ieq]
simp only [List.get!_eq_getD]
rw[List.getD_append_right]
rw[HLl]
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le]
dsimp[K]
rw [@Set.toFinset_union]
calc
  ((Ord.get! (k+1)).C.verts.toFinset ∪ Hi.verts.toFinset).card
  ≥ ( Hi.verts.toFinset).card:= by
    gcongr
    simp
  _≥ m:= by
    apply (Ord.get! (k+1)).H_Order
    exact hHi
rw[HLl ]





lemma set_disjoint_left
(v: V)
(T S: Set V)
(disj: Disjoint S T)
(hv: v∈ S)
:
v∉ T:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine Set.not_disjoint_iff.mpr ?_
  use v
exact h2 disj

lemma set_disjoint_right
(v: V)
(S T: Set V)
(disj: Disjoint S T)
(hv: v∈ T)
:
v∉ S:= by
by_contra cont
have h2: ¬ (Disjoint S T):= by
  refine Set.not_disjoint_iff.mpr ?_
  use v
exact h2 disj



lemma path_forest_support_iff
(F1: PathForest iV iSP H)
(x: V)
:
x∈  {v | ∃ Pi ∈ F1.P, v ∈ Pi.Pa.Wa.support}
↔
∃  (i :ℕ ), i< F1.P.length ∧  x∈  {v | v ∈ (F1.P.get! i).Pa.Wa.support}
:= by
constructor
intro h
simp at h
simp
rcases h with ⟨Pi, hPi, hx⟩
have hjex: ∃ (j: Fin (F1.P.length)), F1.P.get j=Pi:= by
  exact List.mem_iff_get.mp hPi
rcases hjex with ⟨j, hj⟩
use j
constructor
exact j.isLt
have h4: F1.P.get! ↑j=F1.P.get j:= by
  simp
  apply List.getD_eq_get
rw[h4]
rw[hj]
exact hx

intro h
simp at h
simp
rcases h with ⟨i, hi, hx⟩
use (F1.P.get! i)
constructor
have h4: F1.P.getD i default=F1.P.get ⟨i, ?_⟩ := by
  apply List.getD_eq_get
simp
rw[h4]
refine List.get_mem F1.P i ?h.left.refine_1
exact hi
exact hx



lemma path_forest_support_iff_neg
(F1: PathForest iV iSP H)
(x: V)
:
x∉   {v | ∃ Pi ∈ F1.P, v ∈ Pi.Pa.Wa.support}
↔
∀   (i :ℕ ), i< F1.P.length →   x∉   {v | v ∈ (F1.P.get! i).Pa.Wa.support}
:= by
have h1:_:=by exact path_forest_support_iff iV iSP F1 x
by_contra cont
simp at cont
push_neg at cont
simp at h1
simp_all only [gt_iff_lt]
unhygienic
  aesop_cases
    cont
· simp_all only [iff_true]
  unhygienic
    with_reducible
      aesop_destruct_products
  simp_all only
· simp_all only [iff_true]
  unhygienic
    with_reducible
      aesop_destruct_products
  simp_all only

/-
-- used
lemma add_Ver_to_M_list_starts
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)

(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k+1→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k+1)
(Ord_length: Ord.length> k+1)
(Ver_length: Ver.length> k)
(S_length: S.length> k+1)
:
∃ (HL: List  (Subgraph G)),
(HL.length=k+1)
∧ (cut_dense_list! iSub HL γ (k+1))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! (i+1)).verts)
∧ (∀ (i: ℕ ), i<k+1→ (S.get! (i))∈ (HL.get! i).verts)
∧ (∀ i < k + 1, HL.get! i ≤ H)--need to add extra assumptions for this

:= by
-/

/-
unfold Vertex_list_in_clump_list_BSetPlusM at VerInOrd


induction' k with k IH
let K:Subgraph G:= (Ord.get! 0).C
use [K]
constructor
exact rfl
constructor
intro i hi
--cutdense
sorry
constructor
intro i hi

sorry
sorry
-----------induction-------------

have LM_length'': LM.length> k+1:= by
  exact Nat.lt_of_succ_lt LM_length
have LM_length': LM.length> k:= by
  exact Nat.lt_of_succ_lt LM_length''
have Ord_length'': Ord.length> k+1:= by
  exact Nat.lt_of_succ_lt Ord_length
have Ord_length': Ord.length> k:= by
  exact Nat.lt_of_succ_lt Ord_length''
have Ver_length': Ver.length> k:= by
  exact Nat.lt_of_succ_lt Ver_length
have S_length'': S.length> k+1:= by
  exact Nat.lt_of_succ_lt S_length
have S_length': S.length> k:= by
  exact Nat.lt_of_succ_lt S_length''
have hSinLM: ∀ i < k+1, S.get! (i) ∈ (LM.get! i).verts:= by
  intro i hi
  apply hSML i
  exact Nat.lt_add_right 1 hi
have ind: _:= by exact IH hSinLM LM_length'' Ord_length'' Ver_length' S_length''

rcases ind with ⟨HL, HLl, Hcd,VerHL,SHL , InH ⟩


have hkl: k<Ord.length:= by exact Ord_length'
have hkm: k<LM.length:= by exact LM_length'
have hkm': k+1<LM.length:= by exact LM_length''




have MinOrd:LM.get! k ∈ (Ord.get! k).M:= by
  unfold M_list_in_clump_list at LM_in_M
  have h2:_:= by exact  LM_in_M k  hkl
  simp at h2
  simp
  have h3: LM.getD k default=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM default hkm
  have h4: LM.getD k ⊥=LM.get ⟨k, hkm ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm
  rw[h3]
  rw[h4] at h2
  exact h2


have MinOrd:Ver.get! k ∈  BSetPlusM (Ord.get! k) ∩ BSetPlusM (Ord.get! (k + 1)):= by
  apply VerInOrd
  exact Nat.lt_sub_of_add_lt Ord_length''
have MinOrd2:Ver.get! k ∈  BSetPlusM (Ord.get! (k+1)):= by
  exact Set.mem_of_mem_inter_right MinOrd

have Hi_ex: ∃ (Hi: Subgraph G), Hi∈  (Ord.get! (k+1)).H ∧ Ver.get! k∈ Hi.verts:= by
  sorry
rcases Hi_ex with ⟨Hi, hHi, hVerHi⟩


let K:Subgraph G:= (Ord.get! (k+1)).C ⊔Hi
have Kcut_dense: cut_dense G K γ:= by
  apply clump_add_Hi_cut_dense
  exact mPositive
  exact pPositive
  exact κPositive
  --γ ≥ 16 * κ ^ (2 * (100 * (Ord.get! k).k).factorial)
  exact iSub
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

let HL':List (Subgraph G):= HL++[K]
use HL'

constructor
dsimp[HL']
simp
exact HLl


-----cutdense
constructor
dsimp[HL']
intro i hi
by_cases case: i<k+1
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
apply   Hcd i case

have hi2: i=k+1:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! (k+1) =[K].get! ((k+1)-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default (k+1)
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
exact Kcut_dense

constructor
----Ver in HL
dsimp[HL']
intro i hi
by_cases case: i<k
have h1: (HL ++ [K]).get! (i+1) =HL.get! (i+1) := by
  simp
  apply List.getD_append
  calc
    i+1 < k+1:= by
      exact Nat.add_lt_add_right case 1
    _= HL.length:= by
      exact HLl.symm
rw[h1]
exact VerHL i case

have hi2: i=k:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! (k+1) =[K].get! ((k+1)-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default (k+1)
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]
exact Set.mem_union_right (Ord.get! (k + 1)).C.verts hVerHi

----S in HL
constructor
dsimp[HL']
intro i hi
by_cases case: i<k+1
have h1: (HL ++ [K]).get! i =HL.get! i := by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id HLl.symm)
rw[h1]
exact SHL i case

have hi2: i=k+1:= by exact Nat.eq_of_lt_succ_of_not_lt hi case
rw[hi2]

have h1: (HL ++ [K]).get! (k+1) =[K].get! ((k+1)-HL.length) := by
  simp only [List.get!_eq_getD]
  apply List.getD_append_right HL [K] default (k+1)
  exact Nat.le_of_eq HLl
rw[HLl] at h1
simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, List.getD_cons_zero] at h1
rw [@List.get!_cons_zero] at h1
rw[h1]
dsimp[K]

have hSinMM: S.get! (k+1) ∈(LM.get! (k+1)).verts:= by
  apply hSML (k+1)
  exact lt_add_one (k + 1)

unfold M_list_in_clump_list at LM_in_M
have hMM: LM.get! (k + 1) ∈ (Ord.get! (k + 1)).M:= by
  have h55:_:=by
    apply LM_in_M (k + 1)
    exact Ord_length''
  simp at h55
  simp
  have h3: LM.getD (k + 1) default=LM.get ⟨(k + 1), hkm' ⟩:= by
    exact List.getD_eq_get LM default hkm'
  have h4: LM.getD (k + 1) ⊥=LM.get ⟨(k + 1), hkm' ⟩:= by
    exact List.getD_eq_get LM ⊥ hkm'
  rw[h3]
  rw[h4] at h55
  exact h55
have In_C:(LM.get! (k + 1)).verts⊆ (Ord.get! (k + 1)).C.verts:= by
  sorry
exact Set.mem_union_left Hi.verts (In_C hSinMM)
--in H
sorry





--used
lemma add_Ver_to_M_list_starts_alt
(H: Subgraph G)
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k+1+1→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k+1+1)
(Ord_length: Ord.length> k+1+1)
(Ver_length: Ver.length> k+1)
(S_length: S.length> k+1+1)
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list! iSub HL γ (k))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! (i)).verts)
∧ (∀ (i: ℕ ), i<k→ (S.tail.get! (i))∈ (HL.get! i).verts)
∧ (∀ i < k , HL.get! i ≤ H)
∧ (∀ (i: ℕ ), i<k→ (HL.get! i).verts.toFinset.card≥ m)

:=by
have hex:_:= by
  apply add_Ver_to_M_list_starts _  _ iSub  H Ord Ver S LM LM_in_M VerInOrd (k+1) _ LM_length Ord_length Ver_length S_length
  use γ
  exact κPositive
  exact pPositive
  exact mPositive
  exact hSML




rcases hex with ⟨HL, HLl, Hcd,VerHL,SHL , InH ⟩
use HL.tail

have htail_get: ∀ i < k, (HL.tail).get! i = HL.get! (i+1):= by
  intro i hi
  simp
  sorry
have stail_get: ∀ i < k, (S.tail).get! i = S.get! (i+1):= by
  intro i hi
  simp
  sorry

constructor
sorry
constructor
intro i hi
rw[htail_get i hi]
apply Hcd
simp
exact Nat.lt_add_right 1 hi

constructor
intro i hi
rw[htail_get i hi]
apply VerHL
exact Nat.lt_add_right 1 hi

constructor
intro i hi
rw[htail_get i hi]
rw[stail_get i hi]
apply SHL (i+1)
simp
exact Nat.lt_add_right 1 hi

sorry








/-
lemma set_disjoint_to_tail_disjoint
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1}⊆ Fb)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by

intro i j hi hj
unfold tail_disjoint_imp

apply Fb_disj_to_tail_disj

exact (F2.P.get! j).Pa.Wa_Is_Path
calc
  {v | v ∈ (F1.P.get! i).Pa.Wa.support} \ {(F2.P.get! j).s}
  ⊆ {v | v ∈ (F1.P.get! i).Pa.Wa.support} := by
    exact Set.diff_subset {v | v ∈ (F1.P.get! i).Pa.Wa.support} {(F2.P.get! j).s}
  _⊆ {v:V| v∈ Path_forest_support iV iSP F1}:= by
    simp
    unfold Path_forest_support
    simp
    intro a ha
    have h78:F1.P.get! i ∈ F1.P:= by
      simp
      have h2: F1.P.getD i default=F1.P.get ⟨ i,_⟩:= by
        refine List.getD_eq_get F1.P default ?_
        rw[F1.P_length ]
        exact Nat.lt_of_lt_of_le hi F1k
      rw[h2]
      exact
        List.get_mem F1.P i
          (Eq.mpr (id (congrArg (fun _a ↦ i < _a) F1.P_length)) (Nat.lt_of_lt_of_le hi F1k))
    use F1.P.get! i
  _⊆ Fb:= by
    exact F1_in_Fb

apply F2_avoids_Fb
exact hj




lemma single_path_forest_tail_disjoint
(F1 : PathForest iV iSP H)
(k: ℕ )
(F1k: F1.k≥ k)
:
( ∀(i j: ℕ ), (i< j)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
:= by
intro i j hi hj
have hpathsdisjoint:_:=by exact F1.Paths_disjoint
unfold paths_disjoint at hpathsdisjoint
unfold tail_disjoint_imp
have hj': j<F1.k:= by
  exact Nat.lt_of_lt_of_le hj F1k
have h2:_:= by exact hpathsdisjoint i j hi hj'
simp at h2
intro x hx hx2
have hh2: x∈ {v | v ∈ (F1.P.get! j).Pa.Wa.support}:= by
  simp
  exact List.mem_of_mem_tail hx2
have hh3: x∈ {v | v ∈ (F1.P.get! i).Pa.Wa.support}:= by
  simp
  exact hx
have neg: ¬ (Disjoint {v | v ∈ (F1.P.get! i).Pa.Wa.support} {v | v ∈ (F1.P.get! j).Pa.Wa.support}):= by
  refine Set.Nonempty.not_disjoint ?_
  refine Set.inter_nonempty.mpr ?_
  use x
exact neg (hpathsdisjoint i j hi hj')




-/


-/
