import MyProject

--import MyProject.path_forests_join
import MyProject.long_path_forest
import MyProject.path_forest.path_forests

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




structure PathForest' (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P (k))--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P (k))--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P (k-1))--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P (k))  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)



def Path_forest_avoids!
{H: Subgraph G}
(Fo: PathForest' iV iSP H)
(Fb: Set V)
(k : ℕ )
:=
∀ (i: ℕ ), i< k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)




def cut_dense_list!
(HL: List (Subgraph G))
(p k: ℕ )
:=∀(i: ℕ ), (i<k)→  (cut_dense G  (HL.get! i) p)

def small_intersection_list!
(HL: List (Subgraph G))
(Fb: Set V)
(p m k pr: ℕ )
--(k: ℕ )
:=∀(i: ℕ ), (i<k)→
(8*p*
(Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))≤ (HL.get! i).verts.toFinset.card
)


def Path_forest_long!
{H: Subgraph G}
(Fo: PathForest' iV iSP H)
(l k: ℕ )
:=
∀ (i: ℕ ), i< k→ (Fo.P.get! i).Pa.Wa.length≥ l


lemma SubgraphPathImplicitExistence
(G: SimpleGraph V)
(s e: V)
:
∃ (P: SubgraphPath_implicit G), P.s=s∧  P.e=e∧ P.Pa.Wa.support=[s,e]
:= by
sorry

lemma sparse_family_monotone
(F F': Finset (Subgraph G))
(sparse: family_sparse  κ m F)
(contained: F'⊆ F)
:
family_sparse  κ m F'
:= by
intro A B h1 h2 h3
apply sparse
exact contained h1
exact contained h2
repeat assumption

lemma order_ge_m_family_monotone
(F F': Finset (Subgraph G))
(sparse: HOrder_ge_m_Family  F m)
(contained: F'⊆ F)
:
HOrder_ge_m_Family  F' m
:= by
intro A h1
apply sparse
exact contained h1
repeat assumption


def Path_forest_support'
{H: Subgraph G}
(Fo: PathForest' iV iSP H)
: Set V
:={v: V| ∃ (Pi: SubgraphPath_implicit G), Pi∈ Fo.P∧  (v∈ Pi.Pa.Wa.support)}



lemma path_forest_specified_ends_simplified_prefix
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m : ℕ )
(Fb: Set V)

(SinH: vertex_list_in_graph_list iV iSub S HL (k))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k-1))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length≥ k)
(Elength: E.length≥  k)
(HLlength: HL.length≥  k)



(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))


(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)


(cutdense: cut_dense_list! iSub HL p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list!  iSub HL Fb p m (k) pr) ---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
--new
(kBig: k>1)
(mbig1: 172 * p * p * k ≤ m / (2 * pr) + 8 * p * (2 * k))
:

∃ (Fo: PathForest' iV iSP H),
Fo.S= S.take k
∧ Fo.E= E.take k
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids! iV iSP Fo Fb (k-1)---change
∧ (Path_forest_support' iV iSP Fo ).toFinset.card≤ 41*p*k
--∧ Path_forest_avoids! iV iSP Fo {v:V|v∈ (List.drop k S)} k---change
--∧ Path_forest_avoids!  iV iSP Fo {v:V|v∈ (List.drop k E)} k---change
∧ Fo.S.length=k
∧ Fo.E.length=k
:= by

have kPositive: k>0:= by
  exact Nat.zero_lt_of_lt kBig
let HL':= List.take (k) HL
have HL'_length: HL'.length=k:= by
  exact List.length_take_of_le HLlength
let S':= List.take (k) S
have S'_length: S'.length=k:= by
  exact List.length_take_of_le Slength
let E':= List.take (k) E
have E'_length: E'.length=k:= by
  exact List.length_take_of_le Elength




have HLget: ∀ (i: ℕ ), (i<k)→ HL'.get! i= HL.get! i:= by
  intro i hi
  dsimp[HL']
  have hi1: i<(List.take (k) HL).length:=by
    dsimp[HL'] at HL'_length
    rw[HL'_length]
    exact hi
  have hi2: i<HL.length:=by
    exact Nat.lt_of_lt_of_le hi HLlength
  have hte: (List.take (k ) HL).get ⟨ i, hi1⟩= HL.get ⟨ i, hi2⟩:= by
    refine List.IsPrefix.get_eq ?h hi1
    exact List.take_prefix (k ) HL
  have hte2: (List.take (k ) HL).get ⟨ i, hi1⟩= (List.take (k ) HL).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k ) HL) default hi1).symm
  have hte3:HL.get ⟨ i, hi2⟩= HL.get! i:= by
    simp
    exact (List.getD_eq_get HL default hi2).symm
  rw[hte2.symm, hte3.symm, hte]

have Sget: ∀ (i: ℕ ), (i<k)→ S'.get! i= S.get! i:= by
  intro i hi
  dsimp[S']
  have hi1: i<(List.take (k ) S).length:=by
    dsimp[S'] at S'_length
    rw[S'_length]
    exact hi
  have hi2: i<S.length:=by
    exact Nat.lt_of_lt_of_le hi Slength
  have hte: (List.take (k ) S).get ⟨ i, hi1⟩= S.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k ) S
  have hte2: (List.take (k ) S).get ⟨ i, hi1⟩= (List.take (k ) S).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k ) S) default hi1).symm
  have hte3:S.get ⟨ i, hi2⟩= S.get! i:= by
    simp
    exact (List.getD_eq_get S default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have Eget: ∀ (i: ℕ ), (i<k)→ E'.get! i= E.get! i:= by
  intro i hi
  dsimp[E']
  have hi1: i<(List.take (k ) E).length:=by
    dsimp[E'] at E'_length
    rw[E'_length]
    exact hi
  have hi2: i<E.length:=by
    exact Nat.lt_of_lt_of_le hi Elength
  have hte: (List.take (k ) E).get ⟨ i, hi1⟩= E.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k ) E
  have hte2: (List.take (k ) E).get ⟨ i, hi1⟩= (List.take (k ) E).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k) E) default hi1).symm
  have hte3:E.get ⟨ i, hi2⟩= E.get! i:= by
    simp
    exact (List.getD_eq_get E default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have HLget2: ∀ (i: Fin (HL'.length) ),  HL'.get i=HL.get! i:= by
  intro i
  have h2: i.1<k:= by
    rw[HL'_length.symm]
    exact i.2

  have h1:HL'.get i=HL'.get! i:= by
    simp
    symm
    apply List.getD_eq_get
  rw[h1]
  rw[HLget i.1 h2]




have Esublist: E' ⊆ E:= by
  dsimp[E']
  exact List.take_subset (k ) E
have Ssublist:  S' ⊆ S:= by
  dsimp[S']
  exact List.take_subset (k ) S
have Hsublist:  HL' ⊆ HL:= by
  dsimp[HL']
  exact List.take_subset (k ) HL


have Esublist2: List.Sublist E' E  := by
  dsimp[E']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k ) E
have Ssublist2: List.Sublist S' S  := by
  dsimp[S']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k ) S
have HLsublist2: List.Sublist HL' HL  := by
  dsimp[HL']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k ) HL

have kg: k>k-1:= by
  refine Nat.sub_one_lt_of_le ?h₀ ?h₁
  exact kPositive
  simp

have happly:_:= by
  apply path_forest_specified_ends_altk iV iSub  H S' E' HL' (k-1) (k) --_ _ _ _ _ _ _ _ _ --Fb

  /-apply sparse_family_monotone
  exact HL_sparse
  intro x hx
  simp
  simp at hx
  exact Hsublist hx
  --exact HL_sparse. prove monoinicity
  apply order_ge_m_family_monotone
  exact HL_order
  intro x hx
  simp
  simp at hx
  exact Hsublist hx-/
  ---also for gem families


  --vertex_list_in_graph_list iV iSub S HL HL.length
  dsimp[HL', S']
  intro i hi
  have ilk: i<k:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Sget i ilk]
  apply SinH i ilk

  --vertex_list_in_graph_list iV iSub E' HL' HL'.length
  dsimp[HL', E']
  intro i hi
  have ilk: i<k:= by
    exact Nat.lt_trans hi kg
  rw[HLget i ilk]
  rw[Eget i ilk]
  apply EinH i hi


  --S E disjoint
  apply List.disjoint_of_subset_left
  exact Ssublist
  apply List.disjoint_of_subset_right
  exact Esublist
  exact SE_Disjoint

  ---------lengths------
  rw[S'_length]; exact kg
  rw[E'_length]; exact kg
  rw[S'_length];
  rw[E'_length];
  rw[HL'_length]; exact kg



  ----HL in H-----------
  intro i
  rw[HLget2 i]
  apply HL_in_H i
  calc
    _<HL'.length:= by exact i.2
    _=k:= by exact HL'_length


  --exact List.Nodup.sublist HLsublist2 HL_nodup

  rw[HL'_length]
  intro i hi
  rw[Sget i]
  apply SoutsideFb
  exact hi
  exact hi

  --rw[HL'_length]
  intro i hi
  rw[Eget i]
  apply EoutsideFb
  exact Nat.lt_trans hi kg
  exact Nat.lt_trans hi kg

  exact List.Nodup.sublist Ssublist2 Snodup
  exact List.Nodup.sublist Esublist2 Enodup

  simp
  intro i
  rw[HLget2]
  apply cutdense
  calc
    _<HL'.length:= by exact i.2
    _=k:= by exact HL'_length

  intro i
  rw[HLget2]
  calc
    8 * p * (Fb ∩ (HL.get! ↑i).verts).toFinset.card
    + (172*p*p*k)
    ≤
    8*p*
    (Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))
    := by
      gcongr 8*p*(Fb∩ (HL.get! i).verts).toFinset.card+(?_)

    _≤ (HL.get! i).verts.toFinset.card
    := by
      apply Fbcard i.1
      calc
        _<HL'.length:= by exact i.2
        _=k:= by exact HL'_length


  --m≥ 18*p
  --exact mggp
  --exact κPositive
  exact pPositive

  exact iSP



rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh⟩
have Pkex: _:=by
  apply SubgraphPathImplicitExistence G (Fo.S.get! (k-1))  (Fo.E.get! (k-1))
rcases Pkex with ⟨ Pk, sPk, ePk, supPk⟩
--let Pk: SubgraphPath_implicit G:= (Fo.P.get! (0))
--rcases Pkex with ⟨Pk, hPks, hPke⟩
let P':= Fo.P++[Pk]

have hgeteq: ∀ (i: ℕ ), (i<k-1)→  P'.get! i= Fo.P.get! i:= by
  intro i hi
  dsimp[P']
  simp
  rw[List.getD_append]
  rw[hFod]
  exact hi

--let F:PathForest iV iSP H:= ⟨ S.take k, E.take k,  Fo.P, k, ?_, ?_, ?_, ?_, ?_⟩

let F:PathForest' iV iSP H:= ⟨ S.take k, E.take k,  P', k, ?_, ?_, ?_, ?_, ?_⟩





use F

constructor
exact rfl
constructor
dsimp[F]
constructor
exact rfl
constructor
dsimp[F]
dsimp[P']
simp
rw[hFod]
exact Nat.sub_add_cancel kPositive
--exact hFod
constructor
intro i hi
dsimp[F]
rw[hgeteq i hi]

apply hFoe
exact Nat.lt_of_lt_of_eq hi (id hFoc.symm)

constructor
have heq:{v:V|v∈  (Path_forest_support' iV iSP F)}⊆ {v:V|v∈ (Path_forest_support iV iSP Fo)}∪ {(Fo.S.get! (k-1)),  (Fo.E.get! (k-1))}:= by
  intro v hv
  simp at hv
  dsimp[F] at hv
  unfold Path_forest_support' at hv
  simp
  simp at hv
  dsimp[P'] at hv
  simp at hv
  rcases hv with ⟨Pi, hPi1, hPi2 ⟩
  rcases hPi1 with case|case
  right
  right
  unfold Path_forest_support
  simp
  use Pi
  rw[case] at hPi2
  rw[supPk] at hPi2
  simp at hPi2
  rcases hPi2 with case1|case1
  left
  exact case1
  right
  left
  exact case1




/-  unfold Path_forest_support'
  unfold Path_forest_support
  dsimp[F]
  dsimp[P']
  --dsimp[Pk]
  have h1: Pk∈ Fo.P:= by
    dsimp[Pk]
    have h2: Fo.P.get! 0 =Fo.P.get ⟨ 0, ?_⟩:= by
      simp
      refine List.getD_eq_get Fo.P default ?_
    rw[h2]
    refine List.get_mem Fo.P 0 ?refine_1
    rw[hFod]
    refine Nat.zero_lt_sub_of_lt ?refine_1.h
    exact kBig

  ext v
  simp
  constructor
  intro hh
  rcases hh with ⟨Pi, hPi, hv⟩
  use Pi
  constructor
  rcases hPi with case|case
  exact case
  rw[case]
  exact h1
  exact hv
  intro hh
  rcases hh with ⟨Pi, hPi, hv⟩
  use Pi
  constructor
  left
  exact hPi
  exact hv-/

sorry
--rw[heq]
--calc
--  _≤ 41 * p * (k-1):=by exact hFof
--  _≤ 41 * p * k:=by
--    gcongr


constructor
exact S'_length
exact E'_length

sorry
sorry
/-
intro i hi
rw[hgeteq i hi]
rw[hFoc.symm] at hi
rw[(Fo.Starts_equal i hi).symm]
rw[hFoa]
--rw [Sget i]
--rw[hFoc.symm]


intro i hi
rw[hgeteq i hi]
rw[hFoc.symm] at hi
rw[(Fo.Ends_equal i hi).symm]
rw[hFob]
--rw [Eget i]
--rw[hFoc.symm]-/


intro i hi
rw[hgeteq i hi]
--rw[hFoc.symm]
apply Fo.Graphs_equal
rw[hFoc]
exact hi


intro i j hi hj'
by_cases hj: j<k-1
have hii: i<k-1:= by
  exact Nat.lt_trans hi hj
rw[hgeteq i hii]
rw[hgeteq j hj]
apply  Fo.Paths_disjoint
exact hi
rw[hFoc]
exact hj

simp only [not_lt] at hj
have hjeq: j=k-1:= by sorry
rw[hjeq]
rw[hjeq] at hi
rw[hgeteq i hi]
have hgetk: P'.get! (k - 1)=Pk:= by sorry
rw[hgetk]
rw[supPk]
unfold Path_forest_avoids at hFog

have hsin: Fo.S.get! (k-1)∈ {v | v ∈ List.drop (k - 1) S'}:= by
  dsimp[S']
  simp
  have h2: Fo.S.getD (k - 1) default=(List.drop (k - 1) (List.take k S)).getD 0 default:= by
    rw[List.drop_getD]

/-
dsimp[P']
simp
rw[hFod]
exact Nat.sub_add_cancel kPositive



----------------------------------------------------------------------------------------------------------------------------------------------




--Used
lemma long_path_forest_specified_ends_simplified_altnum
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m p pr: ℕ )
(Fb: Set V)

(HL_sparse: family_sparse  κ m (HL.toFinset) )
(HL_order: HOrder_ge_m_Family (HL.toFinset) (m/pr))

(SinH: vertex_list_in_graph_list iV iSub S HL (k))---change
(EinH: vertex_list_in_graph_list iV iSub E HL (k))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length≥  k)
(Elength: E.length≥  k )
(HLlength: HL.length≥  k)


--(HLlength: HL.length> k)
(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))

(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)
(HL_nodup: HL.Nodup)




(cutdense: cut_dense_list! iSub HL p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list! iSub HL Fb p m (k) pr)
  --∀(i: ℕ ), (i<k)→
  --(8*p*
  --(Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))≤ (HL.get! i).verts.toFinset.card
  --))
--small_intersection_list!  iSub HL Fb p m (k))---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
(pPositive: p>0)
--(Fbcard: small_intersection_list  HL Fb p (m +8*p*(2*1*kmax)))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
--new assumptions:
(kPositive: k>0)
--(prPositive: pr>0)
(mggp: m ≥ 18 * p)
(κprop: 8 * p * k * m ≤ κ * (m / (2 * pr)))
:
∃ (Fo: PathForest' iV iSP H),
(Fo.S= S.take k)
∧  (Fo.E=  E.take k)
∧ Fo.k=k
∧ Fo.P.length=k
--∧ Path_forest_avoids iV iSP Fo Fb
∧ Path_forest_avoids! iV iSP Fo Fb (k-1)---change
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
--∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
--∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long!  iV iSP Fo (m / pr / (40 * p)) (k-1)

∧ Fo.S.length=k
∧ Fo.E.length=k
--∧ Path_forest_in_HL iV iSub iSP HL Fo



:= by

--have Slength: S.length> k:=by exact Slen--rw [Slen]; exact lt_add_one k
--have Elength: E.length> k:= by exact Elen--rw [Elen]; exact lt_add_one k

--have  Smaxlength: S.length≤  k+1:= by exact Nat.le_of_eq Slen
--have Emaxlength: E.length≤  k+1:=by exact Nat.le_of_eq Elen


let HL':= List.take (k) HL
have HL'_length: HL'.length=k:= by
  exact List.length_take_of_le HLlength
let S':= List.take (k) S
have S'_length: S'.length=k:= by
  exact List.length_take_of_le Slength
let E':= List.take (k) E
have E'_length: E'.length=k:= by
  exact List.length_take_of_le Elength




have HLget: ∀ (i: ℕ ), (i<k)→ HL'.get! i= HL.get! i:= by
  intro i hi
  dsimp[HL']
  have hi1: i<(List.take (k) HL).length:=by
    dsimp[HL'] at HL'_length
    rw[HL'_length]
    exact hi
  have hi2: i<HL.length:=by
    exact Nat.lt_of_lt_of_le hi HLlength
  have hte: (List.take (k ) HL).get ⟨ i, hi1⟩= HL.get ⟨ i, hi2⟩:= by
    refine List.IsPrefix.get_eq ?h hi1
    exact List.take_prefix (k ) HL
  have hte2: (List.take (k ) HL).get ⟨ i, hi1⟩= (List.take (k ) HL).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k ) HL) default hi1).symm
  have hte3:HL.get ⟨ i, hi2⟩= HL.get! i:= by
    simp
    exact (List.getD_eq_get HL default hi2).symm
  rw[hte2.symm, hte3.symm, hte]

have Sget: ∀ (i: ℕ ), (i<k)→ S'.get! i= S.get! i:= by
  intro i hi
  dsimp[S']
  have hi1: i<(List.take (k ) S).length:=by
    dsimp[S'] at S'_length
    rw[S'_length]
    exact hi
  have hi2: i<S.length:=by
    exact Nat.lt_of_lt_of_le hi Slength
  have hte: (List.take (k ) S).get ⟨ i, hi1⟩= S.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k ) S
  have hte2: (List.take (k ) S).get ⟨ i, hi1⟩= (List.take (k ) S).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k ) S) default hi1).symm
  have hte3:S.get ⟨ i, hi2⟩= S.get! i:= by
    simp
    exact (List.getD_eq_get S default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have Eget: ∀ (i: ℕ ), (i<k)→ E'.get! i= E.get! i:= by
  intro i hi
  dsimp[E']
  have hi1: i<(List.take (k ) E).length:=by
    dsimp[E'] at E'_length
    rw[E'_length]
    exact hi
  have hi2: i<E.length:=by
    exact Nat.lt_of_lt_of_le hi Elength
  have hte: (List.take (k ) E).get ⟨ i, hi1⟩= E.get ⟨ i, hi2⟩:= by
    apply List.IsPrefix.get_eq
    exact List.take_prefix (k ) E
  have hte2: (List.take (k ) E).get ⟨ i, hi1⟩= (List.take (k ) E).get!  i:= by
    simp
    exact (List.getD_eq_get (List.take (k) E) default hi1).symm
  have hte3:E.get ⟨ i, hi2⟩= E.get! i:= by
    simp
    exact (List.getD_eq_get E default hi2).symm
  rw[hte2.symm, hte3.symm, hte]


have HLget2: ∀ (i: Fin (HL'.length) ),  HL'.get i=HL.get! i:= by
  intro i
  have h2: i.1<k:= by
    rw[HL'_length.symm]
    exact i.2

  have h1:HL'.get i=HL'.get! i:= by
    simp
    symm
    apply List.getD_eq_get
  rw[h1]
  rw[HLget i.1 h2]




have Esublist: E' ⊆ E:= by
  dsimp[E']
  exact List.take_subset (k ) E
have Ssublist:  S' ⊆ S:= by
  dsimp[S']
  exact List.take_subset (k ) S
have Hsublist:  HL' ⊆ HL:= by
  dsimp[HL']
  exact List.take_subset (k ) HL


have Esublist2: List.Sublist E' E  := by
  dsimp[E']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k ) E
have Ssublist2: List.Sublist S' S  := by
  dsimp[S']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k ) S
have HLsublist2: List.Sublist HL' HL  := by
  dsimp[HL']
  apply List.IsPrefix.sublist
  exact List.take_prefix (k ) HL

have kg: k>k-1:= by
  refine Nat.sub_one_lt_of_le ?h₀ ?h₁
  exact kPositive
  simp

have happly:_:= by
  apply long_path_forest_specified_ends iV iSub iSP H S' E' HL' (k-1) (k) --_ _ _ _ _ _ _ _ _ --Fb

  apply sparse_family_monotone
  exact HL_sparse
  intro x hx
  simp
  simp at hx
  exact Hsublist hx
  --exact HL_sparse. prove monoinicity
  apply order_ge_m_family_monotone
  exact HL_order
  intro x hx
  simp
  simp at hx
  exact Hsublist hx
  ---also for gem families


  --vertex_list_in_graph_list iV iSub S HL HL.length
  dsimp[HL', S']
  intro i hi
  have ilk: i<k:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Sget i ilk]
  apply SinH i ilk

  --vertex_list_in_graph_list iV iSub E' HL' HL'.length
  dsimp[HL', E']
  intro i hi
  have ilk: i<k:= by
    dsimp[HL'] at HL'_length
    rw[HL'_length] at hi
    exact hi
  rw[HLget i ilk]
  rw[Eget i ilk]
  apply EinH i ilk

  --S E disjoint
  apply List.disjoint_of_subset_left
  exact Ssublist
  apply List.disjoint_of_subset_right
  exact Esublist
  exact SE_Disjoint

  ---------lengths------
  rw[S'_length]; exact kg
  rw[E'_length]; exact kg
  rw[S'_length];
  rw[E'_length];
  rw[HL'_length]; exact kg



  ----HL in H-----------
  intro i
  rw[HLget2 i]
  apply HL_in_H i
  calc
    _<HL'.length:= by exact i.2
    _=k:= by exact HL'_length


  exact List.Nodup.sublist HLsublist2 HL_nodup

  rw[HL'_length]
  intro i hi
  rw[Sget i]
  apply SoutsideFb
  exact hi
  exact hi

  rw[HL'_length]
  intro i hi
  rw[Eget i]
  apply EoutsideFb
  exact hi
  exact hi

  exact List.Nodup.sublist Ssublist2 Snodup
  exact List.Nodup.sublist Esublist2 Enodup

  simp
  intro i
  rw[HLget2]
  apply cutdense
  calc
    _<HL'.length:= by exact i.2
    _=k:= by exact HL'_length

  intro i
  rw[HLget2]
  calc
    8 * p * (Fb ∩ (HL.get! ↑i).verts).toFinset.card
    + (8 * p * k * m / κ+8*p*(2*1*(k)))
    ≤
    8*p*
    (Fb∩ (HL.get! i).verts).toFinset.card+(m/(2*pr) +8*p*(2*(k)))
    := by
      gcongr 8*p*(Fb∩ (HL.get! i).verts).toFinset.card+(?_ +8*p*(2*(k)))
      refine Nat.div_le_of_le_mul ?bc.bc.a
      exact κprop
      --172 * p * p * (k + 1) ≤ m + 8 * p * (2 * (k + 1))

    _≤ (HL.get! i).verts.toFinset.card
    := by
      apply Fbcard i.1
      calc
        _<HL'.length:= by exact i.2
        _=k:= by exact HL'_length


  --m≥ 18*p
  exact mggp
  exact κPositive
  exact pPositive



rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh, hFoi⟩
have Pk: SubgraphPath_implicit G:=by exact (Fo.P.get! (k-1))
--rcases Pkex with ⟨Pk, hPks, hPke⟩
let P':= Fo.P++[Pk]

have hgeteq: ∀ (i: ℕ ), (i<k-1)→  P'.get! i= Fo.P.get! i:= by
  intro i hi
  dsimp[P']
  simp
  rw[List.getD_append]
  rw[hFod]
  exact hi

--let F:PathForest iV iSP H:= ⟨ S.take k, E.take k,  Fo.P, k, ?_, ?_, ?_, ?_, ?_⟩

let F:PathForest' iV iSP H:= ⟨ S.take k, E.take k,  P', k, ?_, ?_, ?_, ?_, ?_⟩





use F

constructor
exact rfl
constructor
dsimp[F]
constructor
exact rfl
constructor
dsimp[F]
dsimp[P']
simp
rw[hFod]
exact Nat.sub_add_cancel kPositive
--exact hFod
constructor
intro i hi
dsimp[F]
rw[hgeteq i hi]

apply hFoe
exact Nat.lt_of_lt_of_eq hi (id hFoc.symm)

constructor
intro i hi
rw[hgeteq i hi]
apply hFoh
rw[hFoc]
exact hi

constructor
exact S'_length
exact E'_length


intro i hi
rw[hgeteq i hi]
rw[hFoc.symm] at hi
rw[(Fo.Starts_equal i hi).symm]
rw[hFoa]
--rw [Sget i]
--rw[hFoc.symm]


intro i hi
rw[hgeteq i hi]
rw[hFoc.symm] at hi
rw[(Fo.Ends_equal i hi).symm]
rw[hFob]
--rw [Eget i]
--rw[hFoc.symm]


intro i hi
rw[hgeteq i hi]
--rw[hFoc.symm]
apply Fo.Graphs_equal
rw[hFoc]
exact hi


intro i j hi hj
have hii: i<k-1:= by
  exact Nat.lt_trans hi hj
rw[hgeteq i hii]
rw[hgeteq j hj]
apply  Fo.Paths_disjoint
exact hi
rw[hFoc]
exact hj

dsimp[P']
simp
rw[hFod]
exact Nat.sub_add_cancel kPositive


    --
-/
