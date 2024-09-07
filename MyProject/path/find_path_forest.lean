import MyProject

--import MyProject.path_forests_join
import MyProject.path.long_path_forest
import MyProject.path.path_forests

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 370000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
/-variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))-/
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )





def Path_forest_avoids!
{H: Subgraph G}
(Fo: PathForest iV iSP H)
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
(Fo:  PathForest iV iSP H)
(l k: ℕ )
:=
∀ (i: ℕ ), i< k→ (Fo.P.get! i).Pa.Wa.length≥ l



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



lemma path_forest_specified_ends_simplified_prefix
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m p pr: ℕ )
(Fb: Set V)

(SinH: vertex_list_in_graph_list iV iSub S HL_init (k))---change
(EinH: vertex_list_in_graph_list iV iSub E HL_init (k-1))---change

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length≥ k)
(Elength: E.length≥  k)
(HLlength: HL_init.length≥  k)



(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL_init.get! i≤ H))


(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)


(cutdense: cut_dense_list! iSub HL_init p (k))---change--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list!  iSub HL_init Fb p m (k) pr) ---change--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
--new
(kBig: k>1)
(mbig1: 172 * p * p * k ≤ m / (2 * pr) + 8 * p * (2 * k))
(pPositive: p>0)
(Fbcard2: Fb.toFinset.card≤ (41 * p * k))
(mbig2: m * 3 ≥ p * k * 16 + p ^ 2 * k * 328 + m / (pr * 2))
:

∃ (Fo: PathForest iV iSP H),
Fo.S= S.take k
∧ Fo.E= E.take k
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids! iV iSP Fo Fb (k)---change
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
--∧ Path_forest_avoids! iV iSP Fo {v:V|v∈ (List.drop k S)} k---change
--∧ Path_forest_avoids!  iV iSP Fo {v:V|v∈ (List.drop k E)} k---change
∧ Fo.S.length=k
∧ Fo.E.length=k
:= by

have Hkex: ∃ (Hk: Subgraph G),
  S.get! (k-1) ∈ Hk.verts
  ∧ E.get! (k-1) ∈ Hk.verts
  ∧ cut_dense G Hk p
  ∧ Hk.verts.toFinset.card≥ 3*m
  := by sorry
rcases Hkex with ⟨Hk, hHks, hHke, hHkcutdense, hHkorder⟩
have hHkintersect: (8 * p * Fb.toFinset.card + (m / (2 * pr) + 8 * p * (2 * k))≤ Hk.verts.toFinset.card):= by
  calc
    Hk.verts.toFinset.card≥ 3*m:= by exact hHkorder
    _≥ 8 * p * (41 * p * k) + (m / (2 * pr) + 8 * p * (2 * k)):= by
      ring_nf
      exact mbig2
    _≥ 8 * p * Fb.toFinset.card + (m / (2 * pr) + 8 * p * (2 * k)):= by
      gcongr



let HL:List (Subgraph G):= HL_init.set (k-1) Hk

have HLget: ∀ (i: ℕ ), (i<k-1)→ HL.get! i= HL_init.get! i:= by
  intro i hi
  dsimp[HL]
  have hi2: i<HL_init.length:=by
    calc
      i< k-1:= by exact hi
      _≤ k:= by simp
      _≤ HL_init.length:= by exact HLlength
  have hi1: i<(HL_init.set (k-1) Hk).length:=by
    simp
    exact hi2
  have get1: (HL_init.set (k-1) Hk).get ⟨ i, hi1⟩=(HL_init.set (k-1) Hk).get! i:= by
    simp
    exact (List.getD_eq_get (HL_init.set (k - 1) Hk) default hi1).symm
  have get2: (HL_init).get ⟨ i, hi2⟩=(HL_init).get! i:= by
    simp
    symm
    apply List.getD_eq_get
  rw[get1.symm, get2.symm]
  refine List.get_set_ne HL_init ?h Hk hi1
  exact Ne.symm (Nat.ne_of_lt hi)


have HLgetk: HL.get! (k-1)= Hk:= by
  dsimp[HL]
  have hi1:  (k-1)<(HL_init.set (k-1) Hk).length:=by
    simp
    calc
      k-1<  k:= by
        rw [@tsub_lt_self_iff]
        constructor
        exact Nat.zero_lt_of_lt kBig
        simp
      _≤ HL_init.length:= by
        exact HLlength

  have get1: (HL_init.set (k-1) Hk).get ⟨  (k-1), hi1⟩=(HL_init.set (k-1) Hk).get!  (k-1):= by
    simp only [ List.get!_eq_getD]
    symm
    apply List.getD_eq_get
  rw[get1.symm]
  apply List.get_set_eq

have SinH: vertex_list_in_graph_list iV iSub S HL (k):= by
  intro i hi
  by_cases hh:i<k-1
  rw[HLget i hh]
  apply SinH i
  exact hi
  simp only [not_lt ] at hh
  have ieq: i=k-1:= by
    refine Nat.le_antisymm ?h₁ hh
    exact Nat.le_sub_one_of_lt hi
  rw[ieq, HLgetk]
  exact hHks--

have EinH: vertex_list_in_graph_list iV iSub E HL (k):= by
  intro i hi
  by_cases hh:i<k-1
  rw[HLget i hh]
  apply EinH i
  exact hh
  simp only [not_lt ] at hh
  have ieq: i=k-1:= by
    apply Nat.le_antisymm
    exact Nat.le_sub_one_of_lt hi
    exact hh
  rw[ieq, HLgetk]
  exact hHke--

have HLlength: HL.length≥  k:= by
  dsimp[HL]
  simp
  exact HLlength

have HL_in_H: ∀ (i: ℕ  ), i<k-1→  (HL.get! i≤ H):=by
  intro i hi
  rw[HLget i hi]
  apply HL_in_H i
  exact Nat.lt_of_lt_pred hi

have cutdense: cut_dense_list! iSub HL p (k):= by
  intro i hi
  by_cases hh:i<k-1
  rw[HLget i hh]
  apply cutdense i
  exact hi
  simp only [not_lt ] at hh
  have ieq: i=k-1:= by
    apply Nat.le_antisymm
    exact Nat.le_sub_one_of_lt hi
    exact hh
  rw[ieq, HLgetk]
  exact hHkcutdense--

have Fbcard: small_intersection_list!  iSub HL Fb p m (k) pr:= by
  intro i hi
  by_cases hh:i<k-1
  rw[HLget i hh]
  apply Fbcard i
  exact hi
  simp only [not_lt ] at hh
  have ieq: i=k-1:= by
    apply Nat.le_antisymm
    exact Nat.le_sub_one_of_lt hi
    exact hh
  rw[ieq, HLgetk]
  calc
    8 * p * (Fb ∩ Hk.verts).toFinset.card + (m / (2 * pr) + 8 * p * (2 * k))
    ≤
    8 * p * (Fb).toFinset.card + (m / (2 * pr) + 8 * p * (2 * k)):= by
      gcongr
      simp
    _≤ Hk.verts.toFinset.card:= by
      exact hHkintersect


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
    apply List.IsPrefix.get_eq
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
  apply Nat.sub_one_lt_of_le
  exact kPositive
  simp

have happly:_:= by
  apply path_forest_specified_ends_altk iV iSub  H S' E' HL' (k) (k) --_ _ _ _ _ _ _ _ _ --Fb

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
  rw[HLget i hi]
  rw[Eget i hi]
  apply EinH i hi



  --S E disjoint
  apply List.disjoint_of_subset_left
  exact Ssublist
  apply List.disjoint_of_subset_right
  exact Esublist
  exact SE_Disjoint

  ---------lengths------
  rw[S'_length];
  rw[E'_length];
  rw[S'_length];
  rw[E'_length];
  rw[HL'_length];



  ----HL in H-----------
  intro i hi
  rw[HLget i]
  apply HL_in_H i
  exact hi
  calc
    i<k-1 :=by exact hi
    _≤ k:=by simp
  --


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



rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh, hFoi⟩
--let Pk: SubgraphPath_implicit G:= (Fo.P.get! (0))
--rcases Pkex with ⟨Pk, hPks, hPke⟩
--let P':= Fo.P++[Pk]


--let F:PathForest iV iSP H:= ⟨ S.take k, E.take k,  Fo.P, k, ?_, ?_, ?_, ?_, ?_⟩



use Fo

constructor
exact hFoa
constructor
exact hFob
constructor
exact hFoc
constructor
exact hFod

constructor
intro i hi
apply hFoe
exact Nat.lt_of_lt_of_eq hi (id hFoc.symm)

constructor
exact hFof




constructor
rw[hFoa]
dsimp[S']
simp
exact Slength

rw[hFob]
dsimp[E']
simp
exact Elength



----------------------------------------------------------------------------------------------------------------------------------------------




--Used
lemma long_path_forest_specified_ends_simplified_altnum
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k m p pr κ : ℕ )
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
(κPositive: κ >0)
--(prPositive: pr>0)
(mggp: m ≥ 18 * p)
(κprop: 8 * p * k * m ≤ κ * (m / (2 * pr)))
:
∃ (Fo: PathForest iV iSP H),
(Fo.S= S.take k)
∧  (Fo.E=  E.take k)
∧ Fo.k=k
∧ Fo.P.length=k
--∧ Path_forest_avoids iV iSP Fo Fb
∧ Path_forest_avoids! iV iSP Fo Fb (k)---change
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
--∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
--∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long!  iV iSP Fo (m / pr / (40 * p)) (k)

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
  apply long_path_forest_specified_ends iV iSub iSP H S' E' HL' (k) (k) --_ _ _ _ _ _ _ _ _ --Fb

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
  rw[S'_length];
  rw[E'_length];
  rw[S'_length];
  rw[E'_length];
  rw[HL'_length];




  ----HL in H-----------
  intro i hi
  rw[HLget i]
  apply HL_in_H i
  calc
    i<k-1 :=by exact hi
    _≤ k:=by simp
  calc
    i<k-1 :=by exact hi
    _≤ k:=by simp


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



rcases happly with ⟨Fo, hFoa, hFob, hFoc, hFod, hFoe, hFof, hFog, hFoh, hFoi, hFoj⟩


use Fo


constructor
exact hFoa
constructor
exact hFob
constructor
exact hFoc
constructor
exact hFod

constructor
intro i hi
apply hFoe
exact Nat.lt_of_lt_of_eq hi (id hFoc.symm)

constructor
intro i hi
apply hFoh
rw[hFoc]
exact hi





constructor
rw[hFoa]
dsimp[S']
simp
exact Slength

rw[hFob]
dsimp[E']
simp
exact Elength


    --
