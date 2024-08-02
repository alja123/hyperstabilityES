import MyProject

import MyProject.path_forests_join

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 50000

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

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}




lemma path_forest_specified_ends_simplified
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)
(HLlength: HL.length> k)



(HL_in_H: ∀ (i: ℕ  ), i<k→  (HL.get! i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (k))
(EoutsideFb: vertex_list_outside_set iV E Fb (k))

(Snodup: S.Nodup)
(Enodup: E.Nodup)


(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
:= by

sorry

def Path_forest_long
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(l: ℕ )
:=
∀ (i: ℕ ), i< Fo.k→ (Fo.P.get! i).Pa.Wa.length≥ l


lemma long_path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(HL_sparse: family_sparse  κ m (HL.toFinset) )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long  iV iSP Fo (m/40*p)
:= by
--#check clump_path_sequence_gives_path
sorry



lemma find_pairs_in_M_list
(Ord: List (Clump G p m κ pr h))
(Ver: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)--possibly just subgraph list??
(k: ℕ )
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

sorry


lemma add_Ver_to_M_list
(Ord: List (Clump G p m κ pr h))
(Ver: List V)
(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(k:ℕ )
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list  HL κ)
∧ (∀ (i: ℕ ), i<k→ (LM.get! i)≤  (HL.get! i))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! i).verts)
∧ vertex_list_in_graph_list iV iSub Ver HL k
:= by

sorry


lemma clump_path_sequence_gives_path
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV α KFam)
(k: ℕ )
:
Has_length_d_path (Clump_Family_Union KFam) (h*m)
:=by


have ex_pairs: _:= by
  apply find_pairs_in_M_list iI iV iSub Seq.Ord Seq.Ver Seq.LM Seq.LM_in_M k

have ex_HS:_:=by
  apply add_Ver_to_M_list iI iV iSub Seq.Ord Seq.Ver Seq.LM Seq.LM_in_M k

have ex_HE:_:=by
  apply add_Ver_to_M_list iI iV iSub Seq.Ord Seq.Ver.tail Seq.LM Seq.LM_in_M k


rcases ex_pairs with ⟨S, E, hS, hE, hSE, hSVer, hEVer, hSNoDup, hENoDup, hSInLM, hEInLM⟩
rcases ex_HS with ⟨HS, hHS, hcutdenseS, hLMS, hVerS, Ver_in_HS⟩
rcases ex_HE with ⟨HE, hHE, hcutdenseE, hLME, hVerE, Ver_in_HL⟩




have SinH: vertex_list_in_graph_list iV iSub S HS HS.length:= by
  sorry

have EinH: vertex_list_in_graph_list iV iSub E HE HE.length:= by
  sorry

have VerinHS: vertex_list_in_graph_list iV iSub Seq.Ver HS HS.length:= by
  sorry--This should match lemma earlier
have VerinHE: vertex_list_in_graph_list iV iSub Seq.Ver HE HE.length:= by
  sorry--This should match lemma earlier



have HS_in_H: ∀ (i: Fin (HS.length) ), (HS.get i≤ H):= by
  sorry

have HE_in_H: ∀ (i: Fin (HE.length) ), (HE.get i≤ H):= by
  sorry


have LM_cut_dense:  cut_dense_list  Seq.LM κ:= by
  sorry
have LM_in_H: ∀ (i: Fin (Seq.LM.length) ), (Seq.LM.get i≤ H):= by
  sorry
have SinLM: vertex_list_in_graph_list iV iSub S Seq.LM Seq.LM.length:= by
  sorry
have EinLM: vertex_list_in_graph_list iV iSub E Seq.LM Seq.LM.length:= by
  sorry

let Fb: Set V:= {v: V|v∈ E}

have SoutsideFb: vertex_list_outside_set iV S Fb (HS.length):= by
  sorry
have Ver_EoutsideFb: vertex_list_outside_set iV Seq.Ver Fb (HS.length):= by
  sorry

have Fbcard: small_intersection_list  HS Fb κ (172*κ*κ*k):= by
  sorry

have VerNoDup: Seq.Ver.Nodup:= by
  exact Seq.VerNoDup

have klek: k≤ k:= by
  exact Nat.le_refl k



have hF1Ex: _:= by
  apply path_forest_specified_ends iV iSub iSP H Seq.Ver S HS  k k _ _ _ _ _ _ _ _ _ Fb
  repeat assumption
  --
  sorry; sorry; sorry; sorry; sorry; assumption

rcases hF1Ex with ⟨F1, hF1a, hF1b, hF1c, hF1d, hF1e, hF1f, hF1g, hF1h⟩


let Fb2: Set V:= {v: V|v∈ S}∪ {v:V| v∈ Path_forest_support iV iSP F1}

have SoutsideFb: vertex_list_outside_set iV E Fb2 (HE.length):= by
  sorry
have Ver_EoutsideFb: vertex_list_outside_set iV Seq.Ver Fb2 (HE.length):= by
  sorry

have Fbcard: small_intersection_list  HE Fb2 κ (172*κ*κ*k):= by
  sorry


have hF2Ex: _:= by
  apply path_forest_specified_ends iV iSub iSP H E Seq.Ver HE  k k _ _ _ _ _ _ _ _ _ Fb2
  repeat assumption
  --
  sorry; sorry; sorry; sorry; sorry; assumption

rcases hF2Ex with ⟨ F2, hF2a , hF2b, hF2c, hF2d, hF2e, hF2f, hF2g, hF2h⟩


let Fb3: Set V:=  {v:V| v∈ Path_forest_support iV iSP F1}∪ {v:V| v∈ Path_forest_support iV iSP F2}

have SoutsideFb: vertex_list_outside_set iV S Fb3 (Seq.LM.length):= by
  sorry
have EoutsideFb: vertex_list_outside_set iV E Fb3 (Seq.LM.length):= by
  sorry

have Fbcard: small_intersection_list  Seq.LM Fb3 κ (172*κ*κ*k):= by
  sorry

have LM_sparse: family_sparse k k Seq.LM.toFinset:= by
  sorry

have hF3Ex: _:= by
  apply long_path_forest_specified_ends iV iSub iSP H S E.tail Seq.LM  k k _ _ _ _ _ _ _ _ _ _ Fb3
  repeat assumption
  --
  sorry; sorry; sorry; sorry; sorry; assumption

rcases hF3Ex with ⟨F3, hF3a, hF3b, hF3c, hF3d, hF3e, hF3f, hF3g, hF3h, hF3i⟩



have Path_ex: _:= by
  apply join_three_forests iV iSP H F2 F1 F3 _ _ _ k k
  sorry;sorry;sorry;sorry;sorry;sorry;sorry;sorry;sorry;
  sorry;sorry;sorry;sorry;sorry;
  --F1.E = F2.S
  rw[hF1a, hF2b]
  rw[hF1b, hF3a]
  rw[hF2a, hF3b]

  --

rcases Path_ex with ⟨P, hP1⟩

sorry






 /-
lemma Dense_list_implies_path_sequence_with_M
(KFam: Finset (Clump G p m κ pr h))
(KFamNonempty: KFam.Nonempty)
--(t: ℕ)
--(ht: t≤ h*pr)
--(narrow: Clump_family_narrow KFam)
(separated: Clump_family_separated KFam)
(has_dense_sets: family_contains_dense_list p m κ pr h α iI KFam  )
:
Nonempty (ClumpPathSequence iI iV κ KFam)
:=by-/

/-def family_sparse
(β m : ℕ )(MFam: Finset (Subgraph G))
:=
∀ (M1 M2: Subgraph G),
(M1∈ MFam)
→ (M2∈ MFam)
→ (M1≠ M2)
→ ((β *(M1.verts∩ M2.verts).toFinset.card)≤  m)



structure ClumpPathSequence
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: family_sparse β m (LM.toFinset) )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)
  (hlengthM: LM.length=Ord.length)
  (hlengthVer: Ver.length=Ord.length-1)
  --(LM_NoDup: LM.Nodup)-/


/-lemma path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length> k)
(Elength: E.length> k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length> k)
(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(Fb: Set V)

(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p (172*p*p*kmax))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
∧ (Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
:= by-/

/-

lemma join_three_forests
(H: Subgraph G)
(F1 F2 F3: PathForest iV iSP H)
(hF1_F2: F1.E=F2.S)
(hF2_F3: F2.E=F3.S)
(hF3_F1: F3.E=F1.S.tail)

(t tmax: ℕ )

( hdisj11: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
( hdisj22: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)))
( hdisj33: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)))
( hdisj12: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)))
( hdisj21: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)))
( hdisj13: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)))
( hdisj31: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)))
( hdisj23: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)))
( hdisj32: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)))

(Slength: tmax < F1.S.length)

(ht: t<tmax)
(pos1: tmax<F1.k)
(pos2: tmax<F2.k)
(pos3: tmax<F3.k)


:
∃ (P: SubgraphPath H (F1.S.get! 0) (F3.E.get! (t))),
{v:V|v∈ P.Wa.support}=Path_forest_support_until_t iV iSP  F1 (t+1)∪ Path_forest_support_until_t iV iSP  F2 (t+1)∪ Path_forest_support_until_t iV iSP  F3 (t+1)
-/


/-simp only [Walk.mem_support_append_iff]
have h5:  {v | v ∈ P.Wa.support ∨ v ∈ Q.Wa.support}= {v | v ∈ P.Wa.support} ∪ {v | v ∈ Q.Wa.support}:= by

rw[h5]
rw[hP1, hQ2]

unfold Path_forest_support_until_t
ext v
constructor
intro h
simp
simp at h

aesop
-/

--#check SimpleGraph.append_paths



/-
structure SubgraphPath_implicit
(G: SimpleGraph V) where
  H: Subgraph G
  s: V
  e: V
  Pa: SubgraphPath H s e



variable (iSP:Inhabited (SubgraphPath_implicit   G) )



def starts_equal
(S : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s)


def ends_equal
(E : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((E.get! i)=(P.get! i).e)

def graphs_equal
(H : Subgraph G)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((P.get! i).H≤ H)


def paths_disjoint
 (P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i j: ℕ ), i< j→ j< k→ (Disjoint {v:V|v∈ (P.get! i).Pa.Wa.support} {v:V|v∈ (P.get! j).Pa.Wa.support})


structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P k)  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)

def Path_forest_support
{H: Subgraph G}
(Fo: PathForest iV iSP H)
: Set V
:={v: V| ∃ (Pi: SubgraphPath_implicit G), Pi∈ Fo.P∧  (v∈ Pi.Pa.Wa.support)}


def Path_forest_avoids
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: Set V)
:=
∀ (i: ℕ ), i< Fo.k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)

def Path_forest_avoids_list
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: List V)
:=
∀ (i: ℕ ), i< Fo.k→ (List.Disjoint ((Fo.P.get! i).Pa.Wa.support) Fb)


def cut_dense_list
(HL: List (Subgraph G))
(p: ℕ )
:=∀(i: Fin (HL.length)),  (cut_dense G  (HL.get i) p)

def small_intersection_list
(HL: List (Subgraph G))
(Fb: Set V)
(p e: ℕ )
--(k: ℕ )
:=∀(i: Fin (HL.length)),
(8*p*
(Fb∩ (HL.get i).verts).toFinset.card+e≤ (HL.get i).verts.toFinset.card
)

def vertex_list_in_graph_list
(S: List V)
(HL: List (Subgraph G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∈ (HL.get! i).verts


def vertex_list_outside_set
(S: List V)
(Fb: Set V)
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∉ Fb

structure SubgraphWalk
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_In_H: Wa.toSubgraph≤ H

structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H

-/
