--import MyProject

import hyperstabilityES.lemmas.brooms
  --import hyperstabilityES.lemmas.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 200000

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

-/

/-

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
:
∃ (P: SubgraphPath H u v), P.Wa.length≥ (m/(40*p)) ∧ (Disjoint {v:V| v∈ P.Wa.support}  Fb)
:= by
-/



lemma finsets4card_alt
(A B C D T: Finset V)
:
((A∪ B∪ C∪ D)∩ T).card≤ (A∩ T).card+(B∩ T).card+C.card+D.card:=by
calc
((A∪ B∪ C∪ D)∩ T).card
≤ (A ∩ T ∪ (B∩ T) ∪ C ∪ D).card:= by
  gcongr
  intro x hx
  simp
  simp at hx
  simp_all only [gt_iff_lt,
    and_true]
_≤ (A∩ T).card+(B∩ T).card+C.card+D.card:= by
  exact card_union_4 (A ∩ T) (B∩ T) C D
/-
lemma sets4card
(A B C D T: Set V)
:
((A∪ B∪ C∪ D)∩ T).toFinset.card≤ (A∩ T).toFinset.card+B.toFinset.card+C.toFinset.card+D.toFinset.card:=by
calc
((A∪ B∪ C∪ D)∩ T).toFinset.card
_= ((A.toFinset ∪ B.toFinset∪ C.toFinset∪ D.toFinset)∩ T.toFinset).card:= by
  simp
_≤ (A.toFinset ∩ T.toFinset).card+B.toFinset.card
+C.toFinset.card
+D.toFinset.card:= by
  apply finsets4card
_=(A∩ T).toFinset.card+B.toFinset.card+C.toFinset.card+D.toFinset.card:=by
  congr; simp



lemma sets4cardinequality
(A B C D T: Set V)
(a b c d: ℕ)
(ha: (A∩ T).toFinset.card≤ a)
(hb: B.toFinset.card≤ b)
(hc: C.toFinset.card≤ c)
(hd: D.toFinset.card≤ d)
:
((A∪ B∪ C∪ D)∩ T).toFinset.card≤ a+b+c+d:=by
calc
((A∪ B∪ C∪ D)∩ T).toFinset.card
≤ (A∩ T).toFinset.card+B.toFinset.card+C.toFinset.card+D.toFinset.card:= by
  apply sets4card
_≤ a+b+c+d:= by
  gcongr

-/


lemma finsets4cardinequality_alt
(A B C D T: Finset V)
(a b c d: ℕ)
(ha: (A∩ T).card≤ a)
(hb: (B∩ T).card≤ b)
(hc: C.card≤ c)
(hd: D.card≤ d)
:
((A∪ B∪ C∪ D)∩ T).card≤ a+b+c+d:=by
calc
((A∪ B∪ C∪ D)∩ T).card
≤ (A∩ T).card+(B∩ T).card+C.card+D.card:= by
  apply finsets4card_alt
_≤ a+b+c+d:= by
  gcongr



def Path_forest_long
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(l: ℕ )
:=
∀ (i: ℕ ), i< Fo.k→ (Fo.P.get! i).Pa.Wa.length≥ l


def Path_forest_in_HL
{H: Subgraph G}
(HL: List (Subgraph G))
(Fo: PathForest iV iSP H)
 :=
∀ (i: ℕ ), i< Fo.k→ {v:V|v∈ (Fo.P.get! i).Pa.Wa.support}⊆ (HL.get! i).verts




lemma long_path_forest_specified_ends
(H: Subgraph G)
(S E: List V)
(HL: List (Subgraph G))
(k kmax: ℕ )

(HL_sparse: family_sparse  κ m (HL.toFinset) )
(HL_order: HOrder_ge_m_Family (HL.toFinset) (m/pr))

(SinH: vertex_list_in_graph_list iV iSub S HL (HL.length))
(EinH: vertex_list_in_graph_list iV iSub E HL (HL.length))

(SE_Disjoint : List.Disjoint S E)


(Slength: S.length≥  k)
(Elength: E.length≥  k)

(Smaxlength: S.length≤  kmax)
(Emaxlength: E.length≤  kmax)

(HLlength: HL.length≥  k)
--(HL_in_H: ∀ (i: Fin (HL.length) ), (HL.get i≤ H))
(HL_in_H: ∀ (i: ℕ  ), i<kmax-1→  (HL.get! i≤ H))--can delete -1

(Fb: Set V)
(HL_nodup: HL.Nodup)
(SoutsideFb: vertex_list_outside_set iV S Fb (HL.length))
(EoutsideFb: vertex_list_outside_set iV E Fb (HL.length))

(Snodup: S.Nodup)
(Enodup: E.Nodup)

(hkMax: k≤ kmax)

(cutdense: cut_dense_list  HL p )--∀(i: ℕ ), (i< k)→ (cut_dense G  (HL.get! i) p))
(Fbcard: small_intersection_list  HL Fb p ((8*p*kmax*m/κ)  +8*p*(2*1*kmax)))--∀(i: ℕ ), (i< k)→ (8*p*(((HL.get! i).verts∩ Fb).toFinset.card≤ (HL.get! i).verts.toFinset.card)))
--(mggp: m ≥ 18 * p)
(mggpr:  m / pr ≥ 18 * p)
:
∃ (Fo: PathForest iV iSP H),
Fo.S=S
∧ Fo.E=E
∧ Fo.k=k
∧ Fo.P.length=k
∧ Path_forest_avoids iV iSP Fo Fb
--∧ (Path_forest_support iV iSP Fo )⊆  41*p*k
∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
∧ Path_forest_avoids  iV iSP Fo {v:V|v∈ (List.drop k E)}
∧ Path_forest_long  iV iSP Fo (m / pr / (40 * p))
∧ Path_forest_in_HL iV iSub iSP HL Fo
∧ (graphs_equal iSP H Fo.P (min (k) (kmax-1)))
:= by

induction' k with k hd1
let S0: List V:=[]
let E0: List V:=[]
let P0: List (SubgraphPath_implicit G):=[]
--have Seq: S=[]:= by
--  exact List.length_eq_zero.mp Slength
--have Eeq: E=[]:= by
--  exact List.length_eq_zero.mp Elength

have Starts_equal: starts_equal iV iSP S P0 0:= by
  unfold starts_equal
  intro i hi1
  by_contra
  exact Nat.not_succ_le_zero i hi1

have Ends_equal: ends_equal iV iSP E P0 0:= by
  unfold ends_equal
  intro i hi1
  by_contra
  exact Nat.not_succ_le_zero i hi1

have Graphs_equal: graphs_equal  iSP H P0 (0-1):= by
  unfold graphs_equal
  intro i hi1
  by_contra
  exact Nat.not_succ_le_zero i hi1

have Paths_disjoint: paths_disjoint  iSP  P0 0:= by
  unfold paths_disjoint
  intro i j hi1 hji
  by_contra
  exact Nat.not_succ_le_zero j hji


have h3: P0.length = 0:= by exact rfl

let F0:PathForest iV iSP H:= ⟨S, E, P0, 0, Starts_equal, Ends_equal, Graphs_equal, Paths_disjoint , h3⟩
use F0
repeat constructor;exact rfl
constructor

intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi

--constructor
--unfold Path_forest_support
--simp
--exact filter_False univ

constructor
intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi
constructor

intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi

constructor
intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi

constructor
intro i hi
dsimp[F0] at hi
by_contra
exact Nat.not_succ_le_zero i hi

intro i hi
--dsimp[F0] at hi
simp at hi
------------induction

have hex: ∃ (Fo: PathForest iV iSP H),Fo.S=S
  ∧ Fo.E=E∧ Fo.k=k
  ∧ (Fo.P.length=k)
  ∧ (Path_forest_avoids iV iSP Fo Fb)
  --∧ ((Path_forest_support iV iSP Fo ).toFinset.card≤ 41*p*k)
  ∧ Path_forest_avoids iV iSP Fo {v:V|v∈ (List.drop k S)}
  ∧ Path_forest_avoids iV iSP Fo {v: V|v∈ (List.drop k E)}
  ∧ Path_forest_long  iV iSP Fo (m / pr / (40 * p))
  ∧ Path_forest_in_HL iV iSub iSP HL Fo
  ∧ (graphs_equal iSP H Fo.P (min (k) (kmax-1)))
  := by


    apply hd1
    --
    exact Nat.le_of_succ_le Slength
    exact Nat.le_of_succ_le Elength
    exact Nat.le_of_succ_le HLlength
    exact Nat.le_of_succ_le hkMax--


  --intro i hi
  --apply SinH
  --exact Nat.lt_add_right 1 hi
  --intro i hi
  --apply EinH
  --exact Nat.lt_add_right 1 hi


--rcases hex with ⟨Fo, ⟨FS, ⟨FE, ⟨Fk⟩⟩⟩⟩
rcases hex with ⟨Fo, ⟨FS, ⟨FE, ⟨Fk, ⟨ FFoL, ⟨ FAvoid,  ⟨ FAvoidS, FAvoidE, FLong, FinHL, FinH⟩    ⟩ ⟩ ⟩⟩⟩⟩

--let k:ℕ := Fo.k


have kUb2: k< HL.length:= by
  exact   HLlength
have hKLget2: (HL.get! (k ))=HL.get ⟨k, kUb2⟩:= by
  simp
  exact List.getD_eq_get HL default kUb2

have kUB_S: k< S.length:= by
  exact  Slength
have hSget: (S.get! (k ))=S.get ⟨k, kUB_S⟩:= by
  simp
  exact List.getD_eq_get S default kUB_S

have kUB_E: k< E.length:= by
  exact  Elength
have hEget: (E.get! (k ))=E.get ⟨k, kUB_E⟩:= by
  simp
  exact List.getD_eq_get E default kUB_E


--let Fb2: Set V:= Fb∪ {v: V| ∃ (i: ℕ ), i< k∧ v∈ (Fo.P.get! i).Pa.Wa.support}∪ {v | v ∈ List.drop (k + 1) S}∪ {v | v ∈ List.drop (k + 1) E}

/-have hbridge: {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}={v: V| ∃ (i: ℕ ), i< k∧ v∈ (Fo.P.get! i).Pa.Wa.support}:=by
  ext x
  simp
  constructor
  intro h
-/

let Fb2: Set V:= Fb∪ {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support} ∪ {v | v ∈ List.drop (k + 1) S}∪ {v | v ∈ List.drop (k + 1) E}
--{v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}

let Fb2Old: Set V:= Fb∪ {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support} ∪ {v | v ∈ List.drop (k + 1) S}∪ {v | v ∈ List.drop (k + 1) E}

have Fb_bridge: {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}⊆ {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}:= by
    simp
    intro a ha ha2 ha3
    use (Fo.P.get! ha)
    constructor
    simp
    have h61: ha< Fo.P.length:= by
      rw[ FFoL]
      exact ha2

    have h71: Fo.P.getD ha default=Fo.P.get ⟨ha, h61⟩:= by
      exact List.getD_eq_get Fo.P default h61
    rw[h71]
    exact List.get_mem Fo.P ha h61

    exact ha3

have Fb_bridge2:{v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}⊆  {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}:= by
  intro a ha
  simp
  simp at ha
  rcases ha with ⟨ Pi, ⟨ hPi1, hPi2⟩ ⟩
  have h1: _:= by
    exact List.mem_iff_get.1 hPi1
  rcases h1 with ⟨i, ⟨hi1, hi2⟩⟩
  use i
  constructor
  calc
    _<Fo.P.length:= by exact i.isLt
    _=k:=by exact FFoL
  let j:ℕ := i
  have h4: Fo.P.get! j=Fo.P.get i:=by
    have h5:j<Fo.P.length:=by exact i.isLt
    have h6: i=⟨j,h5 ⟩:= by exact rfl
    rw[h6]
    exact (get_eq_get2! iSP Fo.P j h5).symm

  rw[h4]
  exact hPi2



have Fb2_eq_old: Fb2=Fb2Old:=by
  dsimp[Fb2, Fb2Old]
  congr
  exact Set.Subset.antisymm Fb_bridge2 Fb_bridge




have exN:∃ (PN: SubgraphPath (HL.get! (k)) (S.get! (k)) (E.get! (k))), PN.Wa.length≥  (m/pr/(40*p)) ∧ (Disjoint ({v | v ∈ PN.Wa.support})  Fb2):=by
  apply Cut_Dense_path_avoiding_connecting_long_2 --_ _ _ p m _ _ _ _ _ _ _ _ Fb2
  repeat assumption

  unfold cut_dense_list at cutdense
  rw[hKLget2]
  apply cutdense

  apply EinH
  exact kUb2

  apply SinH
  exact kUb2

  unfold small_intersection_list at Fbcard
  rw[Fb2_eq_old]
  dsimp [Fb2Old]


  --8 * p *
  --  ((Fb ∪ {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support} ∪ {v | v ∈ List.drop (k + 1) S} ∪ {v | v ∈ List.drop (k + 1) E}) ∩
  --        (HL.get! k).verts).toFinset.card ≤
  --(HL.get! k).verts.toFinset.card
  calc
    _
    =8 * p *
    ((Fb ∪ {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}
    ∪ {v | v ∈ List.drop (k + 1) S}
    ∪ {v | v ∈ List.drop (k + 1) E})
    ∩ (HL.get! k).verts).toFinset.card:= by simp
    _≤ 8 * p * (
    (Fb∩ (HL.get! (k)).verts).toFinset.card
    +
     ({v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}∩(HL.get! (k)).verts).toFinset.card
    +
    kmax
    +
    kmax
    ):=by
      gcongr 4*p*?_
      simp only [List.get!_eq_getD, Set.toFinset_inter, Set.mem_setOf_eq, Set.toFinset_union,
        ]
      apply finsets4cardinequality_alt --_ _ _ _ 1 1 1 1 _ _ _ _
      exact card_le_of_subset fun ⦃a⦄ a ↦ a
      --{v | ∃ i < k, v ∈ (Fo.P.get! i).Pa.Wa.support}.toFinset.card ≤ k * p

      exact card_le_of_subset fun ⦃a⦄ a ↦ a

      calc
        {v | v ∈ List.drop (k + 1) S}.toFinset.card
        =(List.drop (k + 1) S).toFinset.card:= by
          congr
          ext v
          constructor
          intro h
          simp
          simp at h
          exact h
          intro h
          simp
          simp at h
          exact h
        _≤ (List.drop (k + 1) S).length:= by exact List.toFinset_card_le (List.drop (k + 1) S)
        _≤ S.length:= by
          have h3: List.Sublist (List.drop (k + 1) S) S:= by
            exact List.drop_sublist (k + 1) S
          exact List.Sublist.length_le h3
        _≤ kmax:=by exact Smaxlength


      --{v | v ∈ List.drop (k + 1) S}.toFinset.card ≤ k
      calc
        {v | v ∈ List.drop (k + 1) E}.toFinset.card
        =(List.drop (k + 1) E).toFinset.card:= by
          congr
          ext v
          constructor
          intro h
          simp
          simp at h
          exact h
          intro h
          simp
          simp at h
          exact h
        _≤ (List.drop (k + 1) E).length:= by exact List.toFinset_card_le (List.drop (k + 1) E)
        _≤ E.length:= by
          have h3: List.Sublist (List.drop (k + 1) E) E:= by
            exact List.drop_sublist (k + 1) E
          exact List.Sublist.length_le h3
        _≤ kmax:=by exact Emaxlength
    _=8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)
    +8*p*({v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}∩(HL.get! (k)).verts).toFinset.card
    +8*p*(2*1*kmax):=by
      ring_nf
    _≤8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)
    +8*p*kmax*m/κ
    +8*p*(2*1*kmax):=by
      gcongr 8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+?_+8*p*(2*1*kmax)
      unfold family_sparse at HL_sparse
      calc
        8 * p * ({v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support} ∩ (HL.get! k).verts).toFinset.card
        =8 * p * ({v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}.toFinset ∩ (HL.get! k).verts.toFinset).card:=by
          congr
          simp


        _≤ 8 * p * ((Finset.biUnion (Finset.Ico 0 k) (fun x=>(HL.get! x).verts.toFinset)) ∩ (HL.get! k).verts.toFinset).card:=by
          gcongr
          intro w hw
          simp only [Nat.Ico_zero_eq_range, mem_biUnion, mem_range,
            Set.mem_toFinset]
          simp at hw
          rcases hw with ⟨t, hw2t, hw2tt⟩
          use t
          constructor
          exact hw2t
          have h24: {v:V|v∈ (Fo.P.get! t).Pa.Wa.support}⊆ (HL.get! t).verts:= by
            apply  FinHL
            rw[Fk]
            exact hw2t
          have h34:w∈ {v:V|v∈ (Fo.P.get! t).Pa.Wa.support}:= by
            simp
            exact hw2tt
          exact h24 hw2tt


        _=8 * p * ((Finset.biUnion (Finset.Ico 0 k) (fun x=>(HL.get! x).verts.toFinset∩ (HL.get! k).verts.toFinset)) ).card:=by
          congr
          simp
          exact
            biUnion_inter (range k) (fun x ↦ (HL.getD x default).verts.toFinset)
              (HL.getD k default).verts.toFinset
        _≤ 8 * p * (∑  (x∈ Finset.Ico 0 k), (((HL.get! x).verts.toFinset∩ (HL.get! k).verts.toFinset).card)):=by
          gcongr
          exact card_biUnion_le
        _= 8*p*κ*(∑  (x∈ Finset.Ico 0 k), (((HL.get! x).verts.toFinset∩ (HL.get! k).verts.toFinset).card))/κ :=
          by
            apply Nat.eq_div_of_mul_eq_right
            exact Nat.not_eq_zero_of_lt κPositive
            ring_nf


        _=8*p*(κ*∑  (x∈ Finset.Ico 0 k), (((HL.get! x).verts.toFinset∩ (HL.get! k).verts.toFinset).card))/κ:= by
          ring_nf
        _= 8*p*(∑  (x∈ Finset.Ico 0 k), (κ *((HL.get! x).verts.toFinset∩ (HL.get! k).verts.toFinset).card))/κ:=by
          congr
          exact
            mul_sum (Ico 0 k)
              (fun i ↦ ((HL.get! i).verts.toFinset ∩ (HL.get! k).verts.toFinset).card) κ
        _=8*p*(∑  (x∈ Finset.Ico 0 k), (κ *(((HL.get! x).verts∩ (HL.get! k).verts).toFinset).card))/κ:=by
          congr
          simp

        _≤8*p*(∑  (x∈ Finset.Ico 0 k), (m))/κ := by--change m/kmax to m/4*kmax*pr
          gcongr with j hj

          have h91: j< HL.length:= by
              simp at hj
              exact Nat.lt_trans hj kUb2
          have h101: (HL.get! j)=HL.get ⟨j, h91⟩:= by
              simp
              exact List.getD_eq_get HL default h91
          have h52: HL.get! j∈ HL:= by
            rw[h101]
            exact List.get_mem HL j h91
          have h9: k< HL.length:= by
              exact kUb2
          have h10: (HL.get! k)=HL.get ⟨k, h9⟩:= by
              simp
              exact List.getD_eq_get HL default h9
          have h53: HL.get! k∈ HL:= by
            rw[h10]
            exact List.get_mem HL k h9
          apply HL_sparse
          exact List.mem_toFinset.mpr h52
          exact List.mem_toFinset.mpr h53
          simp at hj
          rw[h10, h101]
          by_contra cont
          have h78:HL.get ⟨j, h91⟩ = HL.get ⟨k, h9⟩↔ _=_:=by
            apply  List.Nodup.get_inj_iff
            exact HL_nodup
          have h79: _:=by exact h78.1 cont
          simp at h79
          have h88:j≠ k:= by exact Nat.ne_of_lt hj
          exact h88 h79


        _=8*p*((Finset.Ico 0 k).card*m)/κ:=by
          congr
          exact sum_const_nat fun x ↦ congrFun rfl
        _=8*p*(k*m)/κ:=by
          congr
          rw [Nat.card_Ico]
          simp
        _≤ 8*p*(kmax*m)/κ:=by
          gcongr; exact Nat.le_of_succ_le hkMax
        _=  8*p*kmax*m/κ:=by
          ring_nf

      --
    --_≤8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+m +8*p*(2*1*kmax):=by
    --  gcongr --(4*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+?_)
    --  exact pPositive; exact?
    _=8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+(8*p*kmax*m/κ  +8*p*(2*1*kmax)):=by
      ring_nf
    --_≤ 8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+m +8*p*(2*1*kmax):=by
    --  gcongr; exact Nat.le_of_ble_eq_true rfl
    _=8*p*((Fb∩ (HL.get ⟨ k, kUb2 ⟩ ).verts).toFinset.card)+(8*p*kmax*m/κ +8*p*(2*1*kmax)):= by
      rw[hKLget2]
    _≤ ((HL.get  ⟨ k, kUb2 ⟩ ).verts.toFinset.card):= by
      apply Fbcard ⟨k , kUb2 ⟩

    _= ((HL.get! (k)).verts.toFinset.card):= by
      rw[hKLget2.symm]



  /-calc
    _
    =4 * p *
    ((Fb ∪ {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}
    ∪ {v | v ∈ List.drop (k + 1) S}
    ∪ {v | v ∈ List.drop (k + 1) E})
    ∩ (HL.get! k).verts).toFinset.card:= by simp
    _≤ 4 * p * (
    (Fb∩ (HL.get! (k)).verts).toFinset.card
    +
    41*kmax*p
    +
    kmax
    +
    kmax
    ):=by
      gcongr 4*p*?_
      simp only [List.get!_eq_getD, Set.toFinset_inter, Set.mem_setOf_eq, Set.toFinset_union,
        ]
      apply finsets4cardinequality --_ _ _ _ 1 1 1 1 _ _ _ _
      exact card_le_of_subset fun ⦃a⦄ a ↦ a
      --{v | ∃ i < k, v ∈ (Fo.P.get! i).Pa.Wa.support}.toFinset.card ≤ k * p
      unfold Path_forest_support at FSupport
      --simp
      calc
        {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset.card
        ≤ 41*p*k:= by simp; simp at FSupport; apply FSupport
        _≤ 41*p*kmax:=by gcongr; exact Nat.le_of_succ_le hkMax
      --{v | v ∈ List.drop (k + 1) S}.toFinset.card ≤ k
      --gcongr (40*?_)*?_
      rw[mul_assoc,mul_comm p kmax,mul_assoc]

      calc
        {v | v ∈ List.drop (k + 1) S}.toFinset.card
        =(List.drop (k + 1) S).toFinset.card:= by
          congr
          ext v
          constructor
          intro h
          simp
          simp at h
          exact h
          intro h
          simp
          simp at h
          exact h
        _≤ (List.drop (k + 1) S).length:= by exact List.toFinset_card_le (List.drop (k + 1) S)
        _≤ S.length:= by
          have h3: List.Sublist (List.drop (k + 1) S) S:= by
            exact List.drop_sublist (k + 1) S
          exact List.Sublist.length_le h3
        _≤ kmax:=by exact Smaxlength


      --{v | v ∈ List.drop (k + 1) S}.toFinset.card ≤ k
      calc
        {v | v ∈ List.drop (k + 1) E}.toFinset.card
        =(List.drop (k + 1) E).toFinset.card:= by
          congr
          ext v
          constructor
          intro h
          simp
          simp at h
          exact h
          intro h
          simp
          simp at h
          exact h
        _≤ (List.drop (k + 1) E).length:= by exact List.toFinset_card_le (List.drop (k + 1) E)
        _≤ E.length:= by
          have h3: List.Sublist (List.drop (k + 1) E) E:= by
            exact List.drop_sublist (k + 1) E
          exact List.Sublist.length_le h3
        _≤ kmax:=by exact Emaxlength
    _=4*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+4*p*(41*kmax*p+2*1*kmax):=by
      ring_nf
    _≤4*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+4*p*(41*kmax*p+2*p*kmax):=by
      gcongr --(4*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+?_)
      exact pPositive
    _=4*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+172*p*p*kmax:=by
      ring_nf
    _≤ 8*p*((Fb∩ (HL.get! (k)).verts).toFinset.card)+172*p*p*kmax:=by
      gcongr; exact Nat.le_of_ble_eq_true rfl
    _=8*p*((Fb∩ (HL.get ⟨ k, kUb2 ⟩ ).verts).toFinset.card)+172*p*p*kmax:= by
      rw[hKLget2]
    _≤ ((HL.get  ⟨ k, kUb2 ⟩ ).verts.toFinset.card):= by
      apply Fbcard ⟨k , kUb2 ⟩

    _= ((HL.get! (k)).verts.toFinset.card):= by
      rw[hKLget2.symm]
  -/

  rw[Fb2_eq_old]
  dsimp [Fb2Old]
  simp only [ Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor
  constructor
  constructor
  apply SoutsideFb
  exact kUb2

  intro x hx
  --unfold Path_forest_avoids at FAvoidS
  have h7: S.get! k∈(List.drop k S):= by
    have h9: k+0< S.length:= by
      exact  Slength
    have h10: (S.get! k)=S.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get S default h9
    rw[h10]
    rw[List.get_drop S h9]
    exact List.get_mem (List.drop k S) 0 (List.lt_length_drop S h9)
  have h8: Disjoint {v:V|v∈ (Fo.P.get! x).Pa.Wa.support} {v:V|v∈ (List.drop k S)}:= by
    unfold Path_forest_avoids at FAvoidS
    apply FAvoidS
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  have h72: S.get! k∈{v:V|v∈ (List.drop k S)}:= by
    simp only [Set.mem_setOf_eq]
    exact h7
  have h11: S.get! k ∉ {v: V|v∈ (Fo.P.get! x).Pa.Wa.support}:= by
    by_contra cont
    simp only [ Set.mem_setOf_eq] at cont
    have hneg: ¬(Disjoint {v | v ∈ (Fo.P.get! x).Pa.Wa.support} {v | v ∈ List.drop k S}):= by
      unfold Disjoint
      simp only [Set.le_eq_subset, Set.bot_eq_empty, not_forall, Classical.not_imp]
      use {S.get! k}
      simp only [Set.singleton_subset_iff, Set.mem_empty_iff_false,
        not_false_eq_true, Set.mem_setOf_eq, exists_prop, and_true]
      exact ⟨cont, h72⟩
    simp at hneg
    exact  hneg h8
  simp only [Set.mem_setOf_eq] at h11
  exact h11


  apply getk_nin_dropk
  exact Snodup
  exact  Slength

  have h5: S.get! k∈ S:= by
    have h9: k< S.length:= by
      exact  Slength
    have h10: (S.get! k)=S.get ⟨k, h9⟩:= by
      simp
      exact List.getD_eq_get S default h9
    rw[h10]
    exact List.get_mem S k h9
  have h5: S.get! k∉ E:= by
    exact SE_Disjoint h5
  --have h13: List.Sublist (List.drop (k + 1) E) E:= by
  --  exact List.drop_sublist (k + 1) E
  by_contra cont
  --simp only [List.get!_eq_getD] at cont
  have h5': S.get! k∈  E:= by
    exact List.mem_of_mem_drop cont
  exact h5 h5'
  --------------------E

  rw[Fb2_eq_old]
  dsimp [Fb2Old]
  simp only [ Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor
  constructor
  constructor
  apply EoutsideFb
  exact kUb2

  intro x hx
  have h7: E.get! k∈(List.drop k E):= by
    have h9: k+0< E.length:= by
      exact  Elength
    have h10: (E.get! k)=E.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get E default h9
    rw[h10]
    rw[List.get_drop E h9]
    exact List.get_mem (List.drop k E) 0 (List.lt_length_drop E h9)
  have h8: Disjoint {v:V|v∈ (Fo.P.get! x).Pa.Wa.support} {v:V|v∈ (List.drop k E)}:= by
    unfold Path_forest_avoids at FAvoidE
    apply FAvoidE
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  have h72: E.get! k∈{v:V|v∈ (List.drop k E)}:= by
    simp only [Set.mem_setOf_eq]
    exact h7
  have h11: E.get! k ∉ {v: V|v∈ (Fo.P.get! x).Pa.Wa.support}:= by
    by_contra cont
    simp only [ Set.mem_setOf_eq] at cont
    have hneg: ¬(Disjoint {v | v ∈ (Fo.P.get! x).Pa.Wa.support} {v | v ∈ List.drop k E}):= by
      unfold Disjoint
      simp only [Set.le_eq_subset, Set.bot_eq_empty, not_forall, Classical.not_imp]
      use {E.get! k}
      simp only [Set.singleton_subset_iff, Set.mem_empty_iff_false,
        not_false_eq_true, Set.mem_setOf_eq, exists_prop, and_true]
      exact ⟨cont, h72⟩
    simp at hneg
    exact  hneg h8
  simp only [Set.mem_setOf_eq] at h11
  exact h11




  have h5: E.get! k∈ E:= by
    have h9: k< E.length:= by
      exact  Elength
    have h10: (E.get! k)=E.get ⟨k, h9⟩:= by
      simp
      exact List.getD_eq_get E default h9
    rw[h10]
    exact List.get_mem E k h9
  have h5: E.get! k∉ S:= by
    exact id (List.Disjoint.symm SE_Disjoint) h5
  --have h13: List.Sublist (List.drop (k + 1) E) E:= by
  --  exact List.drop_sublist (k + 1) E
  by_contra cont
  --simp only [List.get!_eq_getD] at cont
  have h5': E.get! k∈  S:= by
    exact List.mem_of_mem_drop cont
  exact h5 h5'

  apply getk_nin_dropk
  exact Enodup
  exact   Elength

    -------------------E S disjoint
  have h5: E.get! k∈ E:= by
    have h9: k< E.length:= by
      exact  Elength
    have h10: (E.get! k)=E.get ⟨k, h9⟩:= by
      simp
      exact List.getD_eq_get E default h9
    rw[h10]
    exact List.get_mem E k h9
  have h5: E.get! k∉ S:= by
    exact id (List.Disjoint.symm SE_Disjoint) h5
  --have h13: List.Sublist (List.drop (k + 1) E) E:= by
  --  exact List.drop_sublist (k + 1) E
  have h6: S.get! k∈ S:= by
    have h9: k< S.length:= by
      exact  Slength
    have h10: (S.get! k)=S.get ⟨k, h9⟩:= by
      simp
      exact List.getD_eq_get S default h9
    rw[h10]
    exact List.get_mem S k h9
  exact ne_of_mem_of_not_mem h6 h5


  have h5: HL.get! k∈ HL:= by
    have h9: k< HL.length:= by
      exact kUb2
    have h10: (HL.get! k)=HL.get ⟨k, h9⟩:= by
      simp
      exact List.getD_eq_get HL default h9
    rw[h10]
    exact List.get_mem HL k h9

  apply HL_order
  simp only [List.mem_toFinset]
  exact h5
  /-calc
    _ ≥ (2*m):= by
      apply HL_order
      simp only [List.mem_toFinset]
      exact h5
    _≥ 1*m:=by gcongr; exact NeZero.one_le
    _=m:= by ring_nf-/
  --m/pr≥ 18*p

  exact mggpr









  /-unfold Path_forest_avoids at FAvoidE
  intro x hx
  have h7: E.get! k∈(List.drop k E):= by
    have h9: k+0< E.length:= by
      exact Nat.lt_of_succ_lt Elength
    have h10: (E.get! k)=E.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get E default h9
    rw[h10]
    rw[List.get_drop E h9]
    exact List.get_mem (List.drop k E) 0 (List.lt_length_drop E h9)

  have h8: (Fo.P.get! x).Pa.Wa.support.Disjoint (List.drop k E):= by
    apply FAvoidE
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  exact id (List.Disjoint.symm h8) h7


  dsimp [Fb2]
  simp only [ Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor
  apply EoutsideFb
  exact kUb2-/



  /-unfold Path_forest_avoids_list at FAvoidS
  intro x hx
  have h7: E.get! k∈(List.drop k E):= by
    have h9: k+0< E.length:= by
      exact Nat.lt_of_succ_lt Elength
    have h10: (E.get! k)=E.get ⟨k+0, h9⟩:= by
      simp
      exact List.getD_eq_get E default h9
    rw[h10]
    rw[List.get_drop E h9]
    exact List.get_mem (List.drop k E) 0 (List.lt_length_drop E h9)

  have h8: (Fo.P.get! x).Pa.Wa.support.Disjoint (List.drop k E):= by
    apply FAvoidE
    exact Nat.lt_of_lt_of_eq hx (id Fk.symm)
  exact id (List.Disjoint.symm h8) h7-/

--have exN:∃ (PN: SubgraphPath (HL.get! (k)) (S.get! (k)) (E.get! (k))), PN.Wa.length≤ 40*p∧ (Disjoint (PN.Wa.support.toFinset.toSet)  Fb):=by
--


rcases exN with ⟨PN, ⟨ hPN1, hPN2⟩ ⟩

dsimp [Fb2] at hPN2
simp at hPN2
let ⟨⟨⟨  hPN2a, hPN2b⟩ , hPN2c⟩ , hPN2d⟩:= hPN2

let PN_imp: SubgraphPath_implicit G:=⟨HL.get! (k), S.get! (k), E.get! (k), PN⟩

let  Fo': List (SubgraphPath_implicit G):= Fo.P++[PN_imp]

have Starts_equal: starts_equal iV iSP S Fo' (k+1):= by
  unfold starts_equal
  intros i hi
  by_cases case:(i< k)
  rw[FS.symm]
  rw[Fo.Starts_equal i]
  dsimp[Fo']
  simp
  congr 1
  refine (List.getD_append Fo.P [PN_imp] default i ?_).symm
  rw[FFoL]
  exact case
  rw[Fk]
  exact case

  simp at case
  have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
  rw[hieq]
  dsimp[Fo']
  have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
  simp at h1
  rw[FFoL] at h1
  simp
  rw[h1]

  dsimp[PN_imp]
  simp

have Ends_equal: ends_equal iV iSP E Fo' (k+1):= by
  unfold ends_equal
  intros i hi
  by_cases case:(i< k)
  rw[FE.symm]
  rw[Fo.Ends_equal i]
  dsimp[Fo']
  simp
  congr 1
  refine (List.getD_append Fo.P [PN_imp] default i ?_).symm
  rw[FFoL]
  exact case
  rw[Fk]
  exact case

  simp at case
  have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
  rw[hieq]
  dsimp[Fo']
  have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
  simp at h1
  rw[FFoL] at h1
  simp
  rw[h1]

  dsimp[PN_imp]
  simp




have Graphs_equal: graphs_equal   iSP H Fo' (k+1-1):= by
  intros i hi
  dsimp[Fo']
  simp
  rw[List.getD_append ]
  unfold graphs_equal at FinH
  simp at FinH
  apply FinH
  simp at hi
  exact hi
  calc
    i<(k+1)-1:=by exact hi
    _≤ kmax-1:=by
      gcongr
  rw[FFoL]
  simp at hi
  exact hi
  --



have Paths_disjoint: paths_disjoint iSP  Fo' (k+1):= by
  intro i j hi hj
  by_cases case:(j< k)
  dsimp[Fo']
  --simp
  have h1: (Fo.P ++ [PN_imp]).get! j=(Fo.P).get! j:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
  have h2: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    have h3: i<k:= by exact Nat.lt_trans hi case
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq h3 (id FFoL.symm)
  rw[h1, h2]
  apply Fo.Paths_disjoint
  exact hi
  exact Nat.lt_of_lt_of_eq case (id Fk.symm)

  simp at case
  have hieq: j=k:= by
      exact Nat.eq_of_le_of_lt_succ case hj
  rw[hieq]
  dsimp[Fo']
  have h2: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    have h3: i<k:= by exact Nat.lt_of_lt_of_eq hi hieq
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq h3 (id FFoL.symm)
  rw[h2]


  have h4: ((Fo.P ++ [PN_imp]).get! k)=PN_imp:= by
    have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
      apply List.getD_append_right
      exact Nat.le_refl Fo.P.length
    simp at h1
    rw[FFoL] at h1
    simp
    rw[h1]
  rw[h4]
  dsimp[PN_imp]
  have h5: {v | v ∈ (Fo.P.get! i).Pa.Wa.support}⊆ {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}:= by
    simp
    intro a ha
    use i
    constructor
    exact Nat.lt_of_lt_of_eq hi hieq
    exact ha
  have h5: {v | v ∈ (Fo.P.get! i).Pa.Wa.support}≤  {v | ∃ t < k, v ∈ (Fo.P.get! t).Pa.Wa.support}:= by
    exact h5
  apply Disjoint.mono_left h5 --hPN2.2
  apply Disjoint.symm

  apply Disjoint.mono_right Fb_bridge --hPN2.2
  exact hPN2b



have Fo'Length: Fo'.length=k+1:=by
  dsimp[Fo']
  simp
  rw[Fk.symm]
  exact Fo.P_length


let F1:PathForest iV iSP H:= ⟨S, E, Fo', k+1, Starts_equal, Ends_equal, Graphs_equal, Paths_disjoint, Fo'Length ⟩

use F1

constructor
exact rfl
constructor
exact rfl
constructor
exact rfl
constructor
dsimp[F1]
dsimp[Fo']
simp
exact FFoL

constructor

intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
apply FAvoid
exact Nat.lt_of_lt_of_eq case (id Fk.symm)

simp at case
have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
have h6: (Fo.P ++ [PN_imp]).get! k=PN_imp:= by
  simp
  rw[h1]
rw[h6]

exact hPN2a




/-dsimp[F1]
unfold Path_forest_support
dsimp[Fo']
simp only [List.mem_append, List.mem_singleton]

have h20: {v | ∃ Pi, (Pi ∈ Fo.P ∨ Pi = PN_imp) ∧ v ∈ Pi.Pa.Wa.support}={v | ∃ Pi, Pi ∈ Fo.P  ∧ v ∈ Pi.Pa.Wa.support}∪ {v |  v ∈ PN_imp.Pa.Wa.support}:= by
  ext v
  constructor
  intro h
  simp
  simp at h
  rename_i
    h_1
  aesop_subst
    [Fk,
    FS,
    FE]
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    List.get!_eq_getD,
    true_implies,
    and_self,
    PN_imp]
  unhygienic
    with_reducible
      aesop_destruct_products
  unhygienic
    aesop_cases
      left
  · apply
      Or.inl
    apply
      Exists.intro
    apply
      And.intro
    on_goal
      2 =>
      exact
        right
    simp_all only
  · aesop_subst
      h
    simp_all only [or_true]

  intro
    a
  aesop_subst
    [Fk,
    FS,
    FE]
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    List.get!_eq_getD,
    true_implies,
    and_self,
    Set.mem_union,
    Set.mem_setOf_eq,
    PN_imp]
  unhygienic
    aesop_cases
      a
  · unhygienic
      with_reducible
        aesop_destruct_products
    apply
      Exists.intro
    apply
      And.intro
    on_goal
      2 =>
      exact
        right
    simp_all only [true_or]
  · apply
      Exists.intro
    apply
      And.intro
    apply
      Or.inr
    apply
      Eq.refl
    simp_all only
simp_rw[h20]


constructor
calc
  ({v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support} ∪ {v | v ∈ PN.Wa.support}).toFinset.card
  =
  ({v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset ∪ {v | v ∈ PN.Wa.support}.toFinset).card:= by
    simp
  _≤ {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset.card + {v | v ∈ PN.Wa.support}.toFinset.card:= by
    exact
      card_union_le {v | ∃ Pi ∈ Fo.P, v ∈ Pi.Pa.Wa.support}.toFinset
        {v | v ∈ PN.Wa.support}.toFinset

  _≤41*p*k+41*p:= by
    gcongr
    unfold Path_forest_support at FSupport
    simp at FSupport
    simp
    exact FSupport

    simp only [Set.mem_setOf_eq]
    calc
      {v | v ∈ PN.Wa.support}.toFinset.card
      = PN.Wa.support.toFinset.card:= by
        congr
        simp
        ext v
        constructor

        intro h
        simp
        simp at h
        exact h
        intro h
        simp
        simp at h
        exact h
      _≤ PN.Wa.support.length:=by
        exact List.toFinset_card_le PN.Wa.support

      _=PN.Wa.length+1:= by
        simp
      _≤ 40*p+p:= by gcongr; exact pPositive
      _=41*p:=by ring_nf

  _=41*p*(k+1):= by
    ring_nf

--∃ (P: SubgraphPath H u v), P.Wa.length≤ 40*p∧ (Disjoint (P.Wa.support.toFinset.toSet)  Fb)

-/
constructor

--------------- Avoid S
intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
have h13: {v | v ∈ List.drop (k + 1) S}⊆ {v | v ∈ List.drop (k ) S}:= by
  simp
  intro b hb
  have h12: List.drop (1+k) S= List.drop (1) (List.drop (k) S):= by
    exact List.drop_add 1 k S
  rw[add_comm] at h12
  apply List.mem_of_mem_drop
  rw[h12] at hb
  exact hb
apply Disjoint.mono_right h13
apply FAvoidS
exact Nat.lt_of_lt_of_eq case (id Fk.symm)

simp at case
have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
have h6: (Fo.P ++ [PN_imp]).get! k=PN_imp:= by
  simp
  rw[h1]
rw[h6]
exact hPN2c





constructor

--------------- Avoid E
intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
have h13: {v | v ∈ List.drop (k + 1) E}⊆ {v | v ∈ List.drop (k ) E}:= by
  simp
  intro b hb
  have h12: List.drop (1+k) E= List.drop (1) (List.drop (k) E):= by
    exact List.drop_add 1 k E
  rw[add_comm] at h12
  apply List.mem_of_mem_drop
  rw[h12] at hb
  exact hb
apply Disjoint.mono_right h13
apply FAvoidE
exact Nat.lt_of_lt_of_eq case (id Fk.symm)

simp at case
have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
have h6: (Fo.P ++ [PN_imp]).get! k=PN_imp:= by
  simp
  rw[h1]
rw[h6]
exact hPN2d


constructor
------------long:
intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
apply FLong
exact Nat.lt_of_lt_of_eq case (id Fk.symm)

simp at case
have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
have h6: (Fo.P ++ [PN_imp]).get! k=PN_imp:= by
  simp
  rw[h1]
rw[h6]
exact hPN1


----inHL
constructor
intro i hi
by_cases case:(i< k)
dsimp[Fo']
  --simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
    simp
    apply List.getD_append
    exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
apply FinHL
exact Nat.lt_of_lt_of_eq case (id Fk.symm)

simp at case
have hieq: i=k:= by
      exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
    apply List.getD_append_right
    exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
have h6: (Fo.P ++ [PN_imp]).get! k=PN_imp:= by
  simp
  rw[h1]
rw[h6]



have h24:_:= by exact PN_imp.Pa.Wa_In_H
dsimp [PN_imp] at h24
dsimp [PN_imp]
simp
simp at h24
calc
  {v | v ∈ PN.Wa.support}
  ⊆ PN.Wa.toSubgraph.verts:= by
    intro a ha
    simp
    simp at ha
    exact ha
  _⊆ (HL.getD k default).verts:=by
    apply subgraphs_vertex_sets_subsets
    exact h24



by_cases case9: k+1≤ (kmax - 1)
have mineq: min (k + 1) (kmax - 1)=k+1:= by
  exact Nat.min_eq_left case9
have mineq2: min (k ) (kmax - 1)=k:= by
  have kmi: k≤ (kmax - 1):= by
    calc
      k≤ k+1:= by simp
      _≤ kmax - 1:= by
        exact case9
  exact Nat.min_eq_left kmi
unfold graphs_equal
rw[mineq]
intros i hi
by_cases case:(i< k)
dsimp[Fo']
--simp
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
  simp
  apply List.getD_append
  exact Nat.lt_of_lt_of_eq case (id FFoL.symm)
rw[h1]
apply FinH
rw[mineq2]
exact   case
simp at case
have hieq: i=k:= by
    exact Nat.eq_of_le_of_lt_succ case hi
rw[hieq]
--dsimp[Fo']
have h1: ((Fo.P ++ [PN_imp]).getD (Fo.P.length) default)=[PN_imp].getD (Fo.P.length-Fo.P.length) default:= by
  apply List.getD_append_right
  exact Nat.le_refl Fo.P.length
simp at h1
rw[FFoL] at h1
simp
rw[h1]

dsimp[PN_imp]
--simp
apply HL_in_H
calc
  k< k+1:= by simp
  _≤ kmax - 1:= by
    exact case9


simp at case9
have mineq: min (k + 1) (kmax - 1)=(kmax - 1):= by
  have h7: (kmax - 1)≤ (k + 1):= by
    apply Nat.le_of_lt case9
  apply Nat.min_eq_right h7
have case9':(kmax - 1)≤ k:= by
  exact Nat.le_of_lt_succ case9

intros i hi
--dsimp[Fo']
--simp
have ilk: i<k:= by
  calc
    i<min (k + 1) (kmax - 1):= by exact hi
    _=(kmax - 1):= by rw[mineq]
    _≤ k:= by exact case9'
have ilkm: i<(kmax-1):= by
  calc
    i<min (k + 1) (kmax - 1):= by exact hi
    _=(kmax - 1):= by rw[mineq]
have h1: (Fo.P ++ [PN_imp]).get! i=(Fo.P).get! i:= by
  simp
  apply List.getD_append
  rw[FFoL]
  exact ilk
rw[h1]
apply FinH
simp
constructor
exact ilk
exact ilkm
