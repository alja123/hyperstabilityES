--import MyProject

import hyperstabilityES.lemmas.clumps_joining2
 --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false
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
variable {p m κ pr h: ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable (iSub:Inhabited (Subgraph G))




@[ext] structure Locally_Dense  (G: SimpleGraph V) (p m    h: ℕ ) where
  Gr: Subgraph G
  H: Finset (Subgraph G)
  H_Edge_Disjoint:  HEdge_Disjoint H -- ∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅)
  H_Cut_Dense: HCut_Dense_Family H p --∀ (A: Subgraph G), A ∈ H → cut_dense G A p
  H_Order: HOrder_ge_m_Family H m -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_Order_Upper_Bound: HOrder_le_hm_Family H m h -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_In_K: FamilyContained_in_Graph H Gr--∀ (A: Subgraph G), A ∈ H → A ≤ Gr
  H_Partition_K: sSup H= Gr
/-
@[ext] structure Clump_Decomposition  (G: SimpleGraph V) ( p m κ pr h: ℕ ) (L: Subgraph G) (KF: Finset (Clump G p m κ pr h)) where
  GrFam: Set (Subgraph G):={K.Gr| K ∈ KF}

  H_Edge_Disjoint:  HEdge_Disjoint GrFam -- ∀ (A B: Subgraph G),  (A∈ H)→ (B∈ H)→ (A≠ B)→ (A.edgeSet ∩ B.edgeSet = ∅)
  H_Cut_Dense: HCut_Dense_Family H p --∀ (A: Subgraph G), A ∈ H → cut_dense G A p
  H_Order: HOrder_ge_m_Family H m -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_Order_Upper_Bound: HOrder_le_hm_Family H m h -- ∀ (A: Subgraph G), A ∈ H → A.verts.toFinset.card ≥ m
  H_In_K: FamilyContained_in_Graph H Gr--∀ (A: Subgraph G), A ∈ H → A ≤ Gr
  H_Partition_K: sSup H= Gr
-/


def Clump_family_edge_disjoint
(KFam: Finset (Clump G p m κ pr h))
:=(∀(K1 K2: (Clump G p m κ pr h)), K1∈ KFam→ K2∈KFam→ K1≠ K2→ K1.Gr.edgeSet ∩ K2.Gr.edgeSet = ∅)

def Clump_family_contained_in_L
(L:Subgraph G)(KFam: Finset (Clump G p m κ pr h))
:=(∀ (K: (Clump G p m κ pr h)), K∈ KFam→ K.Gr≤ L)

def L_contained_in_clump_family
(L:Locally_Dense G p m h)(KFam: Finset (Clump G p m κ pr h))
:=(∀ (Hi: Subgraph G), Hi∈ L.H→ ∃ (K: Clump G p m κ pr h), K ∈ KFam ∧ Hi≤ K.Gr)



def graph_forms_clump (L: Subgraph G)(X: Clump G p m κ pr h)
  :=X.Gr=L
  ∧ X.H={L}
  ∧ X.C=L
  ∧ X.k≥ 1
  ∧ X.k≤ L.verts.toFinset.card/(m/pr)+1


lemma initial_clump_construction_2
{L: Subgraph G}
(hLorderm: L.verts.toFinset.card ≥ m)
(hLorderhm: L.verts.toFinset.card ≤  h*m)
(hL: cut_dense G L p)
--(pLarge: p≥ 20)
--(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
:
∃ (X: Clump G p m κ pr h), graph_forms_clump L X
:= by
have hpm: m/pr>0:= by
  refine Nat.div_pos ?hba prPositive
  calc
    m≥ κ := by  apply gg2_ge; repeat assumption
    _≥ h:= by apply gg1_ge; repeat assumption
    _≥ pr:= by apply gg1_ge; repeat assumption
have hLorderUpperBound: L.verts.toFinset.card ≤  m*h*4:=by
  calc
    L.verts.toFinset.card ≤ h*m:= by exact hLorderhm
    _=m*h*1:= by ring_nf
    _≤ m*h*4:= by gcongr; exact NeZero.one_le
apply initial_clump_construction
repeat assumption
calc
    m≥ κ := by  apply gg2_ge; repeat assumption
    _≥ h:= by apply gg1_ge; repeat assumption
    _≥ gg1 pr:= by exact hggp

exact gg2_5 prggp pPositive
calc
  κ ≥ h:= by apply gg1_ge; repeat assumption
  _≥ pr:= by apply gg1_ge; repeat assumption
  _≥ p:= by apply gg2_ge; repeat assumption
repeat assumption


lemma initial_clump_construction_3
{L: Locally_Dense G p m h}
(Li: Subgraph G)
(hLi: Li∈ L.H)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
:
∃ (X: Clump G p m κ pr h), graph_forms_clump Li X
:= by
apply initial_clump_construction_2
repeat assumption
exact L.H_Order Li hLi
exact L.H_Order_Upper_Bound Li hLi
exact L.H_Cut_Dense Li hLi
repeat assumption


def Clumps_forming_L: Subgraph G→ (Set (Clump G p m κ pr h)):=
  fun L=> {K: Clump G p m κ pr h| graph_forms_clump L K}

--noncomputable def Clump_forming_L: Subgraph G→ (Set (Clump G p m κ pr h)):=
  --fun L=> if x:Nonempty (Clumps_forming_L L) then (Clumps_forming_L L) else ∅

noncomputable def Clump_forming_L  (nan: Clump G p m κ pr h ): Subgraph G→  (Clump G p m κ pr h):=
  fun L=> if x:Nonempty {K: Clump G p m κ pr h| graph_forms_clump L K} then x.some else nan
  --{K: Clump G p m κ pr h| graph_forms_clump L K}





def Clump_Decomposition
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
:= Clump_family_edge_disjoint KFam-- (∀(K1 K2: (Clump G p m κ pr h)), K1∈ KFam→ K2∈KFam→ K1≠ K2→ K1.Gr.edgeSet ∩ K2.Gr.edgeSet = ∅)
∧ Clump_family_contained_in_L L.Gr KFam  --(∀ (K: (Clump G p m κ pr h)), K∈ KFam→ K.Gr≤ L.Gr)
∧L_contained_in_clump_family L KFam-- (∀ (Hi: Subgraph G), Hi∈ L.H→ ∃ (K: Clump G p m κ pr h), K ∈ KFam ∧ Hi≤ K.Gr)


lemma Initial_Clump_Decomposition_forms_clump
(L: Locally_Dense G p m h)
(Li: Subgraph G)
(hLi: Li∈ L.H)
(nan: Clump G p m κ pr h)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
:
graph_forms_clump Li (Clump_forming_L nan Li)
:= by
have hNonemp:Nonempty {K: Clump G p m κ pr h| graph_forms_clump Li K}:=by
  refine nonempty_subtype.mpr ?_
  apply @initial_clump_construction_3  _ _ _ _  p m κ pr h
  repeat assumption

have h1: (Clump_forming_L nan Li)=(hNonemp.some):= by
  simp [Clump_forming_L]
  apply dif_pos
  apply @initial_clump_construction_3  _ _ _ _  p m κ pr h
  repeat assumption

have h2: (Clump_forming_L nan Li)∈{K: Clump G p m κ pr h| graph_forms_clump Li K}:=by
  rw[h1]
  exact Subtype.coe_prop hNonemp.some

simp at h2
exact h2

/-
lemma Clump_forming_injective
(L: Locally_Dense G p m h)
(nan Ki: Clump G p m κ pr h)
:
(Clump_forming_L nan).Injective
:=by
intro Li Lj hAB
have h1: graph_forms_clump Li (Clump_forming_L nan Li):=by
  apply Initial_Clump_Decomposition_forms_clump
  repeat assumption
have h2: graph_forms_clump Lj (Clump_forming_L nan Lj):=by
  apply Initial_Clump_Decomposition_forms_clump
  repeat assumption
have h3: (Clump_forming_L nan Li).Gr=Li:=by
  exact h1.1
have h4: (Clump_forming_L nan Lj).Gr=Lj:=by
  exact h2.1
rw[h3.symm, h4.symm]
exact congrArg Clump.Gr hAB
-/

lemma Initial_Clump_Decomposition_Li_eq_Gr
(L: Locally_Dense G p m h)
(nan Ki: Clump G p m κ pr h)
(KFam: Finset (Clump G p m κ pr h))
(hKFam: KFam= Finset.image (Clump_forming_L nan) L.H)
(hKi: Ki∈ KFam)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
: ∃ (Li: Subgraph G), Li∈ L.H ∧ Ki.Gr=Li∧ (Clump_forming_L nan Li = Ki)
:= by
rw [hKFam] at hKi
simp  at hKi
rcases hKi with ⟨Li, hLi, hKi⟩
have h_forms_clump:graph_forms_clump Li Ki:=by
  rw[hKi.symm]
  apply Initial_Clump_Decomposition_forms_clump
  repeat assumption
exact ⟨Li, ⟨hLi, h_forms_clump.1, hKi⟩⟩


lemma Initial_Clump_Decomposition_1
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
(KFam: Finset (Clump G p m κ pr h))
(hKFam: KFam= Finset.image (Clump_forming_L nan) L.H)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
:
Clump_Decomposition L KFam
∧ (∀ (X:Clump G p m κ pr h ), (X∈ KFam) → (X.k≤ (h*m)/(m/pr)+1))
:= by
constructor
constructor
intro K1 K2 hK1 hK2 hK1K2
have h1: ∃ (L1: Subgraph G), L1∈ L.H ∧ K1.Gr=L1∧ (Clump_forming_L nan L1 = K1):=by
  apply Initial_Clump_Decomposition_Li_eq_Gr
  repeat assumption
have h2: ∃ (L2: Subgraph G), L2∈ L.H ∧ K2.Gr=L2∧ (Clump_forming_L nan L2 = K2):=by
  apply Initial_Clump_Decomposition_Li_eq_Gr
  repeat assumption
rcases h1 with ⟨L1, hL1, hK1L1, h'K1L1⟩
rcases h2 with ⟨L2, hL2, hK2L2, h'K2L2⟩
rw[hK1L1, hK2L2]

apply L.H_Edge_Disjoint
repeat assumption
by_contra hcont
have h3: K1=K2:=by
  rw[h'K1L1.symm, h'K2L2.symm]
  exact congrArg (Clump_forming_L nan) hcont
exact hK1K2 h3

constructor
intro K hK
have h1: ∃ (Li: Subgraph G), Li∈ L.H ∧ K.Gr=Li∧ (Clump_forming_L nan Li = K):=by
  apply Initial_Clump_Decomposition_Li_eq_Gr
  repeat assumption
rcases h1 with ⟨Li, hLi, hKL, h'KL⟩
calc
 K.Gr=Li:=by exact hKL
  _≤ L.Gr:=by
    apply L.H_In_K
    exact  hLi

intro Li hLi
let Ki:=(Clump_forming_L nan Li)
have h1: graph_forms_clump Li Ki:=by
  dsimp [Ki]
  apply Initial_Clump_Decomposition_forms_clump
  repeat assumption
have h2: Ki∈ KFam:=by
  rw[hKFam]
  simp
  exact ⟨Li, hLi, rfl⟩
have h3:  Ki.Gr=Li:=by
  exact h1.1
have h4: Li≤ Ki.Gr:=by
  exact le_of_eq (id h3.symm)
exact ⟨Ki, h2, h4⟩

intro K1 hK1
have h1: ∃ (L1: Subgraph G), L1∈ L.H ∧ K1.Gr=L1∧ (Clump_forming_L nan L1 = K1):=by
  apply Initial_Clump_Decomposition_Li_eq_Gr
  repeat assumption
rcases h1 with ⟨L1, hL1, hK1L1, h'K1L1⟩
have h1: graph_forms_clump L1 K1:=by
  rw[h'K1L1.symm]
  apply Initial_Clump_Decomposition_forms_clump
  repeat assumption
unfold graph_forms_clump at h1
calc
  K1.k ≤ L1.verts.toFinset.card / (m / pr) + 1:=by
    exact h1.2.2.2.2
  _≤ h * m / (m / pr) + 1:=by
    gcongr
    apply L.H_Order_Upper_Bound
    exact hL1



/-
lemma Initial_Clump_Decomposition
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
:
∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam
:= by
let KFam: Finset (Clump G p m κ pr h):=Finset.image (Clump_forming_L nan) L.H
have hKFam: KFam= Finset.image (Clump_forming_L nan) L.H:= by exact rfl
use KFam

apply Initial_Clump_Decomposition_1
repeat assumption
-/

/-
lemma Initial_Clump_Decomposition
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
:
∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam
:= by

have Nonempty_f_Li:∀ (Li: Subgraph G), Li∈ L.H→ Nonempty {K: Clump G p m κ pr h| graph_forms_clump Li K}:=by
  intro Li
  intro hLi
  refine nonempty_subtype.mpr ?_
  apply @initial_clump_construction_3  _ _ _ _  p m κ pr h
  repeat assumption

have f_not_nan:∀ (Li: Subgraph G), Li∈ L.H→
graph_forms_clump L (Clump_forming_L nan Li)=x.some:=by
-/

/-
lemma Initial_Clump_Decomposition
(L: Locally_Dense G p m h)
:
∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam
:= by

have Nonempty_f_Li:∀ (Li: Subgraph G), Li∈ L.H→ Nonempty (Clumps_forming_L Li):=by
  intro Li
  intro hLi
  refine nonempty_subtype.mpr ?_
  apply @initial_clump_construction_3  _ _ _ _  p m κ pr h
  repeat assumption


have f: (Li: Subgraph G)→ (Li∈ L.H)→ Nonempty (Clumps_forming_L Li):= by
  exact fun Li a ↦  Nonempty_f_Li Li a
let KFamSet: (Finset (Set (Clump G p m κ pr h))):= Finset.image Clumps_forming_L L.H

have hNonemp: ∀ (x: Set (Clump G p m κ pr h)), x ∈ KFamSet→ Nonempty x:= by
  intro x
  intro h
  dsimp [KFamSet] at h
  simp at h
  rcases h with ⟨Li, hLi, h⟩
  rw [h.symm]

  apply Nonempty_f_Li
  exact hLi


  --repeat assumption
-/
