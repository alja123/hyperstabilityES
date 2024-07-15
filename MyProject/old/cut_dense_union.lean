import MyProject

import MyProject.cut_dense_basics


open Classical
open Finset
--open scoped BigOperators

namespace SimpleGraph

--set_option maxHeartbeats 600000

universe u
variable {V : Type u} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]
variable (n: ℕ )
variable (d:ℕ )
variable [Fintype (Sym2 V)]

--theorem cut_dense_union (H: Subgraph G)(K: Subgraph G)(p q:ℚ)(HCutDense: cut_dense G H p)(KCutDense: cut_dense G H p)(hq: q= (p* (H.verts ∩ K.verts).toFinset.card)/(4*(H.verts ∪ K.verts).toFinset.card)):cut_dense G (H⊔K) q:= by
lemma nonempty_set_finset (S: Set V)(h: Nonempty (S.toFinset)): Nonempty S:= by
have h1: ∃(x:V),(x∈ S.toFinset):= by exact nonempty_subtype.mp h
rcases h1 with ⟨x, hx⟩
have h2:x∈ S:= by exact Set.mem_toFinset.mp hx
refine nonempty_subtype.mpr ?intro.a
use x

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
  _≥ (Nat.ceil (a'/b'))*e:= by gcongr;
  _=  (Nat.ceil (a'/b'))*e':= by exact rfl
  _≥ (a'/b')*e':= by gcongr;
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

lemma nat_self_div (a:ℕ)(ha:0<a): (a/a=1):= by
have h0: a≤ a:= by exact Nat.le_refl a
have h1:a/a=(a-a)/a+1:= by exact Nat.div_eq_sub_div ha h0
exact Nat.div_self ha

lemma subgraph_preserves_adj  (H K: Subgraph G)(hHK:H≤ K)(v w:V):( H.Adj v w → K.Adj v w):= by
have h1: (H.verts ⊆ K.verts) ∧ (∀ (v w : V), H.Adj v w → K.Adj v w):= by exact hHK
apply h1.2

theorem interedges_subgraph_leq (H K: Subgraph G)(hHK:H≤ K):(Rel.interedges H.Adj A B⊆  Rel.interedges K.Adj A B):= by
intro e he
let (x, y):=e
have h: x∈ A∧ y∈ B ∧ H.Adj x y := by exact Rel.mk_mem_interedges_iff.mp he
have hxy:H.Adj x y:= h.2.2
have kxy: K.Adj x y:= by exact subgraph_preserves_adj G H K hHK x y hxy
--have hx:x∈ K.verts:= by exact K.edge_vert kxy
--have hy:x∈ K.verts:= by exact K.edge_vert kxy
have hxy': x∈ A∧ y∈ B ∧ K.Adj x y := by
  constructor
  exact h.1
  constructor
  exact h.2.1
  exact kxy
exact Rel.mk_mem_interedges_iff.mpr hxy'

--theorem interedges_subsets_leq (H: Subgraph G)(A B A' B':Finset V)(hA: A'⊆ A)(hB: B'⊆ B):Rel.interedges H.Adj A' B'⊆ Rel.interedges H.Adj A B:=by
--exact?

lemma gt_implies_gte_rational (a  b: ℚ )(ha:(b<a)):  (b≤ a):= by
  have h1: (b≤ a) ∧ (b≠ a):= by exact lt_iff_le_and_ne.mp ha
  exact h1.1

lemma gt_cast_N_Q (a:ℕ)(ha:0< a): (0< (a:ℚ)):=
by exact Nat.cast_pos.mpr ha


theorem cut_dense_union_after_wlog (H: Subgraph G)(K: Subgraph G)(hNonempty: Nonempty (H⊔ L).verts )(k :ℕ )
(HCutDense: cut_dense G H k)(KCutDense: cut_dense G K k)
--(hl: l= (4*k* ((H.verts ∪  K.verts).toFinset.card ))/(((H.verts ∩ K.verts).toFinset.card)))
 (I A B:Finset V)(hunion: (H.verts∪ K.verts).toFinset= A∪ B)
 (hI: I=(H.verts ∩ K.verts).toFinset)(Iwlog: 2*((I∩ A).card) ≥ I.card)
 (hBwlog: 2*((H.verts.toFinset ∩ B).card)  ≥ B.card)
 :4*k* ((H.verts ∪  K.verts).toFinset.card )*(Rel.interedges (H⊔ K).Adj A B).card ≥ A.card*B.card* ((H.verts ∩  K.verts).toFinset.card ):= by

have contHunion: H≤ H⊔ K := by exact SemilatticeSup.le_sup_left H K
have cont1: Rel.interedges H.Adj A B⊆ Rel.interedges (H ⊔ K).Adj A B:= by exact interedges_subgraph_leq G H (H ⊔ K) contHunion
let A':=A∩ H.verts.toFinset
let B':=B∩ H.verts.toFinset
have hunion2:H.verts ∪ K.verts=(H⊔ K).verts:= by exact rfl
have Hunion: A'∪ B'=H.verts.toFinset:= by calc
  A'∪ B'=(A∩ H.verts.toFinset)∪ (B∩ H.verts.toFinset):= by exact rfl
  _=(A∪ B)∩ H.verts.toFinset:= by exact (union_inter_distrib_right A B H.verts.toFinset).symm
  _=(H.verts ∪ K.verts).toFinset ∩ H.verts.toFinset:= by exact    congrFun (congrArg Inter.inter (id hunion.symm)) H.verts.toFinset
  _= H.verts.toFinset:= by simp
have hA':A'⊆ A:= by exact inter_subset_left A H.verts.toFinset
have hB':B'⊆ B:= by exact inter_subset_left B H.verts.toFinset
have cont2:Rel.interedges H.Adj A' B'⊆Rel.interedges (H ⊔ K).Adj A B:= by calc
  Rel.interedges H.Adj A' B'⊆ Rel.interedges H.Adj A B:= by exact Rel.interedges_mono hA' hB'
  _⊆ Rel.interedges (H⊔ K).Adj A B:= by exact cont1

have ineq1:  (Rel.interedges (H ⊔ K).Adj A B).card ≥ (Rel.interedges H.Adj A' B').card:= by exact  card_le_of_subset cont2


let AI:= A∩ I
have hAicont:AI⊆ A':= by calc
  AI=A∩(H.verts ∩ K.verts).toFinset:= by rw[hI.symm]
  _=A∩H.verts.toFinset ∩ K.verts.toFinset:= by simp
  _⊆ A':= by exact inter_subset_left (A ∩ H.verts.toFinset) K.verts.toFinset

have AIeq: AI= I∩ A:= by exact inter_comm A I
rw [AIeq.symm] at Iwlog
--have Iwlog: (AI.card:ℚ)≥ (I.card / 2:ℚ)  := by exact?

have B'eq:B'=(H.verts.toFinset ∩ B):= by exact inter_comm B H.verts.toFinset
rw [B'eq.symm] at hBwlog

have hAcont: A⊆ (H.verts ∪ K.verts).toFinset:= by calc
 A⊆A∪ B:= by exact subset_union_left A B
 _=(H.verts ∪ K.verts).toFinset:= by exact id hunion.symm
have aAcontcard:A.card≤  (H.verts ∪ K.verts).toFinset.card:= by exact card_le_of_subset hAcont



#check HCutDense A' B' (id Hunion.symm)
#check cut_dense
calc
  4*k* ((H.verts ∪  K.verts).toFinset.card )*((Rel.interedges (H ⊔ K).Adj A B).card) ≥ 4*k* ((H.verts ∪  K.verts).toFinset.card )*((Rel.interedges H.Adj A' B').card ):= by gcongr;
  _=4*((H.verts ∪  K.verts).toFinset.card )*(k*((Rel.interedges H.Adj A' B').card )):= by
    simp;
    ring_nf
  _≥ 4*((H.verts ∪  K.verts).toFinset.card )* (A'.card * B'.card) := by
    have _:(k*((Rel.interedges H.Adj A' B').card ))≥ (A'.card * B'.card):= by exact      HCutDense A' B' (id Hunion.symm)
    gcongr--exact HCutDense A' B' (id Hunion.symm)
  _≥ 4*((H.verts ∪  K.verts).toFinset.card )* (AI.card *B'.card):= by
    have h1: A'.card≥ AI.card:= by exact card_le_of_subset hAicont;
    gcongr
  _=2*((H.verts ∪  K.verts).toFinset.card )*B'.card* (2*AI.card):= by
    ring_nf--exact mul_right_comm p ↑AI.card ↑B'.card
  _≥ 2*((H.verts ∪  K.verts).toFinset.card )*B'.card * I.card:= by
    gcongr--gcongr
  _=((H.verts ∪  K.verts).toFinset.card )* (I.card)*(2*B'.card):= by
    ring_nf--exact (mul_right_comm p (↑I.card / 2) ↑B'.card).symm
  _≥ ((H.verts ∪  K.verts).toFinset.card )* (I.card) * (B.card):= by
    gcongr
  _≥ (A.card )* (I.card) * (B.card):= by
    gcongr
  _= (A.card) * (B.card) * (I.card ):= by
    ring_nf
  _= A.card * B.card * (H.verts ∩ K.verts).toFinset.card:= by
    congr



lemma incl_excl_corollary (X Y Z: Finset V)(hsubset:X⊆ Y∪ Z): (Y∩ X).card +(Z∩ X).card ≥ (X).card:= by
have incl_excl: X.card=(Y∩ X).card+(Z∩ X).card-(X∩  Y∩ Z).card:= by calc
  X.card=((Y∩ X)∪ (Z∩ X)).card:= by
    have h1: ((Y∩ X)∪ (Z∩ X))=X:= by calc
      ((Y∩ X)∪ (Z∩ X))=(Y∪ Z)∩ X:= by exact (union_inter_distrib_right Y Z X).symm
      _=X:= by exact inter_eq_right.mpr hsubset
    exact congrArg card (id h1.symm)
  _=(Y∩ X).card+(Z∩ X).card-((Y∩ X)∩ (Z∩ X)).card:= by exact card_union (Y ∩ X) (Z ∩ X)
  _=(Y∩ X).card+(Z∩ X).card-(X∩  Y∩ Z).card:= by
    have h1:((Y∩ X)∩ (Z∩ X))=(X∩  Y∩ Z):= by calc
      ((Y∩ X)∩ (Z∩ X))=(Y∩ X∩  Z∩ X):= by simp
      _=(Y∩ X∩  X∩ Z):= by exact inter_right_comm (Y ∩ X) Z X
      _=Y∩ (X∩ Z):=by simp
      _=X∩ (Y∩ Z):=by exact inter_left_comm Y X Z
      _=X∩ Y∩ Z:= by simp;
    rw[h1]

calc
(Y∩ X).card+(Z∩ X).card≥ (Y∩ X).card+(Z∩ X).card-(X∩  Y∩ Z).card:= by exact  Nat.sub_le ((Y ∩ X).card + (Z ∩ X).card) (X ∩ Y ∩ Z).card
_=X.card:= by exact id incl_excl.symm

lemma incl_excl_corollary2 (X Y Z: Finset V)(hsubset:X⊆ Y∪ Z): (2*(Y∩ X).card ≥ (X).card)∨ (2*(Z∩ X).card ≥ (X).card):= by
by_contra h
simp at h
have h1: 2 * ((Y ∩ X).card +  (Z ∩ X).card) < 2*X.card:= by calc
  2 * ((Y ∩ X).card +  (Z ∩ X).card) = 2 * (Y ∩ X).card +  2* (Z ∩ X).card:= by exact    Nat.mul_add 2 (Y ∩ X).card (Z ∩ X).card
  _< 2 * (Y ∩ X).card + X.card:= by gcongr; exact h.2
  _<  X.card+ X.card:= by gcongr; exact h.1
  _= 2* X.card:= by exact (Nat.two_mul X.card).symm
have h2:  ((Y ∩ X).card +  (Z ∩ X).card) ≥  X.card:= by exact  incl_excl_corollary X Y Z hsubset
have h2: 2*(((Y ∩ X).card +  (Z ∩ X).card)) ≥  2*X.card:=by exact Nat.mul_le_mul_left 2 h2
have h3:  2 * ((Y ∩ X).card + (Z ∩ X).card)+2*X.card<2 * ((Y ∩ X).card + (Z ∩ X).card)+2*X.card:= by
  exact  lt_imp_lt_of_le_imp_le (fun a ↦ h2) h1
exact (lt_self_iff_false (2 * ((Y ∩ X).card + (Z ∩ X).card) + 2 * X.card)).mp h3

theorem cut_dense_union (H: Subgraph G)(K: Subgraph G)
(p q:ℕ )(HCutDense: cut_dense G H p)(KCutDense: cut_dense G K p)
(hq: q= (4*p* (H.verts ∪  K.verts).toFinset.card)/((H.verts ∩ K.verts).toFinset.card)+1)
(hNonemptyIntersection: (H.verts ∩ K.verts)≠ ∅ )
:cut_dense G (H⊔K) q:= by
intro A B hAB
let I:= (H.verts ∩ K.verts).toFinset
have hAUBI:(A∩ I)∪ (B∩ I)=I:= by  calc
  (A∩ I)∪ (B∩ I)=(A∪ B)∩ I:= by exact (union_inter_distrib_right A B I).symm
  _=I:= by
    simp;
    calc
    I=H.verts.toFinset ∩ K.verts.toFinset:= by exact Set.toFinset_inter H.verts K.verts
    _⊆ (H.verts).toFinset:=by  exact inter_subset_left H.verts.toFinset K.verts.toFinset
    _⊆ (H.verts.toFinset) ∪ (K.verts.toFinset):= by exact      subset_union_left H.verts.toFinset K.verts.toFinset
    _=(H.verts ∪ K.verts).toFinset:= by exact (Set.toFinset_union H.verts K.verts).symm
    _=(H ⊔ K).verts.toFinset:= by exact rfl
    _=A∪ B:= by rw[hAB.symm]; simp
let HV:=H.verts.toFinset
let KV:=K.verts.toFinset

have IinAUB:I⊆ A ∪ B:= by calc
  I=(H.verts ∩ K.verts).toFinset:= by rfl
  _=(H.verts).toFinset ∩ K.verts.toFinset:= by exact Set.toFinset_inter H.verts K.verts
  _=HV∩ KV:= by exact rfl
  _⊆ HV:= by exact inter_subset_left HV KV
  _⊆ HV ∪ KV:= by exact subset_union_left HV KV
  _=A∪ B:= by rw[hAB.symm]; simp

have AinHUK:A⊆ HV ∪ KV:= by calc
  A⊆ A∪ B:= by exact subset_union_left A B
  _=(H ⊔ K).verts.toFinset:= by rw[hAB.symm]; simp
  _=(H.verts ∪ K.verts).toFinset:= by exact rfl
  _=HV ∪ KV:= by exact Set.toFinset_union H.verts K.verts
have hHA:(A∩ HV)∪ (A∩ KV)= A:= by calc
  (A∩ HV)∪ (A∩ KV)=A∩ (HV∪ KV):= by exact (inter_union_distrib_left A HV KV).symm
  _=(HV∪ KV)∩ A:= by exact inter_comm A (HV ∪ KV)
  _=A:= by exact inter_eq_right.mpr AinHUK

have BinHUK:B⊆ HV ∪ KV:= by calc
  B⊆ A∪ B:= by exact subset_union_right A B
  _=(H ⊔ K).verts.toFinset:= by rw[hAB.symm]; simp
  _=(H.verts ∪ K.verts).toFinset:= by exact rfl
  _=HV ∪ KV:= by exact Set.toFinset_union H.verts K.verts

have hHB:(B∩ HV)∪ (B∩ KV)= B:= by calc
  (B∩ HV)∪ (B∩ KV)=B∩ (HV∪ KV):= by exact (inter_union_distrib_left B HV KV).symm
  _=(HV∪ KV)∩ B:= by exact inter_comm B (HV ∪ KV)
  _=B:= by exact inter_eq_right.mpr BinHUK

have hUnion: (H.verts ∪ K.verts).toFinset=A∪ B:= by calc
  (H.verts ∪ K.verts).toFinset=H.verts.toFinset ∪ K.verts.toFinset:= by exact Set.toFinset_union H.verts K.verts
  _=HV ∪ KV:= by simp
  _=A∪ B:= by rw[hAB.symm]; simp


have hNonempty: Nonempty (H⊔ K).verts:= by
  have h1: (H⊔ K).verts=H.verts ∪ K.verts:= by exact rfl
  rw[h1]
  have h2': (H.verts ∩ K.verts)⊆(H.verts ∪ K.verts):= by calc
    H.verts ∩ K.verts⊆ H.verts:= by exact Set.inter_subset_left H.verts K.verts
    _⊆ H.verts ∪ K.verts:= by exact Set.subset_union_left H.verts K.verts
  have h4: (H.verts ∪ K.verts)≠ ∅:= by
    by_contra h
    have ha: (H.verts ∩ K.verts)=∅:= by exact Set.subset_eq_empty h2' h
    exact hNonemptyIntersection ha
  exact Set.nonempty_iff_ne_empty'.mpr h4
have hI: I=(H.verts ∩ K.verts).toFinset:= by rfl

have hbpos:(H.verts ∩ K.verts).toFinset.card>0:= by
  refine card_pos.mpr ?_
  have h1: (H.verts ∩ K.verts).Nonempty:= by exact    Set.nonempty_iff_ne_empty.mpr hNonemptyIntersection
  exact Set.toFinset_nonempty.mpr h1


let e:= (Rel.interedges (H⊔ K).Adj A B).card
let a:=4*p* ((H.verts ∪  K.verts).toFinset.card )
let b:=((H.verts ∩  K.verts).toFinset.card )
let v:=A.card*B.card
have he:e=(Rel.interedges (H⊔ K).Adj A B).card:= by exact rfl
have ha:a=4*p* ((H.verts ∪  K.verts).toFinset.card ):= by exact rfl
have hb:b=((H.verts ∩  K.verts).toFinset.card ):= by exact rfl
have hv:v=A.card*B.card:= by exact rfl

have hintercom3: ((K.verts:Set V) ∩  (H.verts:Set V))=((H.verts :Set V)∩  (K.verts:Set V)):= by exact Set.inter_comm K.verts H.verts

have hintercom: (K.verts ∩  H.verts:Set V)=(H.verts ∩  K.verts:Set V):= by exact Set.inter_comm K.verts H.verts
have hintercom2: (K.verts ∩  H.verts).toFinset=(H.verts ∩  K.verts).toFinset:= by exact  Set.toFinset_inj.mpr hintercom
have hintercom2: (K.verts ∩  H.verts).toFinset.card=(H.verts ∩  K.verts).toFinset.card:= by exact  congrArg card hintercom2

have hunioncom: K.verts ∪   H.verts=H.verts ∪  K.verts:= by exact Set.union_comm K.verts H.verts
have hunioncom2: (K.verts ∪   H.verts).toFinset=(H.verts ∪  K.verts).toFinset:= by exact  Set.toFinset_inj.mpr hunioncom
have hunioncom3: (K.verts ∪   H.verts).toFinset.card=(H.verts ∪  K.verts).toFinset.card:= by exact  congrArg card hunioncom2

have hkuh: K⊔ H=H⊔ K:= by exact sup_comm K H


have he':e=(Rel.interedges (K⊔ H).Adj A B).card:= by rw[hkuh];
have he'':e=(Rel.interedges (H⊔ K).Adj B A).card:= by exact  Rel.card_interedges_comm (fun ⦃x y⦄ a ↦ id (Subgraph.adj_symm (H ⊔ K) a)) A B
have he''':e=(Rel.interedges (K⊔ H).Adj B A).card:= by rw[hkuh]; exact he''
have ha':a=4*p* ((K.verts ∪  H.verts).toFinset.card ):= by exact  congrArg (4 * p).mul (id hunioncom3.symm)
have hb':b=((K.verts ∩  H.verts:Set V).toFinset.card ):= by exact id hintercom2.symm
have hv':v=B.card*A.card:= by exact Nat.mul_comm A.card B.card

have hI':I=(K.verts ∩  H.verts).toFinset:= by  simp_rw[hintercom3]

have hNonempty' : Nonempty ↑(K ⊔ H).verts:= by rw[hkuh]; exact hNonempty

have ABunioncom: A∪ B=B∪ A:= by exact union_comm A B

have hUnion':(K.verts ∪ H.verts).toFinset = A ∪ B:= by simp_rw[hunioncom]; exact hUnion
have hUnion'':(H.verts ∪ K.verts).toFinset = B ∪ A:= by simp_rw[ABunioncom.symm]; exact hUnion
have hUnion''':(K.verts ∪ H.verts).toFinset = B ∪ A:= by simp_rw[ABunioncom.symm, hunioncom]; exact hUnion

have hOr2: (2 * (HV ∩ B).card ≥ B.card) ∨ (2 * (KV ∩ B).card ≥ B.card):= by exact  incl_excl_corollary2 B HV KV BinHUK
have hOr3: (2 * (HV ∩ A).card ≥ A.card) ∨ (2 * (KV ∩ A).card ≥ A.card):= by exact  incl_excl_corollary2 A HV KV AinHUK
have hOr1:(2*(A∩ I).card ≥ I.card) ∨ (2*(B∩ I).card ≥ I.card):= by exact incl_excl_corollary2 I A B IinAUB
have AIcom: A∩ I=I∩ A:= by exact inter_comm A I
have BIcom: B∩ I=I∩ B:= by exact inter_comm B I
have hOr1:(2*(I∩ A).card ≥ I.card) ∨ (2*(I∩ B).card ≥ I.card):= by rw[AIcom.symm, BIcom.symm]; exact hOr1

by_cases hAI: 2*(I∩ A).card ≥ I.card
by_cases hBH: 2*(HV∩ B).card ≥ B.card



--have h1: ((4*p* ((H.verts ∪  K.verts).toFinset.card )*(Rel.interedges (H⊔ K).Adj A B).card) :ℕ )≥ ((A.card*B.card* ((H.verts ∩  K.verts).toFinset.card )):ℕ ):= by
--  exact cut_dense_union_after_wlog G H K hNonempty p HCutDense KCutDense I A B hUnion  hI hAI hBH

have hineq: a*e≥ v*b:= by
  rw[he, ha, hb, hv];
  exact cut_dense_union_after_wlog G H K hNonempty p HCutDense KCutDense I A B hUnion  hI hAI hBH
have hineqfrac: (a / b+1) * e   ≥ v:= by exact nat_div_ge a b e v hineq hbpos
rw [hq, ha.symm, hb.symm, he.symm, hv.symm]
exact hineqfrac


have hBK:(2 * (KV ∩ B).card ≥ B.card):= by exact Or.resolve_left hOr2 hBH
have hineq: a*e≥ v*b:= by
  rw[he', ha', hb', hv];
  exact cut_dense_union_after_wlog G K H hNonempty' p KCutDense HCutDense I A B hUnion'  hI' hAI hBK
have hineqfrac: (a / b+1) * e   ≥ v:= by exact nat_div_ge a b e v hineq hbpos
rw [hq, ha.symm, hb.symm, he.symm, hv.symm]
exact hineqfrac

have  hBI:2*(I∩ B).card ≥ I.card:= by exact Or.resolve_left hOr1 hAI
by_cases hAH: 2*(HV∩ A).card ≥ A.card
have hineq: a*e≥ v*b:= by
  rw[he'', ha, hb, hv'];
  exact cut_dense_union_after_wlog G H K hNonempty p HCutDense KCutDense I B A hUnion''  hI hBI hAH
have hineqfrac: (a / b+1) * e   ≥ v:= by exact nat_div_ge a b e v hineq hbpos
rw [hq, ha.symm, hb.symm, he.symm, hv.symm]
exact hineqfrac

have hAK:(2 * (KV ∩ A).card ≥ A.card):= by exact Or.resolve_left hOr3 hAH
have hineq: a*e≥ v*b:= by
  rw[he''', ha', hb', hv'];
  exact cut_dense_union_after_wlog G K H hNonempty' p KCutDense HCutDense I B A hUnion'''  hI' hBI hAK
have hineqfrac: (a / b+1) * e   ≥ v:= by exact nat_div_ge a b e v hineq hbpos
rw [hq, ha.symm, hb.symm, he.symm, hv.symm]
exact hineqfrac

end SimpleGraph
