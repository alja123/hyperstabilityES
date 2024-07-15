


theorem new
(hT : T.IsTree)(hDeg : G.minDegree ≥ k)(hSize:T.edgeFinset.card=k)(vG:VG)(uT:VT):
∃ (f: T →g G), (f vT=vG)∧ (Function.Injective f.toFun) := by
induction' k  with  k ih
case zero
have h3: Finset.card T.edgeFinset + 1 = Fintype.card VT := by exact IsTree.card_edgeFinset hT
have h2:T.edgeFinset.card+1=1 := by exact Nat.add_eq_right.mpr hSize
have h1:Fintype.card VT=1 := by calc
  Fintype.card VT=T.edgeFinset.card+1:= by exact id h3.symm
  _=1:= by exact h2


have h5hkjh:∃ (f: T →g  G), (f vT=vG)∧ (Function.Injective f.toFun) :=
by exact inj_hom_from_graph_with_one_vertex G T vT vG h1
exact  h5hkjh

case succ

let VTT: Finset VT:= Finset.univ
let VTS: Finset VT:= ({vT}: Finset VT)
have h1Size: Finset.card VTT=Fintype.card VT:= by exact rfl
have h2Size: Finset.card VTS=1:= by exact rfl


let VT': Finset VT:=  VTT \ VTS
have h3Size: Finset.card VT'=(Finset.card VTT)-(Finset.card VTS):= by
  refine card_sdiff ?h
  exact subset_univ VTS




let typeVT':= { x // x ∈ VT' }

let T':SimpleGraph typeVT':= by exact induce VT' T
have hsiz: (Fintype.card typeVT')=(Finset.card VT'):= by exact Fintype.card_coe VT'

have hVT'Size: Fintype.card VT'=Fintype.card VT -1:= by apply?



sorry
