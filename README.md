This repository contains a formalization of the following theorem in Lean: 

Theorem: 
Fix eps > 0, and let C be sufficiently large compared to eps. Let P be a path with d ≥ C edges. For any graph G with e(G) ≥ eps * d * |G| having no copies of P, it is possible to delete (eps * e(G)) edges to get a graph H each of whose connected components has a cover of order ≤ Cd.

This theorem is found in the file hyperstabilityES\Main_Theorem.lean. 
