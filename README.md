This repository contains a formalization of the following theorem in Lean4: 

Theorem: 
Fix eps > 0, and let C be sufficiently large compared to eps. Let P be a path with d ≥ C edges. For any graph G with e(G) ≥ eps * d * |G| having no copies of P, it is possible to delete (eps * e(G)) edges to get a graph H each of whose connected components has a cover of order ≤ Cd.

This theorem is found in the file Main_Theorem.lean. 



The project can be compiled remotely on GitHub codespaces by following the following: 

- Open https://github.com/alja123/hyperstabilityES while logged into a GitHub account.

- Click the green [<> Code] button and select [Create codespace on master]. This should open up a fresh window with a codespace.

- In the terminal section on the bottom right, type: 
`code --install-extension leanprover.Lean4`
Wait for it to stop installing Lean.

- In the terminal section on the bottom right, type: 
`code Main_Theorem.lean`

- Now follow the various prompts that the installer gives. Specifically:
    - A dialog will pop up saying "Lean is not installed. Do you want to install Lean's version manager Elan and a recent stable version of Lean 4?". Select [Install Elan and Lean 4]. 
    - At some point, on the very bottom right of the screen a box should pop up saying "Lake configuration changed". Click [Restart Lean] in that box. Afterwards wait for it to stop doing anything. 
    - At the top right of the screen, there should be a panel called "Lean Infoview", which will be asking "Imports are out of date and must be rebuilt; use the "Restart File" command in your editor". Click the [Restart File] button at the bottom right of the Lean Infoview panel.

- Now wait a *very* long time while everything compiles (around an hour for me).  

- When it is done, Lean Infoview should display: 
    ```
    Main_Theorem.lean:3:0
    No info found.
    All Messages (0)
    ```
The fact that it didn't generate error or warning messages means that it compiled successfully. 
