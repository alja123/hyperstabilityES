Dear Prof Kevin Buzzard,

I'm an associate professor at UCL working in combinatorics. A few months ago I was inspired to learn Lean by formalizing a theorem from a preprint that I am working on. I've now successfully gotten it to compile without errors or 'sorrys', and am now in the process of finalizing the paper and repository before posting on arXiv. The pdf of the preprint is attached below, and the Githup repository is https://github.com/alja123/hyperstabilityES

As I understand, this will be one of the first theorems to come out simultaneously with its formalization, so I wanted to get in touch about whether you have any thoughts about how a paper like this should look (both the bits of the pdf about Lean and the Github repository)? Some specific questions that come to mind: 

- What sort of things should one do/say to justify that the proof is actually correct? Is it sufficient that the code compiles and doesn't contain any 'sorry's or are there other potential ways one could hide an error in the proof?

- The code currently generates a lot of warnings. Are these okay, or should the standard be zero warnings?

- Is it okay that the project uses an old version of Mathlib (from May this year)? I somehow hadn't realized that I should be keeping an eye out for updates in Mathlib until I was basically done with the project. I tried compiling it with the latest version - with a lot of fairly routine changes it should be possible to get it to work, though I wasn't sure if it was necessary.

- What are useful things to write for people to be able to check that the formalization actually does what it says it does? In the main lean file [Main_Theorem.lean], I tried to explain what the various lines do, while in the pdf I have a short section describing the formalization. In the statement of the theorem I stuck entirely with definitions from Mathlib - was this a good idea or would it have been better to write it using custom definitions in order to get a more concise statement? Would something else be useful (e.g. some sort of guide for how to install Lean).

Any other thoughts you have would be greatly appreciated also. If you'd rather meet in person in Imperial/UCL rather than composing a long email let me know - from my side it would be nice to link up with the formalization community in London. 

Best wishes,
Alexey

PS. Apologies for how messy most of the code is - some of it is from May when I knew basically zero Lean.


-- This module serves as the root of the `MyProject` library.
-- Import modules here that should be built as part of the library.
import «hyperstabilityES».Basic