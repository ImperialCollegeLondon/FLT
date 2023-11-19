# A Lean formalisation of Fermat's Last Theorem

## What is Fermat's Last Theorem?

[Fermat's Last Theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem) is a simple-looking mathematical statement about positive integers, which was raised by Pierre Fermat in 1637, and finally resolved over 350 years later by Andrew Wiles, assisted by Richard Taylor. One extraordinary thing about the proof is that even though the statement of the theorem involves only counting numbers (the simplest of mathematical objects), all known proofs of the theorem involve much deeper mathematics, including but not limited to the theory of elliptic curves, modular forms and Galois representations. Moreover, even though the statement of the theorem is arithmetic, the proof uses algebra, geometry, analysis and other branches of mathematics. The proof, if written out in full, would occupy several thousand pages.

## What is Lean?

[Lean](https://lean-lang.org/) is an *interactive theorem prover*, meaning that it is a programming language which knows the axioms of mathematics and the rules of logic, and is expressive enough to understand modern proofs in mathematics.

## What is this project?

The goal of this project is to teach Lean a proof of Fermat's Last Theorem. It will not be the original Wiles/Taylor-Wiles proof, but rather a "newer" proof using more recent developments due to Khare-Wintenberger, Kisin and many other people. However at its heart the proof we are formalising still uses the same theme -- the revolutionary idea (conjectured by Mazur and Tilouine and proved in many cases by Wiles) that a deformation ring R is isomorphic to a Hecke algebra T. For more information about the technical mathematics being taught to Lean, see the [blueprint](blueprint) of the project, an ongoing exposition in both LaTeX and Lean of the mathematical details being formalised.

## Why are you doing this?

Here are several reasons.

1) Digitising things means that you can use them in new ways. Without the digitisation of music there would be no Spotify, for example. This project will involve digitising a lot of mathematical objects which are used in modern research. This project will be working closely with [`mathlib`](https://github.com/leanprover-community/mathlib4), Lean's mathematical library, in order to increase the coverage of this library. It is my hope that digitising mathematics in this way will enable humans to discover new ways of manipulating and communicating mathematics. Examples of possible applications would include interactive error-free textbooks, mathematical papers which can be "unfolded" in as much detail as a reader desires (right down to the axioms of mathematics if necessary), interactive mathematical games for teaching, and so on.

2) At the time of writing, large language models such as ChatGPT have got very good at mimicking humans, however their ability to *reason* (i.e., to think logically rather than just parrotting information) is in general poor. Lean is at the opposite end of the scale -- it cannot write code itself, but it is extremely logically accurate. One current target in AI is to construct a system which can help humans with research level mathematical proofs. An ambitious project such as this one will generate a lot of Lean code, which can be used as high-level training data or in conjunction with a future large language model, to get closer to this target. Another target would be a highly trained chatbot which could give accurate answers to PhD students interested in learning topics such as algebraic geometry or algebraic number theory; students might well find such a system more convenient when trying to learn the basics of such a technical theory.

3) Freek Wiedijk maintains a [web page](https://www.cs.ru.nl/~freek/100/) comprising of 100 challenge problems for computer formalisation. Currently 99 of the 100 problems in the list of challenges have been formalised; the one remaining is Fermat's Last Theorem. Thus a fully formal proof of the theorem would represent the completion of this benchmark.
