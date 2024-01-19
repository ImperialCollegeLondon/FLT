# A Lean formalisation of Fermat's Last Theorem

## What is Fermat's Last Theorem?

Fermat's Last Theorem (see [https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem) for more details) is the claim that if x,y,z,n are positive integers and n is at least 3, then x^n + y^n can never equal z^n. The question is so simple that Diophantus, who lived nearly 2000 years ago, could have understood it. It was raised by Pierre de Fermat in 1637, and finally resolved over 350 years later by Andrew Wiles, assisted by Richard Taylor. One extraordinary thing about the proof is that even though the statement of the theorem involves only the counting numbers (some of the simplest mathematical objects), all known proofs involve much deeper mathematics, including but by no means limited to the theory of elliptic curves, modular forms, finite flat group schemes, and Galois representations. Moreover, even though the theorem statement is of a highly arithmetic nature, all known proofs use many other branches of mathematics, borrowing from algebra, geometry, and both real and p-adic analysis. Any of the known proofs, if written out in full from the axioms of mathematics, would occupy several thousand pages.

## What is Lean?

Lean (see [https://lean-lang.org/](https://lean-lang.org/) for more details) is an *interactive theorem prover*, meaning that it is a programming language which knows the axioms of mathematics and the rules of logic, and is expressive enough to understand modern mathematical proofs. Many other theorems provers exist (for example Coq, Isabelle, Mizar, Metamath, Agda, HOL Light,...); the reason we will be using Lean is that projects such as the Liquid Tensor Experiment [https://leanprover-community.github.io/liquid/](https://leanprover-community.github.io/liquid/), the Sphere Eversion Project [https://leanprover-community.github.io/sphere-eversion/](https://leanprover-community.github.io/sphere-eversion/) and many others have convinced us that Lean will be able to handle the proof.

## What is this project?

The goal of this project is to teach Lean a proof of Fermat's Last Theorem. This will involve translating thousands of pages of "informal mathematics" (i.e. mathematics papers or textbooks) into "formal mathematics" (i.e. Lean's language). We will manage this open source project using Patrick Massot's blueprint software; the blueprint will slowly grow into a map of the theorem and a LaTeX documentation of the proof. At the time of writing (December 2023) the AI tools available to humanity are not really able to help with the formalisation aspect of this task, so most of the work will be done by humans. It will be interesting to see how different things will be in September 2029 as the grant ends.

## Why are you formalising a proof of Fermat's Last Theorem?

Here are several reasons.

1) Digitising things means that you can use them in new ways. Without the digitisation of music there would be no Spotify. This project will involve digitising a whole bunch of mathematical objects and techniques which are used in modern research. More foundational theories needed for this project will be PR'ed to [`mathlib`](https://github.com/leanprover-community/mathlib4), Lean's mathematical library. It is my hope that digitising huge chunks of modern mathematics in this way will enable humans to explain mathematics in new ways. Examples include interactive error-free textbooks, mathematical papers which can be interactively "unfolded down to the axioms", interactive mathematical games for teaching and so on.

2) At the time of writing (December 2023), large language models such as ChatGPT have got very good at mimicking humans, however their ability to *reason* (i.e., to think logically rather than just being stochastic parrots) is poor. Lean is at the opposite end of the scale -- it cannot write code itself, but it is extremely logically accurate. One current target in AI is to construct a system which can help humans with research level mathematical proofs. An ambitious project such as this one will generate a lot of Lean code, which can be used as high-level training data or in conjunction with a future large language model, to get perhaps closer to this target of proof assistants actually *assisting* across mathematics. Another possible application would be a highly trained chatbot which could give accurate answers to PhD students interested in learning topics such as algebraic geometry or algebraic number theory; students might well find such a system more convenient when trying to learn the basics of such a technical theory.

3) Despite a lot of the hype currently surrounding large language models and the fact that they can write code, it is still the case that many of the standard objects studied in modern number theory have not even been defined in Lean or any other theorem prover. This means that currently it is not even possible to *state* many of the recent results proved in number theory, let alone prove them, in Lean or in any other theorem prover. This project will go some way towards fixing this problem by forcing us to define many modern number-theoretic objects.
 
4) Freek Wiedijk maintains a [web page](https://www.cs.ru.nl/~freek/100/) comprising of 100 challenge problems for computer formalisation. Currently 99 of the 100 problems in the list of challenges have been formalised; the one remaining is Fermat's Last Theorem. Thus a fully formal proof of the theorem would represent the completion of this benchmark.

## When does the project start?

I (Kevin Buzzard) will be devoting a lot of time to this project once the grant kicks in, which is October 2024, although there are currently some blue nodes (meaning nodes suitable for a small project), so in some sense the formalisation has started already.

## Will you start with the basics?

No! This project will start everywhere at once. We're going to build from both ends. The project's will have achieved its initial goal if it successfully reduces Fermat's Last Theorem (initially proved in the 1990s) to a collection of several far more complex mathematical claims, all of which were known by the end of the 1980s. I believe that this reduction will be achieved by September 2029 when the EPSRC grant runs out and I hope that we will have got much further. We'll also work up from the basics, PRing stuff to Lean's mathematics library `mathlib` [https://github.com/leanprover-community/mathlib4/](https://github.com/leanprover-community/mathlib4/) as we go, and eventually we'll meet in the middle. A preliminary early goal will be to *state* all of the major claims which we shall initially be assuming (for example the existence of Galois representations associated to certain automorphic forms). I am hoping that this project will be a good source of smaller Lean projects suitable for PhD students in number theory who are interested in learning the language.

## Which proof will you formalise?

It will not be the original Wiles/Taylor-Wiles proof, but rather a "newer" proof which takes into account more recent developments due to Khare-Wintenberger, Kisin and many other people. However at its heart the proof we are formalising still uses the same theme -- the revolutionary idea (conjectured by Mazur and Tilouine and proved in many crucial cases by Wiles) that a deformation ring R is isomorphic to a Hecke algebra T. More details of the actual modularity lifting theorem which we will formalise will come later.

The route we are taking was essentially completely designed by Richard Taylor and when I have more time I will explain it in more detail.
