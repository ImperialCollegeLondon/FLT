# A Lean formalisation of Fermat's Last Theorem

## What is Fermat's Last Theorem?

Fermat's Last Theorem (see [https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem) for more details) is the claim that if x,y,z,n are positive integers and n is at least 3, then x^n + y^n can never equal z^n. The question is so simple that Diophantus, who lived nearly 2000 years ago, could have understood it. The question was raised by Pierre de Fermat in 1637, and finally resolved over 350 years later by Andrew Wiles, assisted by Richard Taylor. One extraordinary thing about the proof is that even though the statement of the theorem involves only the counting numbers (some of the simplest mathematical objects), all known proofs involve much deeper mathematics, including but by no means limited to the theory of elliptic curves, modular forms, finite flat group schemes, and Galois representations. Moreover, even though the theorem statement is of a highly arithmetic nature, the proof uses many other branches of mathematics, borrowing from algebra, cohomology, geometry, and both real and p-adic analysis. The proof, if written out in full from the axioms of mathematics, would occupy several thousand pages.

## What is Lean?

Lean (see [https://lean-lang.org/](https://lean-lang.org/) for more details) is an *interactive theorem prover*, meaning that it is a programming language which knows the axioms of mathematics and the rules of logic, and is expressive enough to understand modern mathematical proofs. Many other theorems provers exist (for example Coq, Isabelle, Mizar, Metamath, Agda, HOL Light,...); the reason we will be using Lean is that it currently has the most mathematician users, and evidence already exists (for example the Liquid Tensor Experiment [https://leanprover-community.github.io/liquid/](https://leanprover-community.github.io/liquid/) that Lean is able to handle proofs at the required level of complexity.

## What is this project?

The goal of this project is to teach Lean a proof of Fermat's Last Theorem. This will involve translating thousands of pages of "informal mathematics" (i.e. mathematics papers or textbooks) into "formal mathematics" (i.e. Lean's language). At the time of writing (November 2023) the AI tools available to humanity are not really able to help with this task, so part of the project is sociological: will it be possible to persuade sufficiently many mathematicians to do this translation manually, so that the project can be finished within ten years or so? However, it will be interesting to reassess the abilities of AI tools in a few years' time, to see if they are any closer to being able to help.

## Why are you formalising a proof of Fermat's Last Theorem?

Here are several reasons.

1) Digitising things means that you can use them in new ways. Without the digitisation of music there would be no Spotify, for example. This project will involve digitising a lot of mathematical objects and techniques which are used in modern research. This project will be working closely with [`mathlib`](https://github.com/leanprover-community/mathlib4), Lean's mathematical library, in order to increase the coverage of this library. It is my hope that digitising mathematics in this way will enable humans to discover new ways of manipulating and communicating mathematics. Examples of possible applications would include interactive error-free textbooks, mathematical papers which can be "unfolded" in as much detail as a reader desires (right down to the axioms of mathematics if necessary), interactive mathematical games for teaching, and so on.

2) At the time of writing, large language models such as ChatGPT have got very good at mimicking humans, however their ability to *reason* (i.e., to think logically rather than just parrotting information) is in general poor. Lean is at the opposite end of the scale -- it cannot write code itself, but it is extremely logically accurate. One current target in AI is to construct a system which can help humans with research level mathematical proofs. An ambitious project such as this one will generate a lot of Lean code, which can be used as high-level training data or in conjunction with a future large language model, to get closer to this target. Another possible application would be a highly trained chatbot which could give accurate answers to PhD students interested in learning topics such as algebraic geometry or algebraic number theory; students might well find such a system more convenient when trying to learn the basics of such a technical theory.

3) Despite a lot of the hype currently surrounding large language models and the fact that they can write code, it is still the case that many of the standard objects studied in modern number theory have not even been defined in Lean or any other theorem prover. This means that currently it is not even possible to *state* many of the recent results proved in number theory, let alone prove them, in Lean or in any other theorem prover. This project will go some way towards fixing this problem by forcing us to define many modern number-theoretic objects.
 
4) Freek Wiedijk maintains a [web page](https://www.cs.ru.nl/~freek/100/) comprising of 100 challenge problems for computer formalisation. Currently 99 of the 100 problems in the list of challenges have been formalised; the one remaining is Fermat's Last Theorem. Thus a fully formal proof of the theorem would represent the completion of this benchmark.

## When does the project start?

I (Kevin Buzzard) will be devoting a lot of time to this project once the grant kicks in, which is October 2024, although in practice I hope to get going in April 2024 once my teaching for this year is completed.

## Will you start with the basics?

No! This project will start everywhere at once. In particular, part of the formalisation will "start from the top", with its first major goal being a reduction of Fermat's Last Theorem (initially proved in the 1990s) to a collection of several far more complex mathematical claims, all of which were known to humanity by the end of the 1980s. I hope that this reduction will be achieved by September 2029 when the EPSRC grant runs out. We will work down from this, and up from the basics, until we meet in the middle. A preliminary early goal will be to *state* the more complex claims which we shall initially be assuming, as they will be natural targets for either other human formalisation projects, or (as AI gets better) AI formalisation projects. The work coming up from the basics will be PRed into Lean's mathematics library `mathlib` [https://github.com/leanprover-community/mathlib4/](https://github.com/leanprover-community/mathlib4/). Note that in the near future there will be a list of
projects suitable for PhD students in number theory who are interested in learning Lean.

## Which proof will you formalise?

It will not be the original Wiles/Taylor-Wiles proof, but rather a "newer" proof which takes into accout more recent developments due to Khare-Wintenberger, Kisin and many other people. However at its heart the proof we are formalising still uses the same theme -- the revolutionary idea (conjectured by Mazur and Tilouine and proved in many crucial cases by Wiles) that a deformation ring R is isomorphic to a Hecke algebra T. More details of the actual modularity lifting theorem which we will formalise will come later.
