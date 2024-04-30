---
author: 'Kevin Buzzard'
category: 'project announcement'
date: 2024-03-24 07:42:45+00:00
description: ''
has_math: false
link: ''
slug: FLT-announcement
tags: ''
title: The Fermat's Last Theorem Project
type: text
---

Kevin Buzzard discusses the project to prove Fermat's Last Theorem in Lean.

<!-- TEASER_END -->
# Introduction

Fermat's Last Theorem (FLT) is the claim that some equation or other has no solutions in positive integers. The equation has no applications, either theoretical or practical. So why did the announcement of its solution by Andrew Wiles in 1993 make the front page of the New York Times?

One aspect of FLT is that the theorem is ridiculously simple to *state* ($x^n+y^n=z^n$ has no solutions in positive integers if n>=3) (*TODO* maths mode?), and yet it was incredibly hard to *prove* (indeed, it took the mathematical community over 350 years). Thus it serves as a great reminder of how profound mathematics is. But what really justifies the interest in the problem is that over the past few centuries a huge amount of mathematical theory has been developed and invented/discovered in an attempt to resolve the problem, and this mathematics has had applications from cryptography to physics. Indeed Wiles' breakthrough work in the Langlands Program which ultimately resolved FLT was of course motivated by FLT, and historically many other developments in algebraic number theory (for example the theory of factorization in number fields, and the arithmetic of cyclotomic fields) have been at least partly motivated by the desire to shed more light on the problem.

The work of Wiles, completed by Taylor--Wiles, was built upon a gigantic edifice of 20th century mathematics, and furthermore the fundamental technique which Wiles introduced (a "modularity lifting theorem") has been conceptually simplified and hugely generalised in the 30 years following the publication of the original papers; the area continues to be a very active one today. [Frank Calegari's 2022 ICM paper](https://arxiv.org/abs/2109.14145) is a survey of what has happened since, and what questions remain open. The fact that the area is still active is part of my motivation to "formalise" the proof. But what is formalisation?

# Formalisation of mathematics

Formalisation of mathematics is the art of translating paper mathematics into a computer programming language rich enough to understand the concepts of theorems and proofs. These programming languages, also called interactive theorem provers (ITPs), have been around for decades. Over the last few years however, the area seems to have captured the attention of parts of the mathematics community. We have now seen several examples of modern mathematics being formalised (by mathematicians, rather than computer scientists) in real time, the most recent of which (at the time of writing) is Tao et al's formalisation of his work with Gowers, Green and Manners resolving the polynomial Freiman--Ruzsa conjecture. Success stories like these might lead casual observers to believe that ITPs such as Lean are now ready to formalise all modern mathematics. However the truth is far more sobering. In *some* areas of mathematics, for example additive combinatorics, we now have extensive evidence that modern breakthroughs can be formalised in real time. However, I attend the London Number Theory Seminar on a regular basis, and most weeks I note that Lean does not know enough modern mathematical definitions to even *state* the results announced in the seminar, let alone to check their proofs.

The fact that number theory is still "behind" in this regard is one of my main motivations to embark on a formalisation of a modern proof of FLT. Once the project is finished, Lean will understand the concepts of automorphic forms and representations, L-functions, Galois representations, potential automorphy, modularity lifting theorems, the arithmetic of varieties, class field theory, arithmetic duality theorems, Shimura varieties and many other concepts used in modern algebraic number theory; formalising the *statements* of what is happening in my own area of expertise will no longer be science fiction. And why might one want to do this? Well, if we are to believe some computer scientists, the exponential growth in AI should one day translate into computers being able to help mathematicians do their work. But what chance does this have of coming true if computers cannot even *understand what we are doing*?

# The FLT project

The Fermat's Last Theorem formalisation project is [now open](https://github.com/ImperialCollegeLondon/FLT). Perhaps more interesting than a link to a github repository is the [blueprint graph](https://legendary-couscous-yrrvjlg.pages.github.io/blueprint/dep_graph_document.html) (**TODO** couscous in link) giving an indication of the current progress of the proof. If you are a mathematician you might also be interested in the [blueprint](https://legendary-couscous-yrrvjlg.pages.github.io/blueprint/index.html) itself, which contains an in-progress LaTeX write-up of the route we shall be taking. Experts interested in the precise details of the route we shall be taking can refer to Chapter 4 of the blueprint for the details.

I am being funded for the first five years of the project by EPSRC grant blah (**TODO**). During this time, my first goal is to *reduce* FLT to claims which were known to mathematicians by the end of the 1980s. I am quietly confident that we will succeed in this aim. But who is "we"?

# Crowd-sourcing mathematics

I cannot formalise FLT alone. Indeed there are several parts of the arguments where I understand the basic principles but have never checked the details carefully, and on top of this there are two inputs (Langlands' work on cyclic base change for GL_2, and the work of Jacquet-Langlands relating automorphic representations for GL_2 with automorphic representations for inner forms of GL_2) which I have only the most superficial understanding of. However this is where one begins to see the benefits of a formalisation project. I will be able to explicitly *state* the results I need in Lean, and pass them on to others. The blueprint software we're using was developed by Patrick Massot to enable collaboration and was first used by him to formalise a modern proof of Smales' [sphere eversion theorem](link). The blueprint framework, combined with the Lean Zulip chat, a high-powered research forum where mathematicians and computer scientists can collaborate in real time, posting code and mathematics, have proved to be decisive here. People interested in watching progress of the project can occasionally check the blueprint graph (**TODO** link); people interested in contributing themselves should make themselves known on the FLT stream on the Lean Zulip. 

***********

The blueprint software was developed by Patrick Massot, motivated by his own work formalising 

*********
Algebraic number theory is certainly not the only area of mathematics where we cannot state the theorems which are currently being proved in mathematics departments today. I would urge people working in other areas of mathematics to come up with challenges and consider writing blueprints which can be used as roadmaps to formalise these challenges.

***********

 There seem to be two viable approaches to teaching computers what is happening in mathematics today. The first is to feed a bunch of modern papers into a large language model and to hope that enough of the ideas sink in for these systems to go beyond the "stochastic parrot" mode which we see so often nowadays when they attempt to do mathematics. The second is to teach an ITP some modern results; this is the route I have decided to take. Perhaps in the future some combination of the two approaches is what will be decisive.