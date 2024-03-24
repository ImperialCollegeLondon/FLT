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

Fermat's Last Theorem (FLT) is the claim that some equation or other has no solutions in positive integers. The equation has no applications, either theoretical or practical. So why did its solution by Andrew Wiles in 1993 make the front page of the New York Times?

One aspect of FLT is that the question is ridiculously simple to *state*, and yet it seems incredibly hard to *prove* (indeed, it took the mathematical community over 350 years). Thus it serves as a great reminder of how profound mathematics is. But what really justifies the interest in the problem is that over the past few centuries a huge amount of mathematics has been developed and discovered in an attempt to resolve it, and this mathematics has had applications from cryptography to physics. Indeed Wiles has said that, unsurprisingly, his breakthrough work in the Langlands Program was motivated by FLT, and historically many other developments in algebraic number theory (for example the theory of factorization in cyclotomic fields) have been motivated by the same desire.

The work of Wiles and Taylor-Wiles built upon a gigantic edifice of 20th century mathematics, and furthermore the fundamental technique which it introduced (a "modularity lifting theorem") has been simplified and hugely generalised in the 30 years following the publication of the original papers; the area continues to be a very active one today. [Frank Calegari's 2022 ICM paper](https://arxiv.org/abs/2109.14145) is a survey of what has happened since.

# Formalisation of mathematics

Formalisation of mathematics is the art of translating paper mathematics into a computer programming language rich enough to understand the concepts of theorems and proofs. Over the last few years, the area seems to have captured the attention of parts of the mathematics community. We have seen several examples of modern mathematics being formalised in real time, the most recent example of which was Tao et al's formalisation of his work with Gowers, Green and Manners resolving the polynomial Freiman-Ruzsa conjecture. Bystanders might be forgiven for thinking that interactive theorem provers like Lean are now ready to deal with all modern mathematics. However the truth is far more sobering. In *some* areas of mathematics, for example additive combinatorics, we now have extensive evidence that modern breakhroughs can be formalised in real time. However, I attend the London Number Theory Seminar week in week out, and essentially every week I note that Lean does not know enough modern mathematical definitions to even *state* the results announced in the seminar, let alone to check the proofs.

The fact that number theory is still "behind" in this regard is one of my main motivations to embark on a formalisation of a modern proof of FLT. Once the project is finished, Lean will understand the concepts of automorphic forms and representations, L-functions, Galois representations, potential automorphy, modularity lifting theorems, Shimura varieties and many other fancy concepts used in modern algebraic number theory; we will be closer to my preliminary goal of being able to formalise *statements* of what is happening in my own area of expertise. And why might one want to do this? Well, if we are to believe some computer scientists, the exponential growth in AI should one day translate to computers being able to help mathematicians do their work. But what chance does this have of coming true if computers cannot even *understand what we are doing*?

# The FLT project

The Fermat's Last Theorem formalisation project is [now open](https://github.com/ImperialCollegeLondon/FLT). Perhaps more interesting than a link to a github repository is the [blueprint graph](https://legendary-couscous-yrrvjlg.pages.github.io/blueprint/dep_graph_document.html) **TODO** couscous giving an indication of the current progress of the proof. If you are a mathematician you might also be interested in the [blueprint](https://legendary-couscous-yrrvjlg.pages.github.io/blueprint/index.html) itself, which contains an in-progress LaTeX write-up of the route we shall be taking. Experts interested in the precise details of the route we shall be taking can refer to chapter 4 of the blueprint for the details. Note that whilst our main applications are in the 2-dimensional case, we will work in the n-dimensional case whenever we can.

I am being funded for the first five years of the project by EPSRC grant [blah] **TODO**. During this time, my first goal is to *reduce* FLT to claims which were known to mathematicians by the end of the 1980s. I am quietly confident that we, the community, will succeed in this aim. 