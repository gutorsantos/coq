# Proofs Repository

## Introduction

This repository contains proofs of theorems, including sorting algorithms, made throughout Computational Logic 1 discipline. 
During the course it was difficult to find example codes for a better understanding of implementing solutions using Coq.
Thus this repository is intended to be a source of examples for those who need it.

## Coq

Coq is an interactive theorem prover first released in 1989. It allows for expressing mathematical assertions, mechanically checks proofs of these assertions, 
helps find formal proofs, and extracts a certified program from the constructive proof of its formal specification. 
Coq works within the theory of the calculus of inductive constructions, a derivative of the calculus of constructions. 
Coq is not an automated theorem prover but includes automatic theorem proving tactics (procedures) and various decision procedures. 

Coq provides a specification language called Gallina ("hen" in Latin, Spanish, Italian and Catalan). Programs written in Gallina have the weak normalization 
property, implying that they always terminate. This is a distinctive property of the language, since infinite loops (non-terminating programs) are common in other 
programming languages, and is one way to avoid the halting problem.

Sourced by [Wikipedia](https://en.wikipedia.org/wiki/Coq).

## Files

### desafio.v

This file includes an introductory logic problem.

There are only two types of inhabitants on an island: the honest ones, who always speak the truth; and the dishonest ones, who always lie. 
You find two inhabitants of this island, named João and José. João says that José is dishonest. Joseph says "Neither John nor I are dishonest". 
Can you determine which one is honest and which one is dishonest?

### inducao_equivalencia.v

This file has the purpose of prove the **Equivalence between the Principle of Mathematical Induction and the Principle of Strong Induction**.

### insertion_sort.v

This file proves the correction of insertion sorting algorithm. In it, we will present the entire process of formalizing the insertion sort algorithm.

### mergesort.v

This file proves the correction of merge sorting algorithm. In it, we will present the entire process of formalizing the merge sort algorithm.
