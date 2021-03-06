# Calculating Certified Compilers for Non-Deterministic Languages [![Build Status](https://travis-ci.org/pa-ba/calc-comp-rel.svg?branch=master)](https://travis-ci.org/pa-ba/calc-comp-rel)


This repository contains the supplementary material for the paper
["Calculating Certified Compilers for Non-Deterministic Languages"](http://www.diku.dk/~paba/pubs/files/bahr15mpc-preprint.pdf)
by Patrick Bahr.  The material includes Coq formalisations of all
calculations in the paper. In addition, we also include Coq
formalisations for calculations that were mentioned but not explicitly
carried out in the paper. The Coq development also proves the
underlying calculation framework that is used by the calculation.

Paper vs. Coq Proofs
--------------------

The Coq proofs proceed as the calculations in the paper. There is
however, one minor technical difference due to the nature of the Coq
system. The Coq files contain the final result of the calculation, and
thus do not reflect the *process* of discovering the definition of the
compiler and the VM. That is, the files already contain the full
definitions of the compiler and the virtual machine. But we used the
same methodology as described in the paper to *develop* the Coq
proofs. This is achieved by initially defining the Code data type as
an empty type, defining the VM relation as an empty relation
(i.e. with no rules), and defining the compiler function using the
term "Admit". This setup then allows us to calculate the definition of
the Code data type, the VM, and the compiler as described in the
paper. Alternatively, the calculations can also be read as a post hoc
verification of a given compiler.

File Structure
--------------

Below we list the relevant Coq files for the calculations in the
paper:

 - [Random.v](Random.v): toy language that generates random numbers
   (sections 2 - 4)
 - [Interrupts.v](Interrupts.v): Hutton & Wright's language with
   interrupts (section 5)

In addition we also include calculations for the following languages:


 - [HuttonWright.v](HuttonWright.v): Hutton & Wright's language with
   interrupts but using their original compiler and VM from the paper
   ["What is the meaning of these constant interruptions?"](http://dx.doi.org/10.1017/S0956796807006363)
 - [StateGlobal.v](StateGlobal.v): language with interrupts and global
   state
 - [StateLocal.v](StateLocal.v): language with interrupts and local
   state
 - [Arith.v](Arith.v): simple arithmetic language
 - [Exceptions.v](Exceptions.v): arithmetic language extended with
   exceptions

The reasoning framework that is used by the abovementioned
calculations is formalised in [Machine.v](Machine.v). The calculations
do not use this formalisation directly, but instead invoke the proof
tactics defined in [Tactics.v](Tactics.v). These tactics allow us to
write the proofs in the calculational style that is presented in the
paper.

Technical Details
-----------------

### Dependencies

- To check the proofs: Coq 8.4pl5
- To step through the proofs: GNU Emacs 24.3.1, Proof General 4.2

### Proof Checking

To check and compile the complete Coq development, you can use the
`Makefile`:

```shell
> make
```
