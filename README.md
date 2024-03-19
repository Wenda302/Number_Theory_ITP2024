# Number Theory (ITP 2024)
The accompanying code for the submission "Formalising Half of a Graduate Textbook on Number Theory" to ITP 2024.

We have formalised Chapter 1,2,3, and 7 of Apostol's [Modular Functions and Dirichlet Series in Number Theory](https://www.springer.com/gp/book/9780387971278). Theory files that roughly correspond to the named chapters are as follows:
- Chapter 1, *Elliptic functions*
    - [Complex_Lattices.thy](Complex_Lattices.thy)
    - [Elliptic_Functions.thy](Elliptic_Functions.thy)
    - [Klein_J.thy](Klein_J.thy)
    - [Fourier_Expansion_Mero_UHP.thy](Fourier_Expansion_Mero_UHP.thy)
    - [Modular_Fourier.thy](Modular_Fourier.thy)
- Chapter 2, *The Modular group and modular functions*
    - [Modular_Group.thy](Modular_Group.thy)
    - [Modular_Forms.thy](Modular_Forms.thy)
    - [Meromorphic_Forms_Valence_Formula_Proof.thy](Meromorphic_Forms_Valence_Formula_Proof.thy)
    - [Modular_Forms_Valence_Formula.thy](Modular_Forms_Valence_Formula.thy)
- Chapter 3, *The Dedekind eta function*
    - [Dedekind_Sums.thy](Dedekind_Sums.thy)
    - [Siegel_Dedekind_Eta.thy](Siegel_Dedekind_Eta.thy)
    - [Dedekind_Eta_Function.thy](Dedekind_Eta_Function.thy)
- Chapter 7, *Kronecker's theorem with applications*
    - [Kronecker_Theorem.thy](Kronecker_Theorem.thy)

This repository is compatible with [Isabelle2023](https://isabelle.in.tum.de) with [AFP2023](https://www.isa-afp.org/download/) installed.

The material can be built in batch mode with `isabelle build -D .` or explored interactively in Isabelle/jEdit – ideally with a pre-built session image for its requirements, such as `isabelle jedit -l Zeta_Function *.thy`.
