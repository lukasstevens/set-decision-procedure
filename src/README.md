# A Verified Decision Procedure for MLSS
This directory contains the formalisation of a tableau calculus for MLSS.

## Running the Formalisation
The formalisation uses Isabelle2022 which is available on [isabelle.in.tum.de](https://isabelle.in.tum.de).
It builds on some entries of the Archive of Formal Proofs (see [www.isa-afp.org/download](https://www.isa-afp.org/download) for installation instructions).
You can build the session with
```
isabelle build -d $AFP -d . Set_Proc
```
where `$AFP` is the directory where you installed the Archive of Formal Proofs.
The session can be opened interactively by running
```
isabelle jedit -d $AFP -d . -R Set_Proc
```

## Structure
The formalisation is split into several files:
- `Logic.thy` contains the datatype of propositional formulae.
- `HF_Extras.thy` contains auxiliary material for Hereditarily Finite Sets.
- `Set_Semantics.thy` defines the syntax and semantics of MLSS.
- `Set_Calculus.thy` introduces the tableau calculus for MLSS.
- `Realisation.thy` contains the definition of the realization function and additional proofs that were not discussed in the paper.
- `Set_Proc.thy` proves soundness and completeness of the calculus. It also gives a bound on the number of formulae in a branch. Finally, it defines the decision procedure and proves its soundness, completeness, and termination.
- The files `Typing_Defs.thy`, `Typing.thy`, and `Typing_Urelems.thy` introduce a light-weight type system for MLSS where the type of a term is a natural number.
  Assuming that the urelements are of type `'a`, we have that type `0` corresponds to `'a`, type `1` to `'a set`, type `2` to `'a set set`, etc. 

## Difference in Notation
The presentation in the paper takes some shortcuts to streamline the presentation.
Here are the most important differences:
- The constructors of a formula don't use the logical operators but are `Atom`, `Neg`, `And`, and `Or`.
- The function `⊧` is called `interp` instead.
- The functions `▷`, `⩥`, and `▷*` are called `lexpands`, `bexpands`, and `expandss`, respectively.
- The function for term-for-term substitution is called `subst_tlvl`.
- The realisation function is defined more abstractly in the locale `realisation` in the file `Realisation.thy`. In the paper, we only showed an instantiation.
