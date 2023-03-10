# A Verified Decision Procedure for MLSS
This repository contains the formalisation of a tableau calculus for MLSS.

## Branches
There are two different versions of the formalisation:
  * One without typing on the branch [`CADE`](https://github.com/lukasstevens/set-decision-procedure/tree/CADE) and
  * one with typing on the branch [`CADE_Typing`](https://github.com/lukasstevens/set-decision-procedure/tree/CADE_Typing).
You can compare the differences between the branches by executing
```
git diff CADE CADE_Typing -- src/
```

## Running the Formalisation
The formalisation uses Isabelle2022 which is available on [isabelle.in.tum.de](https://isabelle.in.tum.de).
It builds on some entries of the Archive of Formal Proofs (see [www.isa-afp.org/download](https://www.isa-afp.org/download) for installation instructions).
You can build the session with
```
isabelle build -d $AFP -d src/ $SESSION 
```
where `$AFP` is the directory where you installed the Archive of Formal Proofs and `$SESSION` is `Set_Proc` or `Set_Proc_Typing` depending on your branch (the master branch uses `Set_Proc`).
The session can be opened interactively by running
```
isabelle jedit -d $AFP -d src/ -R Set_Proc
```

## Browsing the Theory Files without Isabelle
If you don't want to install Isabelle, you can still browse the HTML presentation of the theories.
To get started, look at the overview theories of the branches:
  * [`Set_Proc_All.thy`](https://lukasstevens.github.io/set-decision-procedure/CADE/Set_Proc/Set_Proc/Set_Proc_All.html) on the `CADE` branch or
  * [`Set_Proc_All.thy`](https://lukasstevens.github.io/set-decision-procedure/CADE_Typing/Set_Proc/Set_Proc_Typing/Set_Proc_All.html) on the `CADE_Typing` branch.
