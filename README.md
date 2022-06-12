# Gödel's Theorem Without Tears 
### Essential Incompleteness in Synthetic Computability

This repository contains the Coq code accompanying [Benjamin Peters'](https://www.ps.uni-saarland.de/~peters/) [Bachelor's thesis](https://www.ps.uni-saarland.de/~peters/bachelor.php) (download [here](https://www.ps.uni-saarland.de/~peters/bachelor/thesis.pdf)) at the [Programming Systems Lab](https://www.ps.uni-saarland.de) at [Saarland University](https://www.uni-saarland.de/start.html) as part of a fork of the [Coq library of undecidability proofs](https://github.com/uds-psl/coq-library-undecidability).

The documentation can found [here](https://www.ps.uni-saarland.de/~peters/bachelor/documentation/toc.html).

The development can be found at [`theories/FOL/Incompleteness/`](https://github.com/uds-psl/coq-synthetic-incompleteness/tree/bachelor/theories/FOL/Incompleteness) and comprises the following files:
- `utils.v`: Utilities for vectors and a definition of partial functions
- `epf.v`: Definition of Church's thesis and undecidability/uncomputability results
- `dprm.v`: Church's thesis for mu-recursive functions
    - `recalg.v`: Enumerability and discreteness of mu-recursive functions (by [Johannes Hostert](https://www.ps.uni-saarland.de/~hostert/))
- `formal_systems.v`: Abstract formal systems
- `abstract_incompleteness.v`: Incompleteness of abstract formal systems
- `fol.v`: Utilities for first-order logic and [first-order proofmode](https://github.com/mark-koch/firstorder-proof-mode) integration 
- `qdec.v`: Q-decidability and Σ1-completeness
- `weak_strong.v`: Rosser's trick to show that weak representability implies strong separability in Robinson arithmetic
    - `completeness.v`: Illustrative proof of strong separability using completeness
- `fol_incompleteness.v`: Essential incompleteness of Robinson arithmetic



## Installation Instructions

### Manual installation

You need `Coq 8.13` built on OCAML `>= 4.07.1`, the [Smpl](https://github.com/uds-psl/smpl) package, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. If you are using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
```

### Building the incompleteness results

- navigate to the `theories` directory
- `make all` builds the whole library and might take >30min
- `make FOL/Incompleteness/fol_incompleteness.vo FOL/Incompleteness/completeness.vo` compiles all files necessary to assess the incompleteness results
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

#### Compiled interfaces

The library is compatible with Coq's compiled interfaces ([`vos`](https://coq.inria.fr/refman/practical-tools/coq-commands.html#compiled-interfaces-produced-using-vos)) for quick infrastructural access.

- `make vos` builds compiled interfaces for the library
- `make FOL/Incompleteness/fol_incompleteness.vos FOL/Incompleteness/completeness.vos` builds compiled interfaces for the incompleteness results
- `make vok` checks correctness of the library 

### Troubleshooting

#### Windows

If you use Visual Studio Code on Windows 10 with Windows Subsystem for Linux (WSL), then local opam switches may cause issues.
To avoid this, you can use a non-local opam switch, i.e. `opam switch create 4.07.1+flambda`.

#### Coq version

Be careful that this branch only compiles under `Coq 8.13`. If you want to use a different Coq version you have to change to a different branch.

