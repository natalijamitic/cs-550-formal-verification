# Formal verification of AVL trees
In this work, we implement and formally verify the aforementioned basic operations of AVL trees: `lookup`, `insert`, `delete`. Additionally, we expand the basic interface with formal verification of `join` and `split` operations. Our source code can be found in the [`code/`](code/) folder.

## Introduction
Standard list allocations _sequential_ and _linked_ allocations) cannot guarantee equally good performances for `lookup`, `insert`, `delete` operations - there is an intrinsic trade-off between linear and constant computation complexity. In order to achieve logarithmic time complexity for all three operations, **balanced tree** representations of a _linear list_ were introduced. One of the first and most significant balanced trees is the **AVL tree** with a worst-case lookup, insertion, and deletion time of O(logN), where N is the number of nodes in the tree. 

In this work, we aim to implement and prove correctness of `lookup`, `insert` and `delete` operations of AVL trees. In addition, we expand the basic interface with implementation and formal verification of `join` and `split` operations performed on AVL trees. All operations are implemented in _Scala_ programming language, while the formal verification is performed using the _Stainless_ verification tool. 

## Running the verification
In order to run the verification, make sure to have installed the _Stainless_ verification tool (you can install it from [here](https://github.com/epfl-lara/stainless)).

Verification can be run in your favourite shell using the following command:

```sh
stainless --solvers=smt-z3 --vc-cache=false --timeout=10 code/*.scala
```

We also provide the output of the verification process in [`stainless_output`](stainless_output.txt).

## Authors
- Filip Carevic (filip.carevic@epfl.ch)
- Natalija Mitic (natalija.mitic@epfl.ch)
- Radenko Pejic (radenko.pejic@epfl.ch)