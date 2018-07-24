# BTCompiler

This repository contains the software for the verified execution of Behavior Trees developed in the context of the CARVE project.

## Build instructions

To build from source you will need:

* the [Coq](https://coq.inria.fr/) compiler (version >= 8.7 will work out of the box; previous versions will complain about a missing `Extraction` library, in which case you need to comment all lines `Require Import Extraction` in the source files)
* a working [ocaml](https://ocaml.org/) system with `findlib`, `ocamlbuild` and the [Xmlm library](http://erratique.ch/software/xmlm) (`opam install xmlm`)
* your favorite C compiler.

Before building the interpreter you need to write an XML file (as in [this example](https://github.com/CARVE-ROBMOSYS/BTCompiler/blob/master/infra/sklist.xml)) containing a list of all the basic skills (= `Action` or `Condition` nodes in BT jargon) that will be allowed as leaves in your Behavior Trees. Each skill will be identified by a string, which (for obvious reasons) **must** be unique. Once you have created this file, type:
```
make
cd infra
make readskill
./readskill.native <path to XML file>
make interp
```
(these steps will be automated eventually). This will create a shared object file `modcaml.o` which contains the certified interpreter. The C interface to the interpreter is provided by the two functions
```
value readbt(char *filename);
int tick(value bt);
```
defined in `test/wrap.c`. The `readbt` function reads a single BT contained in the XML file specified and returns the corresponding OCaml data structure. The `tick` function executes the given BT and returns a value of type `enum {RUNNING, FAILURE, SUCCESS}`.

See `test/main.c` for a complete example.
