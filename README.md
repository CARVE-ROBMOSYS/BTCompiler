# BTCompiler

This repository contains the software for the verified execution of Behavior
Trees developed in the context of the CARVE project.

## Build instructions

For building from source you will need:
* `coq`
* `ocaml` with `findlib`, `ocamlbuild` and the [Xmlm library](http://erratique.ch/software/xmlm) (`opam install xmlm`)
* your favorite C compiler.

To build the interpreter you will need an XML file (say `sklist.xml`)
containing a list of all the skills that will be allowed as leaves in your
Behavior Trees (identified by a string). Such strings must be unique. Once you
have created such file (say in the root directory), type:
```
make
cd infra
make readskill
./readskill.native ../sklist.xml
make interp
```
This will create a shared object file `modcaml.o` which contains the certified
interpreter. The C interface to the interpreter is provided by two functions
```
value readbt(char *filename)
int tick(value bt)
```
defined in `test/wrap.c`. The `readbt` function reads a single BT contained in
the XML file specified and returns the corresponding OCaml data structure. 
The `tick` function executes the given BT and returns a value of type
`enum {RUNNING, FAILURE, SUCCESS}`.

See `test/main.c` for an example.
