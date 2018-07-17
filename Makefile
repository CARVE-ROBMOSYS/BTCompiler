.PHONY: all byte checkpkg clean native

# coq compilation
CQC = coqc $(CQC_FLAGS)
CQC_FLAGS = -I .

# OCaml compilation
OCB = ocamlbuild $(OCB_FLAGS)
OCB_FLAGS = -use-ocamlfind

# C compilation
CC = gcc
CFLAGS = -I .

all: certmod skillreader specextr interp

# check that needed OCaml packages can be found
checkpkg:
	ocamlfind query xmlm

certmod:
	$(CQC) bt.v
	$(CQC) shallow.v

skillreader: checkpkg certmod
	cd infra
	$(OCB) readskill.native

interp: checkpkg certmod
	cd infra
	$(OCB) interpreter.native

clean:
	$(OCB) -clean
