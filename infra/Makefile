# OCaml compilation
OCB = ocamlbuild $(OCB_FLAGS)
OCB_FLAGS = -use-ocamlfind

# C compilation
CC = gcc $(CFLAGS)
CFLAGS = -I .

.PHONY: all clean checkpkg readskill interp

all: readskill interp

# check that needed OCaml packages can be found
checkpkg:
	ocamlfind query xmlm

readskill: checkpkg
	$(OCB) 'readskill.native'
	ln _build/readskill.native ../test/rs

interp: checkpkg
	$(OCB) 'interpreter.native.o'
	ln _build/interpreter.native.o ../test/modcaml.o

clean:
	$(OCB) -clean
