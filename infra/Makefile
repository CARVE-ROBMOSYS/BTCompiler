# OCaml compilation
OCB = ocamlbuild $(OCB_FLAGS)
OCB_FLAGS = -use-ocamlfind

# C compilation
CC = gcc $(CFLAGS)
CFLAGS = -I .

.PHONY: all clean checkpkg readskill interp

# check that needed OCaml packages can be found
checkpkg:
	ocamlfind query xmlm

all: readskill interp

readskill: checkpkg
	$(OCB) 'readskill.native'

interp: checkpkg
	$(OCB) 'interpreter.native'

clean:
	$(OCB) -clean
