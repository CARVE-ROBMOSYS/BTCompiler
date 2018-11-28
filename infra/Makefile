# OCaml compilation
OCB = ocamlbuild $(OCB_FLAGS)
OCB_FLAGS = -use-ocamlfind

# C compilation
CC = gcc $(CFLAGS)
CFLAGS = -I .

.PHONY: all clean checkpkg readskill interp mkspec

all: readskill interp mkspec

# check that needed OCaml packages can be found
checkpkg:
	ocamlfind query xmlm str

readskill: checkpkg
	$(OCB) 'readskill.native'

interp: checkpkg
	$(OCB) 'interp.native.o'
	cp _build/interp.native.o ../test/modcaml.o

mkspec: checkpkg
	$(OCB) 'mkspec.native'

clean:
	$(OCB) -clean
