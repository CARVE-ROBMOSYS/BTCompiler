CC = gcc $(CFLAGS)
CFLAGS = -I . -Wall

all:
	$(CC) -c wrap.c dummy_skills.c
	$(CC) -o test main.c modcaml.o wrap.o dummy_skills.o -L`ocamlopt -where` -lunix -lasmrun -lm -ldl
	$(CC) -o test-reset main.c modreset.o wrap.o dummy_skills.o -L`ocamlopt -where` -lunix -lasmrun -lm -ldl
