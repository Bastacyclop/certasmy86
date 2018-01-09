all: build

.PHONY: build
build:
	coqtop -color yes -I src -compile src/ast.v
