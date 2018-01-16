all: build

.PHONY: build
build:
	coqtop -color yes -I src -compile src/ast.v

.PHONY: clean
clean:
	rm -f src/*.aux src/*.glob src/*.vo
