# Lean Machine Makefile

.PHONY: all build clean run

all: build

build:
	lake build

clean:
	lake clean

run: build
	lake exe lean-machine
