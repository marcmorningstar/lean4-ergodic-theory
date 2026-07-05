.PHONY: all build clean

all: build

# Build the ErgodicTheory library (and its Mathlib dependency).
build:
	lake build

# Remove local Lean build artifacts (keeps the dependency cache).
clean:
	lake clean
