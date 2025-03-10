# Esercizio.lean

## Overview
This project contains formalized proofs in Lean 4, focusing on group theory concepts. The main objective was to prove the specific exercise stated below, but it ended up including some useful lemmas.

## Exercise
Every group of order $p^4$ has an abelian subgroup of order $p^3$.

## Prerequisites
To work with this project, you need:
- [Lean 4](https://leanprover.github.io/)
- [Mathlib 4](https://github.com/leanprover-community/mathlib4), the Lean mathematical library

## Installation
1. Install Lean 4 following the [official guide](https://leanprover.github.io/lean4/doc/setup.html).

2. Clone this repository and navigate to its directory:
   ```sh
   git clone https://github.com/Iquadro1/unipi-lean-project
   cd unipi-lean-project
   ```
3. Set up `lake`, the package manager for Lean: 
   ```sh
   lake exe cache get
   ```
4. Ensure Mathlib dependencies are installed:
   ```sh
   lake update
   lake exe cache get
   ```

## Usage
To work with the proofs, open the file in VS Code with the Lean extension installed.
The main files are [`MainResult.lean`](./Progetto/MainResult.lean) and [`Basic.lean`](./Progetto/Basic.lean).


## Contributions
Feel free to make this better.