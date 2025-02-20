# RISC Zero RISC-V zk circuit verification condition generator

This repository contains a verification condition generator for the model of Zirgen, a C++ eDSL for synthesizing zk circuits, developed by RISC Zero.
The model of the language, together with a model of its target MLIR, can be found in the associated Lean [repository](https://github.com/NethermindEth/risczero-fv/).

We invite you to read a more thorough overview in the blog post '[Towards formal verification of the first RISC-V zkVM](https://www.nethermind.io/blog/towards-formal-verification-of-the-first-risc-v-zkvm)'.

## Running the verificaiton condition generator

### Installing dependencies and building the project

1. Follow [these](https://github.com/nvm-sh/nvm?tab=readme-ov-file#installing-and-updating) instructions to install `nvm`.
2. Run `nvm install 22.6.0`.
3. In the root directory, run `npm i`.
4. Set the `leanPath` to the associated Lean repository in `src/index.ts`.
5. Run `npx tsc` to build the project.
6. Run `node build/index.js` to run the extractor.

You should now have both the witness and the constraints template files available in `Risc0/Gadgets/<example>/` for each `<example>` MLIR that are in their respective `*.txt` files in the root of this repository.
