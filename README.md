# Project structure
- `project`: contains the Agda source files.  
    The project is considered successfully built when all the files in `project` are type-checked by `agda`.
- `Makefile`: defines the command to create the docker image and run a container to build the project.
- `Dockerfile`: docker image recipe.
- `run-in-container.sh`: the script executed inside the container.  
    It type-checks all the `.agda` files in `project` directory.
- `result.txt`: the output of the type-checking process.  
    It contains a line for each compiled file.  
    Success if all the lines start with `[OK]`.


# Overview
To build the project, we first create a docker image with the Agda compiler and the Agda standard library installed.  
Then we run a container to type-check the Agda source files.  
We run the `agda` command on `*.agda` files in `project` directory.  
The files are type-checked, therefore the correctness of theorems/lemmas/properties stated therein is verified.


# How to run
1) Prerequisites:  
    - Docker
    - Make
2) Create the docker image:  
    ```bash
    make docker-image
    ```
3) Run the container:  
    ```bash
    make docker-run
    ```


# References
- [Typing with leftovers](https://github.com/gallais/typing-with-leftovers)
- [Programming Language Foundations in Agda](https://plfa.github.io)
- [Introduction to Lambda Calculus](https://plfa.github.io/Lambda)
- [Progress and Preservation](https://plfa.github.io/Properties)
- [De Bruijn representation](https://plfa.github.io/DeBruijn)
- [Absurd pattern](https://agda.readthedocs.io/en/v2.6.4.1/language/function-definitions.html#absurd-patterns)
- [Equality reasoning](https://plfa.github.io/Equality/#chains-of-equations)


# Compatibility
- Agda version 2.6.4
- Agda standard library version 1.7.3
