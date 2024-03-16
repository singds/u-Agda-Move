- Agda version 2.6.4
- Agda standard library version 1.7.3


# Project structure
- `project`: contains the Agda source files.  
    The project is considered successfully built when all the files in this directory are type-checked by `agda`.
- `Makefile`: defines the command to create the docker image and run a container to build the project.
- `Dockerfile`: image recipe.
- `run-in-container.sh`: the script that is executed inside the container.  
    It type-checks all the `.agda` files of the project.
- `result.txt`: the output of the type-checking process.  
    It contains a line for each compiled file.
    Success if all the lines start with `[OK]`.


# Overview
To build the project, we first create a docker image with the Agda compiler and the Agda standard library.  
Then we run a container to type-check the Agda source files.  
We run the `agda` command on all the `.agda` files in the `project` directory.  
This type-checks all the files in the project and so proves the theorems/lemmas/properties therein.


# How to run
1) Create the docker image:  
    ```bash
    make docker-image
    ```
2) Run the container:  
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
