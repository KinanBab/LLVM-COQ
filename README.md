# LLVM_COQ
Attempting to automate/patternize Hoare logic based proofs of correctness for programs written in a low-level LLVM like instruction set.

## Dependencies
This was tested and built using Coq 8.6
It also requires the Frap package as a dependency https://github.com/achlipala/frap
Frap is included as a git submodule pointing at the version used when this code was written.

## Running
use `make` to compile with Coq, the command will also compile the Frap library located at ./Frap/ if needed (using make lib)

`make` will compile both Example\_Correctness.v and Example\_Rules.v

Alternativly, Open either files with CoqIDE.

If during compilation or checking of either file, you see an error about Frap, that means the library is not properly compiled, 
You can manually compile it by going into the ./Frap directory and running `make lib`

The other .v files will not work if compiled separatly since they require definitions available in other files. 
They are treated as library models, they are loaded appropriately by Example_Correctness.v and Example_Rules.v
