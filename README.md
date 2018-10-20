This was tested and built using Coq 8.6

Before running this example, make sure the Frap library is compiled and set under the directory Frap.
To compile Frap, open a terminal, and traverse into the ./Frap directory, then run ``make lib'' to compile the library.

To run the coq compiler COQC on both Example_Correctness.v and Example_Rules.v run ``make'' through a terminal inside this directory.

Alternativly, Open either files with CoqIDE.

If during compilation or checking of either file, you see an error about Frap, that means the library is not properly compiled, 
please recompile it with the above steps.

The other .v files will not work if compiled separatly since they require definitions available in other files. 
They are treated as library models, they are loaded appropriately by Example_Correctness.v and Example_Rules.v