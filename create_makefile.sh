coq_makefile -R . rt $(find -name "*.v" ! -name "*#*" ! -name "*eqdec*.v" -print) -o Makefile
