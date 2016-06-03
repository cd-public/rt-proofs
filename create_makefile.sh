# Compile all *.v files (except the ones that define the decidable equality). Those
# are directly included in other files.
coq_makefile -f _CoqProject $(find -name "*.v" ! -name "*#*" ! -name "*eqdec*.v" -print) -o Makefile

# Fix the 'make validate' command. It doesn't handle the library prefix properly
# and cause clashes for files with the same name. This forces full filenames and
# adds the rt. prefix
sed -i 's|$(notdir $(^:.vo=))|$(addprefix rt., $(subst /,., $(^:.vo=)))|g' Makefile

# Fix 'make html' so that it parses comments and has links to ssreflect.
sed -i 's|-interpolate -utf8|-interpolate -utf8 --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp|g' Makefile

