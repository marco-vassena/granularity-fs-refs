#! /bin/zsh

EVAL_DIR="../eval/"
SRC_DIR="../src"
cd $SRC_DIR

files=( 
  "Bijection.txt"
  "CG.txt"
  "FG.txt"
  "Heap.txt"
  "Lattice.txt"
  "Memory.txt"
  "Misc.txt"
  "Store.txt"
  )

security="Security/Security.txt"

for file in $files 
do
  echo "\n\n--------------------------" $file "--------------------------\n\n"
  xargs cloc --by-file < $EVAL_DIR/$file
done

echo "\n\n-------------------------- Security --------------------------\n\n"

cd $EVAL_DIR
cloc --by-file --list-file=Security.txt
