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

for file in $files 
do
  echo "\n\n--------------------------" $file "--------------------------\n\n"
  xargs cloc --by-file < $EVAL_DIR/$file
done

#echo "\n\n-------------------------- CG --------------------------\n\n"
#xargs cloc --by-file < $EVAL_DIR/CG.txt
#
#echo "\n\n----------------- Misc (common files) ------------------\n\n"
#xargs cloc --by-file < $EVAL_DIR/Misc.txt
#
#echo "\n\n------------- Bijection (common files) -----------------\n\n"
#xargs cloc --by-file < $EVAL_DIR/Bijection.txt 
