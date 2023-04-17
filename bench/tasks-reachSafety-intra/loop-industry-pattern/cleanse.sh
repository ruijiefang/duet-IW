cd $1;
echo " ********** now in directory "$1" ******** "
echo "      continue? [enter]"
read inp

for file in `ls | grep "\.c"`; do 
  echo "-----------------"$file"--------------"
  out=`$DUET/duet.exe -categorize $file`
  echo $out
  if [[ "$out" == *"Memory:    True"* ]]; then 
    echo "memory use found; delete?"
    read inp; 
    echo "deleting "$file"..."
    rm $file;
    echo "deleting ${file%.c}.yml..."
    rm -- "${file%.c}.yml"
  fi
done 

