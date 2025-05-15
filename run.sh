./compile.sh $1".cpp" $1
./$1
rm ./$1
cp $1".cpp" ~/bak/$1".cpp"
cp run.sh ~/bak/run.sh
cp compile.sh ~/bak/compile.sh
sudo cp -r ~/bak /data2/zergs/2024/bak
