all:
	g++ -Werror -g -Ofast -march=native -o 2048 2048.cpp
clean:
	rm -rf 2048 record.txt
