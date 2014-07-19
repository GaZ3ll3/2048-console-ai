all:
	g++ -Werror -g -O3 -o 2048 2048.cpp
clean:
	rm -rf 2048 record.txt
