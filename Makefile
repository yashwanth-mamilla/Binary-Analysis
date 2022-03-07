CC = gcc
CXX = g++
CCFLAGS = -Wall -m32 -no-pie -g

example :
	$(CC) $(CCFLAGS) example.c -o example
	
clean :
	rm -f example_* example

