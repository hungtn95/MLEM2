project1: main.o 
	g++ -g -std=c++11 main.o -o project1

main.o: main.cpp
	g++ -g -std=c++11 -c main.cpp
		
clean:
	$(RM) *.o
	$(RM) project1

.PHONY: clean all
