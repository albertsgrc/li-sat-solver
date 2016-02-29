all: solver solver-alex

%: %.cc
	g++ $@.cc -O3 -pg -g -static -ansi -Wall -Wextra -Werror -Wno-uninitialized -Wno-sign-compare -Wshadow -std=c++11 -o $@ -I$(INCL)

clean:
	rm -f solver solver-alex
