all: solver

%: %.cc
	g++ $@.cc -O3 -g -ansi -Wall -Wextra -Werror -Wno-uninitialized -Wno-sign-compare -Wshadow -o $@ -I$(INCL)

clean:
	rm -f solver solver-alex
