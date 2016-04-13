# doalarm makefile
# M.J. Pomraning <mjp@pilcrow.madison.wi.us>
# 08 Dec 2001

PREFIX = /usr
INSTALL = /usr/bin/install

CC = gcc
CFLAGS = -O2 -Wall

LD = gcc
LDFLAGS = -s
LIBS =

doalarm: doalarm.o
	$(LD) $(LDFLAGS) $(LIBS) $^ -o $@

doalarm.o: doalarm.c
	$(CC) $(CFLAGS) -c $<

install: bininstall maninstall

bininstall:
	$(INSTALL) -m 0755 doalarm $(PREFIX)/bin/

maninstall:
	$(INSTALL) -m 0644 doalarm.1 $(PREFIX)/man/man1/

clean:
	rm -f *.o core doalarm

.PHONY: clean install bininstall maninstall
