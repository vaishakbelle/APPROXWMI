
BINDIR=../bin
targets="doalarm cryptominisat"

all: doalarm cryptominisat
	mkdir $(BINDIR)
	cp thirdparties/doalarm-0.1.7/doalarm $(BINDIR)
	cp thirdparties/cryptominisat-cryptominisat-2.9.10/build/cryptominisat $(BINDIR)
	cp *.py $(BINDIR)

doalarm:
	cd thirdparties/doalarm-0.1.7 && make

cryptominisat:
	cd thirdparties/cryptominisat-cryptominisat-2.9.10/build && ../configure && make

