.PHONY: clean all

clean:
	rm -f .*.aux *.glob *.vo

all: Basics.vo Induction.vo Lists.vo

Basics.vo:
	coqc Basics.v

Induction.vo: Basics.vo
	coqc Induction.v

Lists.vo: Induction.vo
	coqc Lists.v
