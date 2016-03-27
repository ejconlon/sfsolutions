.PHONY: clean all

clean:
	rm -f .*.aux *.glob *.vo

all: Basics.vo Induction.vo Lists.vo Poly.vo MoreCoq.vo

Basics.vo:
	coqc Basics.v

Induction.vo: Basics.vo
	coqc Induction.v

Lists.vo: Induction.vo
	coqc Lists.v

Poly.vo: Lists.vo
	coqc Poly.v

MoreCoq.vo: Poly.vo
	coqc MoreCoq.v

