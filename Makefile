
all: Basics.vo Induction.vo

Basics.vo:
	coqc Basics.v

Induction.vo: Basics.vo
	coqc Induction.v