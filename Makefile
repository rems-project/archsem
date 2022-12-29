# This Makefile is provided for people that prefer to type
# "make" instead of "dune build"
.PHONY : all clean
all:
	dune build


TARBALL=d4b_ISA_interface_and_Promising-Arm_model_in_Coq.tar.gz

$(TARBALL):
	tar -czf $(TARBALL) dune dune-project INSTALL.md README.md Makefile coq-system-semantics.opam LICENSE Common ISASem armv9-instantiation-types GenModels promising-arm

install-deliverable-2022-12: $(TARBALL)
	cp $(TARBALL) ~/repos/deliverables-pkvm-verif-2022/2022-12

clean:
	dune clean
	rm -f $(TARBALL)
