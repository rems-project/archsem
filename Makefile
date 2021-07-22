.PHONY : all exports

all :
	echo "try `make exports` to make a self-contained tarball"

DIR=models_relation

exports :
	rm -rf $(DIR)
	git clone . $(DIR)
	rm $(DIR)/LICENSE
	rm $(DIR)/Makefile
	rm -f $(DIR).tar
	tar cf $(DIR).tar $(DIR)

# rerunning this would discard the hand edits to aarch64_types.v
#
#.PHONY copy-armv8.5
#copy-armv8.5:
#	rm -rf arm-v8.5-a-types
#	cp -a ../../sail-arm/arm-v8.5-a/snapshots/coq arm-v8.5-a-types
#	rm arm-v8.5-a-types/aarch64.v
#	rm arm-v8.5-a-types/aarch64_extras.v
#	cp -a arm-v8.5-a-types-overrides/build arm-v8.5-a-types
#	cp -a arm-v8.5-a-types-overrides/clean arm-v8.5-a-types

# ...then manually hack the build and clean scripts

