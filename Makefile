all : exports

.PHONY : exports

DIR=models_relation

exports :
	rm -rf $(DIR)
	git clone . $(DIR)
	rm $(DIR)/LICENSE
	rm $(DIR)/Makefile
	rm -f $(DIR).tar
	tar cf $(DIR).tar $(DIR)
