.PHONY: debug test

build/bin/GAP: GAP.lean GAP/*.lean leanpkg.toml
	leanpkg build bin


debug:
	leanpkg build bin 2>&1 | spc -e "red, error"  -e "grn,def" # for colored output

test:
	./build/bin/GAP
