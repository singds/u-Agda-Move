
clean:
	rm -rf _build

# Count the number of lines of code in the project
loc:
#	cd project && find . -name "*.agda" | xargs wc -l
	cd project && find . -name "*.agda" | xargs grep -v '^$$' | wc -l
