IMG_NAME=img-u-agda-move

# Count the number of lines of code in the project
count-loc:
# include empty lines
#	cd project && find . -name "*.agda" | xargs wc -l
# ignore empty lines
	cd project && find . -name "*.agda" | xargs grep -v '^$$' | wc -l

clean:        # clean build artefacts
	rm -rf _build

docker-image: # create the docker image
	docker build . --file Dockerfile -t ${IMG_NAME}

docker-run:   # run the artefact in a container
	docker run -it --rm -v `pwd`:`pwd` -w `pwd` ${IMG_NAME} \
		./run-in-container.sh
