- To export docker image [ref](https://docs.docker.com/reference/cli/docker/image/save/)
    ```
    docker save <image-name> | gzip > <image-name>.tar.gz
    ```
- To import docker image [ref](https://docs.docker.com/reference/cli/docker/image/load/)
    ```
    docker load < <image-file>.tar.gz
    ```
