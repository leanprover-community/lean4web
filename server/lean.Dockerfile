FROM ubuntu:22.04

WORKDIR /

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y git curl

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
RUN ./elan-init -y --default-toolchain none
ENV PATH="${PATH}:/root/.elan/bin"

COPY LeanProject LeanProject

WORKDIR /LeanProject
RUN apt-get install libatomic1

RUN lake build
