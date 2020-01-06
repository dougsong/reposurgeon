FROM buildpack-deps:jessie

RUN mkdir -p /usr/local/src/reposurgeon/
WORKDIR /usr/local/src/reposurgeon/

COPY ci/prepare.sh /usr/local/src/reposurgeon/ci/
RUN bash ci/prepare.sh

COPY . /usr/local/src/reposurgeon/
RUN make install

CMD reposurgeon
