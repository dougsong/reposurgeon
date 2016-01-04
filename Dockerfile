FROM buildpack-deps:jessie

RUN apt-get update -qy && apt-get install -qy --no-install-recommends \
    asciidoc \
    python2.7 \
    python-pip \
    xmlto \
 && apt-get clean \
 && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /usr/local/src/reposurgeon/
WORKDIR /usr/local/src/reposurgeon/

COPY requirements.txt /usr/local/src/reposurgeon/
RUN pip install -r requirements.txt

COPY . /usr/local/src/reposurgeon/
RUN make install

CMD reposurgeon
