FROM ubuntu:latest

# Install dependencies
RUN apt-get update -y && \
  apt-get upgrade -y && \
  DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC apt-get install -y build-essential python3 python3-venv python3-pip python3-tk make git

# Install docker (from https://openlane2.readthedocs.io/en/latest/getting_started/docker_installation/installation_ubuntu.html)
RUN apt-get update -y && \
  apt-get install -y ca-certificates curl gnupg

RUN mkdir -p /etc/apt/keyrings && \
  install -m 0755 -d /etc/apt/keyrings && \
  curl -fsSL https://download.docker.com/linux/ubuntu/gpg | gpg --dearmor -o /etc/apt/keyrings/docker.gpg && \
  chmod a+r /etc/apt/keyrings/docker.gpg && \
  echo \
    "deb [arch="$(dpkg --print-architecture)" signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
    "$(. /etc/os-release && echo "$VERSION_CODENAME")" stable" | \
    tee /etc/apt/sources.list.d/docker.list > /dev/null

RUN apt-get update -y && \
  apt-get install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin

ENV OPENLANE_ROOT=/home/openlane
ENV PDK_ROOT=/home/pdk

# Install Caravel
WORKDIR /home
# Cloning my branch here due to a bug in the Makefile.
RUN git clone --depth 1 https://github.com/UnsignedByte/caravel_user_project.git caravel_user_project