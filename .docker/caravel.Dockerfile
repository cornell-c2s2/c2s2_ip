FROM efabless/openlane

# Connect to github repository
LABEL org.opencontainers.image.source https://github.com/cornell-c2s2/c2s2_ip

# Install dependencies
RUN yum update -y && \
  yum install docker -y

# Install Caravel
WORKDIR /home
RUN git clone --depth 1 https://github.com/efabless/caravel_user_project.git caravel
ENV CARAVEL_ROOT=/home/caravel

WORKDIR /home
ADD . c2s2_ip
# Make install
WORKDIR /home/c2s2_ip
RUN make .venv