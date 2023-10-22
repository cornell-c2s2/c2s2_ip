FROM efabless/openlane

# Connect to github repository
LABEL org.opencontainers.image.source https://github.com/cornell-c2s2/c2s2_ip

WORKDIR /home
ADD . c2s2_ip
# Make install
WORKDIR /home/c2s2_ip
RUN make .venv