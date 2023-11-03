FROM ubuntu:latest

# Install dependencies
RUN apt-get update && \
  apt-get install -y unzip wget make g++ build-essential

# Install SoftFloat
WORKDIR /home
RUN wget http://www.jhauser.us/arithmetic/SoftFloat-3e.zip && \
  unzip SoftFloat-3e.zip && \
  rm SoftFloat-3e.zip && \
  cd SoftFloat-3e/build/Linux-386-GCC && \
  make

# Install TestFloat
WORKDIR /home
RUN wget http://www.jhauser.us/arithmetic/TestFloat-3e.zip && \
  unzip TestFloat-3e.zip && \
  rm TestFloat-3e.zip && \
  cd TestFloat-3e/build/Linux-386-GCC && \
  make

ENV PATH="/home/TestFloat-3e/build/Linux-386-GCC:${PATH}"