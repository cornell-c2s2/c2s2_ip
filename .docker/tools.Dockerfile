FROM ubuntu:latest

# --------------------------------------------------------------------
# Install FloPoCo 4.1
# --------------------------------------------------------------------

# Install required libraries
RUN apt update && \
    DEBIAN_FRONTEND=noninteractive apt install -y autoconf automake \
    autotools-dev bison f2c flex git gpg g++ libblas-dev libboost-all-dev \
    liblapack-dev liblpsolve55-dev libsollya-dev libtool lp-solve ninja-build \
    pkg-config sollya wget make libssl-dev

# Install latest cmake from source
RUN wget https://github.com/Kitware/CMake/releases/download/v3.28.0-rc3/cmake-3.28.0-rc3.tar.gz && \
    tar -xvf cmake-3.28.0-rc3.tar.gz && \
    cd cmake-3.28.0-rc3 && ./bootstrap &&\
    make && make install

# Install FloPoCo 4.1
WORKDIR /home
RUN git clone --branch flopoco-4.1 https://gitlab.com/flopoco/flopoco &&\
    cd flopoco && git checkout f3d76595c01f84cee57ae67eee1ceb31a6fe93bc &&\
    mkdir build && cd build &&\
    cmake -GNinja .. && ninja &&\
    ln -s /home/flopoco/build/code/FloPoCoBin/flopoco /usr/bin/flopoco

# --------------------------------------------------------------------
# Install GHDL 3.0.0
# --------------------------------------------------------------------

# Install GHDL 3.0.0
WORKDIR /home
# Install deps
RUN apt install -y gnat llvm clang
RUN git clone --depth 1 --branch v3.0.0 https://github.com/ghdl/ghdl.git &&\
    cd ghdl &&\
    mkdir build && cd build &&\
    LDFLAGS='-ldl' ../configure --with-llvm-config --prefix=/usr &&\
    make && make install

# --------------------------------------------------------------------
# Install Testfloat and Softfloat
# --------------------------------------------------------------------

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