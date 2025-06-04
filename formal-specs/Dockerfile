# Dockerfile for formal verification tools (TLA+ and Alloy)
FROM openjdk:11-slim

# Install required packages
RUN apt-get update && apt-get install -y \
    wget \
    curl \
    unzip \
    python3 \
    python3-pip \
    make \
    && rm -rf /var/lib/apt/lists/*

# Set up working directory
WORKDIR /tools

# Install TLA+ toolbox components
ENV TLA_VERSION=1.7.1
RUN wget https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar && \
    mv tla2tools.jar /tools/tla2tools.jar

# Install Alloy
ENV ALLOY_VERSION=6.0.0
RUN wget https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v${ALLOY_VERSION}/alloy.jar && \
    mv alloy.jar /tools/alloy.jar

# Create wrapper scripts
RUN echo '#!/bin/bash\njava -cp /tools/tla2tools.jar tlc2.TLC "$@"' > /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc

RUN echo '#!/bin/bash\njava -cp /tools/tla2tools.jar tla2sany.SANY "$@"' > /usr/local/bin/sany && \
    chmod +x /usr/local/bin/sany

RUN echo '#!/bin/bash\njava -jar /tools/alloy.jar "$@"' > /usr/local/bin/alloy && \
    chmod +x /usr/local/bin/alloy

# Install Python dependencies for verification scripts
RUN pip3 install pyyaml junit-xml

# Set up verification workspace
WORKDIR /workspace

# Entry point
ENTRYPOINT ["/bin/bash"]