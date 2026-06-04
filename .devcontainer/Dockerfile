# ============================================
# Lean 4 DevContainer Dockerfile
# Base: debian:trixie-slim (Debian 13, current stable)
#
# Provides just enough to build a Lean 4 + Mathlib project:
#   - elan (Lean toolchain manager; the toolchain is resolved per-project
#     from lean-toolchain by post-create.sh)
#   - build-essential / git / curl for elan + lake
#
# Node.js and the Firecrawl CLI are installed at container-create time by
# post-create.sh (not baked here), keeping this image small.
#
# Memory Requirements:
#   - With Mathlib: 8GB RAM minimum (16GB recommended)
# ============================================

FROM debian:trixie-slim

# Minimal system packages:
#   build-essential — C toolchain some lake/Lean steps need
#   git             — version control + lake dependency fetching
#   curl            — download the elan installer
#   ca-certificates — HTTPS for git/curl
#   sudo            — devcontainer user privilege escalation (post-create.sh)
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    ca-certificates \
    git \
    build-essential \
    sudo \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean

# Set environment variables for elan
ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

# Create a shared elan directory accessible to all users
RUN mkdir -p $ELAN_HOME && chmod 777 $ELAN_HOME

# Install elan globally (no default toolchain - resolved per-project via lean-toolchain)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --no-modify-path --default-toolchain none \
    && chmod -R a+w $ELAN_HOME \
    && elan --version

WORKDIR /workspace
