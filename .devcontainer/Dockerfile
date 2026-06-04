# ============================================
# Lean 4 DevContainer Dockerfile
# Base: debian:trixie-slim (Debian 13, current stable)
#
# Includes:
#   - elan (Lean toolchain manager)
#   - TeX Live (XeLaTeX, latexmk, minted)
#   - Python 3 + pip (Pygments, leanblueprint)
#
# Memory Requirements:
#   - Without Mathlib: 4GB RAM minimum
#   - With Mathlib:    8GB RAM minimum (16GB recommended)
# ============================================

FROM debian:trixie-slim

# Install system packages:
#   build-essential, git, curl  — basics for elan/lake
#   python3, python3-pip        — Pygments (minted), leanblueprint (blueprint)
#   python3-dev                 — Python headers needed for native pip wheels
#   graphviz, graphviz-dev      — pygraphviz runtime and headers for leanblueprint
#   pkg-config                  — helps pygraphviz locate Graphviz during build
#   texlive-xetex               — XeLaTeX engine (fontspec)
#   texlive-latex-extra         — minted, enumitem, booktabs, mathtools
#   texlive-science             — additional math/science packages
#   texlive-fonts-recommended   — standard fonts
#   latexmk                     — build automation for blueprint
#   ngspice, libngspice0,       — SPICE engine + shared library for PySpice
#     libngspice0-dev             (autonomous-dynamics-circuit); the -dev pkg
#                                 provides the unversioned libngspice.so symlink
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    ca-certificates \
    git \
    build-essential \
    sudo \
    python3 \
    python3-pip \
    python3-dev \
    graphviz \
    graphviz-dev \
    pkg-config \
    ngspice \
    libngspice0 \
    libngspice0-dev \
    texlive-xetex \
    texlive-latex-extra \
    texlive-science \
    texlive-fonts-recommended \
    latexmk \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean

# Install Python packages:
#   Pygments     — syntax highlighting for minted
#   leanblueprint — Lean 4 blueprint tooling (includes plasTeX)
RUN pip3 install --no-cache-dir --break-system-packages \
    Pygments \
    leanblueprint

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
