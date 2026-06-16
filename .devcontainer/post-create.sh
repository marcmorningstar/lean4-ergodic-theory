#!/bin/bash
# Post-create script for Lean 4 DevContainer
# This script runs after the container is created.

set -e

echo "=== Lean 4 DevContainer Setup ==="

# 1. Install the toolchain specified in lean-toolchain
TOOLCHAIN=$(cat lean-toolchain | tr -d '[:space:]')
echo "Installing toolchain: $TOOLCHAIN"
elan default "$TOOLCHAIN"

# 2. If Mathlib is a dependency, fetch precompiled cache.
#    NOTE: we deliberately do NOT run `lake update` here — the committed
#    lake-manifest.json pins the exact dependency revisions that match
#    lean-toolchain and the prebuilt cache. `lake update` would float mathlib
#    to latest `main`, risking a toolchain mismatch and a multi-hour source
#    build. Run `lake update` by hand only when intentionally bumping deps.
if grep -q "mathlib" lakefile.lean 2>/dev/null || grep -q "mathlib" lakefile.toml 2>/dev/null; then
    echo "Mathlib detected as dependency. Fetching precompiled cache..."
    echo "This may take a few minutes on first run."
    lake exe cache get || echo "WARNING: cache get failed. You may need to build Mathlib from source."
fi

# 4. Firecrawl CLI — connects to the self-hosted Firecrawl instance running
#    on the devcontainer *host* (no auth). Non-fatal: a missing Node, npm
#    registry, or host service must not abort container setup.
echo ""
echo "=== Firecrawl CLI Setup ==="
FIRECRAWL_HOST_URL="http://host.docker.internal:3002"
set +e

# Node.js is the CLI's runtime; install from the distro repos if absent.
if ! command -v node >/dev/null 2>&1; then
    echo "Installing Node.js (firecrawl-cli runtime)..."
    sudo apt-get update -qq && sudo apt-get install -y -qq nodejs npm
fi

# The firecrawl CLI itself.
if ! command -v firecrawl >/dev/null 2>&1; then
    echo "Installing firecrawl-cli..."
    sudo npm install -g firecrawl-cli@1.16.2
fi

# Persist the endpoint in the CLI's own config (~/.config/firecrawl-cli) so it
# works in every shell, including the non-interactive ones tooling spawns that
# never source ~/.bashrc. The self-hosted instance ignores the key value, but
# the CLI insists on *some* key to consider itself authenticated.
if command -v firecrawl >/dev/null 2>&1; then
    firecrawl login --api-key "fc-localhost" --api-url "$FIRECRAWL_HOST_URL" >/dev/null 2>&1
fi

# Reachability smoke test (non-fatal).
if curl -sf -m 5 "$FIRECRAWL_HOST_URL" >/dev/null 2>&1; then
    echo "Firecrawl configured and reachable at $FIRECRAWL_HOST_URL"
else
    echo "WARNING: Firecrawl not reachable at $FIRECRAWL_HOST_URL"
    echo "         (is the self-hosted service running on the host?)"
fi
set -e

# 5. leancheck harness — the warm Lean-feedback hook drives the Lean language server (`lake serve`)
#    through the `leanclient` Python library. Non-fatal: a missing PyPI must not abort setup
#    (the cold `lake build` gate works without it).
echo ""
echo "=== leancheck harness (leanclient) ==="
set +e
if ! python3 -c "import leanclient" >/dev/null 2>&1; then
    echo "Installing leanclient (Lean LSP client for the warm-feedback hook)..."
    pip install --user --break-system-packages -q leanclient \
        || echo "WARNING: leanclient install failed; warm leancheck unavailable (cold build still works)."
fi
python3 -c "import leanclient" >/dev/null 2>&1 && echo "leanclient available"
set -e

echo ""
echo "=== Setup Complete ==="
echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"
command -v firecrawl >/dev/null 2>&1 && echo "Firecrawl version: $(firecrawl --version 2>/dev/null | head -1)"
