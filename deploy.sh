#!/usr/bin/env bash
# Push the working copy straight to the VPS, bypassing CI.
#
# The normal path is CI: push to master, GitHub Actions publishes server.py as a
# release, and vps-health's deployer installs it. This script exists for the
# case where that loop is not available or not fast enough — it is the manual
# override, not the deploy.
#
# It stamps a dev version so the badge in the corner reads e.g. `dev-1a2b3c*`
# and never silently claims to be a released build. The trailing `*` is the
# tell: this came from someone's working copy.
set -euo pipefail

HOST="${HOST:-vps}"
DEST=/opt/session-controller
UNIT=session-controller
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

sha="$(git -C "$here" rev-parse --short HEAD 2>/dev/null || echo nogit)"
dirty=""
git -C "$here" diff --quiet 2>/dev/null || dirty="+"
sed "s/__OSMOSIS_VERSION__/dev-${sha}${dirty}*/g" "$here/server.py" > "$tmp/server.py"

echo "==> syncing to $HOST:$DEST (dev-${sha}${dirty}*)"
ssh "$HOST" "mkdir -p $DEST"
scp -q "$tmp/server.py" "$HOST:$DEST/"

echo "==> installing unit"
scp -q "$here/systemd/$UNIT.service" "$HOST:/etc/systemd/system/"
ssh "$HOST" "systemctl daemon-reload && systemctl enable --now $UNIT && systemctl restart $UNIT"

echo "==> verifying"
sleep 2
# Straight at the loopback port: no X-Forwarded-* headers, so this is the path
# that deliberately skips the SSO redirect. A 200 here means the server is up;
# it says nothing about Caddy, which is checked separately below.
ssh "$HOST" "curl -sf -w 'healthz %{http_code} ' http://127.0.0.1:8221/healthz; echo"
# Through Caddy, resolving the name locally so this works regardless of DNS.
# 302 to the login is the CORRECT answer for an unauthenticated request.
ssh "$HOST" "curl -sk --resolve session.osmosis.work:443:127.0.0.1 \
  -o /dev/null -w 'vhost %{http_code} -> %{redirect_url}\n' https://session.osmosis.work/"
ssh "$HOST" "systemctl is-active $UNIT"
echo "==> done"
