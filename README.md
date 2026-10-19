# agent-control-panel

Start, resume and stop Claude Code sessions on a server from a phone.

A single-file Python web server (`server.py`, standard library only). It lists every
named Claude Code session, shows which are running and how much context each is
carrying, and gives each one a **Resume** or **Stop** button. **+ New** starts a fresh
session under a name you pick, and **Stop all** stops every running one.

A resumed session comes up already connected to the Claude app, so it appears on the
phone under its own name, ready to talk to.

## How it works

- **Runs on the host, launches in a container.** The server runs on the server itself
  under systemd. Claude Code lives in a workspace container, so every launch and stop
  goes through `docker exec`.
- **Launching.** `claude --resume <id> --remote-control <name>` refuses to run without a
  terminal, so a small launcher embedded in `server.py` starts it under a pseudo-terminal
  inside the container. The model and effort level are read from Claude Code's settings
  on every launch, so a resumed session picks up the current choice instead of the one
  it last ran on.
- **Names and liveness.** A named session writes its title into its own transcript, which
  gives the name-to-id list. Running sessions are found from Claude Code's per-process
  registry files and from process command lines; a registry file whose process is gone
  is ignored.
- **Context size.** Read from the last assistant turn's usage in each transcript, reading
  only the last 1 MB of files that changed. A session that has compacted since then shows
  "compacted" instead of its old size.
- **Memory guard.** The workspace container is capped at 3 GB and a resumed session costs
  about 400 MB, so a resume is refused unless 600 MB of the container's limit is left.
  Before refusing, it asks the kernel to drop reclaimable cache and measures again.
- **Stopping** sends SIGTERM, never SIGKILL, so Claude Code saves its transcript and
  removes its registry entry on the way out.

## Endpoints

| Route | What it does |
|---|---|
| `GET /` | The page |
| `GET /api/sessions` | Sessions: name, id, running or not, status, context size |
| `POST /api/new` | `{title}`: start a fresh session |
| `POST /api/resume` | `{session_id, title}` |
| `POST /api/stop` | `{session_id}` |
| `POST /api/stop-all` | Stop every running session |
| `POST /api/dismiss` | `{key}`: clear a launch alert |
| `GET /healthz`, `/version.json` | Build version, no login |

## Login

It never shows a login form or checks a password. It checks a signed login cookie
(HMAC-SHA256 with `SSO_SIGNING_KEY`) set by a separate central login service, and sends
anyone without one there. Requests made straight to the local port, without going
through the web server in front, may read the session list without the cookie (the
deployer's health check and the monitoring dashboard use this); every action always
needs it. Actions are also refused from other sites (`Sec-Fetch-Site`).

The server only listens on `127.0.0.1`; a reverse proxy (`caddy-vhost.conf`) puts it on
the web.

## Files

| File | What it is |
|---|---|
| `server.py` | The whole app: server, page, icons and the in-container launcher |
| `systemd/session-controller.service` | The systemd unit |
| `caddy-vhost.conf` | The reverse-proxy site |
| `deploy.sh` | Copies the working copy to the server by hand, for when CI is unavailable |
