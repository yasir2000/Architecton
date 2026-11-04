#!/usr/bin/env python3
"""Black-box HTTP->Rust->SQLite integration check. Requires a built binary."""
import json
import os
import socket
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path


def req(base, method, route, payload=None):
    data = None if payload is None else json.dumps(payload).encode()
    request = urllib.request.Request(base + route, data=data, method=method)
    if data is not None:
        request.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(request, timeout=2) as res:
            return res.status, json.load(res)
    except urllib.error.HTTPError as e:
        return e.code, json.load(e)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 scripts/smoke.py backend/target/debug/driverpass-poc")
    binary = Path(sys.argv[1]).resolve()
    if not binary.is_file():
        raise SystemExit(f"Binary missing: {binary}; run cargo build first")
    with tempfile.TemporaryDirectory() as td:
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]
        env = {**os.environ, "PORT": str(port), "DATABASE_PATH": str(Path(td) / "test.sqlite")}
        proc = subprocess.Popen([str(binary)], env=env, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        base = f"http://127.0.0.1:{port}"
        try:
            for _ in range(100):
                try:
                    if req(base, "GET", "/health")[0] == 200:
                        break
                except (urllib.error.URLError, ConnectionError, TimeoutError):
                    time.sleep(.1)
            else:
                raise RuntimeError("Server did not start")
            status, data = req(base, "POST", "/api/v1/instructors/7/slots", {"slot_id": 42})
            assert status == 201 and data["decision"] == "accepted", (status, data)
            status, data = req(base, "POST", "/api/v1/instructors/7/slots", {"slot_id": 42})
            assert status == 409 and data["decision"] == "duplicate", (status, data)
            status, data = req(base, "PATCH", "/api/v1/instructors/7/duty", {"off_duty": True})
            assert status == 200 and data["roster"]["off_duty"]
            status, data = req(base, "POST", "/api/v1/instructors/7/slots", {"slot_id": 43})
            assert status == 409 and data["decision"] == "off_duty", (status, data)
            status, data = req(base, "GET", "/api/v1/instructors/7")
            assert status == 200 and data["roster"]["slots"] == [42], (status, data)
            status, data = req(base, "GET", "/api/v1/audit")
            assert status == 200 and [row["decision"] for row in data["entries"]] == ["off_duty", "duplicate", "accepted"], (status, data)
            status, data = req(base, "POST", "/api/v1/instructors/7/slots", {"slot_id": -1})
            assert status == 400 and data["error"] == "slot_id_must_be_nonnegative", (status, data)
            print("PASS: HTTP, domain decision, transaction, persistence, and audit smoke test")
        finally:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()


if __name__ == "__main__":
    main()
